#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include <typeinfo>

using namespace llvm;

#define DEBUG_TYPE "hello"

namespace {
    // Hello2 - The second implementation with getAnalysisUsage implemented.
    struct LoopSplitting : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        LoopSplitting() : FunctionPass(ID) {}

        Value *getValueFromSCEV(const SCEV *scev) {
            if (auto constant = dyn_cast<SCEVConstant>(scev)) {
                return constant->getValue();
            } else if (auto unknown = dyn_cast<SCEVUnknown>(scev)) {
                return unknown->getValue();
            }

            llvm_unreachable("We only treat constant and unknown SCEVs");
        }

        Value *calculateIntersectionPoint(const SCEVAddRecExpr *first,
                                          const SCEVAddRecExpr *second,
                                          const CmpInst::Predicate predicate,
                                          IRBuilder<> *builder,
                                          LLVMContext *context) {
            assert(first->isAffine() && second->isAffine() && "SCEVs must be affine");
            assert((predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_ULT || predicate == CmpInst::ICMP_ULE ||
                    predicate == CmpInst::ICMP_SGT || predicate == CmpInst::ICMP_SGE || predicate == CmpInst::ICMP_SLT ||
                    predicate == CmpInst::ICMP_SLE) && "We only treat integer inequalities for now");

            const auto b1 = getValueFromSCEV(first->getOperand(0));
            const auto a1 = getValueFromSCEV(first->getOperand(1));
            const auto b2 = getValueFromSCEV(second->getOperand(0));
            const auto a2 = getValueFromSCEV(second->getOperand(1));


            // algoritmo:
            // b = b2 - b1
            // a = a1 - a2
            // div = b / a
            // se op == '>=' ou '<':
            //      return div
            // senão:
            //      return b % a == 0 ? div : div + 1
            const auto b = builder->CreateSub(b2, b1, "b"); // b2 - b1
            const auto a = builder->CreateSub(a1, a2, "a"); // a1 - a2
            const auto div = builder->CreateSDiv(b, a, "div"); // b / a

            // se a comparação for > ou <= não precisamos verificar se é divisão exata,
            // pois mesmo se não for queremos arredondar para baixo
            if (predicate == CmpInst::ICMP_UGT || predicate == CmpInst::ICMP_SGT ||
                predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SLE) {
                return div;
            } else {
                // ou seja: return b % a == 0 ? div : div + 1
                const auto rem = builder->CreateSRem(b, a, "rem"); // rem = b % a
                const auto zero = ConstantInt::get(Type::getInt32Ty(*context), 0);
                const auto divisible = builder->CreateICmp(CmpInst::ICMP_NE, rem, zero, "divisible"); // rem == 0 ? 0 : 1
                const auto extended = builder->CreateZExt(divisible, IntegerType::getInt32Ty(*context), "extended"); // extends to 32 bits
                const auto result = builder->CreateAdd(div, extended, "result");
                return result;
            }
        }

        Loop *cloneLoop(Function *F,
                        Loop *loop,
                        LoopInfo *loopInfo,
                        const Twine &NameSuffix) {
            const auto predecessor = loop->getLoopPredecessor();

            ValueToValueMapTy vMap;
            auto dt = DominatorTree(*F);

            SmallVector<BasicBlock *, 8> blocks;



            const auto clonedLoop = cloneLoopWithPreheader(loop->getExitBlock(),
                                                           predecessor,
                                                           loop,
                                                           vMap,
                                                           "newLoop",
                                                           loopInfo,
                                                           &dt,
                                                           blocks);

            remapInstructionsInBlocks(blocks, vMap);
            return clonedLoop;
        }

        void splitLoop(Function *F,
                       Loop *loop,
                       LoopInfo *loopInfo,
                       ScalarEvolution *SE,
                       const CmpInst::Predicate predicate,
                       const Instruction * BrOrSel,
                       Value *SplitPoint,
                       const SCEVAddRecExpr *first,
                       const SCEVAddRecExpr *second) {

            assert((predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_ULT ||
                    predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SGT ||
                    predicate == CmpInst::ICMP_SGE || predicate == CmpInst::ICMP_SLT ||
                    predicate == CmpInst::ICMP_SLE) &&
                   "We only treat integer inequalities for now");

            auto builder = IRBuilder<>(F->getContext()); // builder a partir de onde?
            const auto b1 = getValueFromSCEV(first->getOperand(0));
            const auto a1 = getValueFromSCEV(first->getOperand(1));

            const auto mul = builder.CreateMul(a1, SplitPoint);
            const auto y = builder.CreateAdd(mul, b1, "y");

            const auto zero = ConstantInt::get(Type::getInt32Ty(F->getContext()), 0);
            const auto one = ConstantInt::get(Type::getInt32Ty(F->getContext()), 1);
            const auto before = builder.CreateSub(SplitPoint, one);
            const auto beforeSCEV = SE->getSCEV(before);
            auto firstBefore = getValueFromSCEV(first->evaluateAtIteration(beforeSCEV, *SE));
            auto secondBefore = getValueFromSCEV(second->evaluateAtIteration(beforeSCEV, *SE));
            const auto isLess = builder.CreateICmp(CmpInst::ICMP_SLT,
                                                   firstBefore,
                                                   secondBefore);
            auto clonedLoop = cloneLoop(F, loop, loopInfo, "FirstLoop");

            BasicBlock *header = loop->getHeader();
            for (Instruction &inst: *header) {
                if (CmpInst *cmp = dyn_cast<CmpInst>(&inst)) {
                    cmp->setOperand(1, y);
                }
            }
            auto branch = cast<BranchInst>(header->getTerminator());
            auto condBlock = branch->getSuccessor(0);
            branch->setOperand(1, clonedLoop->getLoopPreheader());

            if (CmpInst *cmp = dyn_cast<CmpInst>(condBlock->getFirstNonPHI())) {
                cmp->setPredicate(CmpInst::ICMP_EQ);
                cmp->setOperand(0, isLess);
                if (predicate == CmpInst::ICMP_SLT || predicate == CmpInst::ICMP_SLE) {
                    cmp->setOperand(1, ConstantInt::getTrue(F->getContext()));
                } else {
                    cmp->setOperand(1, ConstantInt::getFalse(F->getContext()));
                }
            }

            BasicBlock *clonedHeader = clonedLoop->getHeader();
            auto clonedBranch = cast<BranchInst>(clonedHeader->getTerminator());
            auto clonedCondBlock = clonedBranch->getSuccessor(0);

            if (CmpInst *cmp = dyn_cast<CmpInst>(clonedCondBlock->getFirstNonPHI())) {
                cmp->setPredicate(CmpInst::ICMP_EQ);
                cmp->setOperand(0, isLess);

                if (predicate == CmpInst::ICMP_SLT || predicate == CmpInst::ICMP_SLE) {
                    cmp->setOperand(1, ConstantInt::getFalse(F->getContext()));
                } else {
                    cmp->setOperand(1, ConstantInt::getTrue(F->getContext()));
                }
            }

            auto endCondBlock = clonedLoop->getExitBlock();
            // temporário, adiciona no phi a segnda instrução do header
            // do bloco clonado por enquanto
            // iterando sobre todos pq não sei pegar só o segundo =/
            for (PHINode &node : endCondBlock->phis()) {
                int i = 0;
                for (Instruction &inst : clonedHeader->getInstList()) {
                    if (i == 1) {
                        node.addIncoming(&inst, clonedHeader);
                        node.removeIncomingValue(header);
                        break;
                    }
                    i++;
                }
                break;
            }
            auto originalPhis = header->phis();
            auto clonedPhis = clonedHeader->phis();

            auto original = originalPhis.begin();
            auto cloned = clonedPhis.begin();
            for (; original != originalPhis.end() && cloned != clonedPhis.end(); original++, cloned++) {
                original->dump();
                cloned->dump();

                cloned->setIncomingValue(0, &*original);
            }

//            %.02 = phi i32 [ 3, %1 ], [ %9, %10 ]
//            %.01 = phi i32 [ 0, %1 ], [ %.1, %10 ]
//            %.0 = phi i32 [ 1, %1 ], [ %11, %10 ]
//
//            %.02newLoop = phi i32 [ 3, %12 ], [ %20, %21 ]
//            %.01newLoop = phi i32 [ 0, %12 ], [ %.1newLoop, %21 ]
//            %.0newLoop = phi i32 [ 1, %12 ], [ %22, %21 ]

        }

        bool runOnFunction(Function &F) override {
            auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
            auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
            bool updated = false;


            for(auto bb = F.begin(); bb != F.end(); bb++){
                // bool a = LI.isLoopHeader(dyn_cast<BasicBlock>(bb));
                if(!LI.isLoopHeader(dyn_cast<BasicBlock>(bb))){
                    for(auto it = bb->begin(); it != bb->end(); it++){

                        if(CmpInst* inst = dyn_cast<CmpInst>(it)){

                            Value* op0 = inst->getOperand(0);
                            Value* op1 = inst->getOperand(1);
                            if(SE.isSCEVable(op0->getType()) && SE.isSCEVable(op1->getType())){

                                const SCEV* sc0 = SE.getSCEV(op0);
                                const SCEV* sc1 = SE.getSCEV(op1);
                                if(dyn_cast<SCEVAddRecExpr>(sc0) &&
                                   dyn_cast<SCEVAddRecExpr>(sc1)){
                                    
                                    const SCEVAddRecExpr* sc0Add = dyn_cast<SCEVAddRecExpr>(sc0);
                                    const SCEVAddRecExpr* sc1Add = dyn_cast<SCEVAddRecExpr>(sc1);
                                    if(sc0Add->isAffine() && sc1Add->isAffine()) {
                                        auto builder = IRBuilder<>(inst);
                                        const auto result = calculateIntersectionPoint(sc0Add,
                                                                                       sc1Add,
                                                                                       inst->getPredicate(),
                                                                                       &builder,
                                                                                       &F.getContext());
                                        result->dump();
                                        auto loop = LI.getLoopsInPreorder()[0];
                                        splitLoop(&F,
                                                  loop,
                                                  &LI,
                                                  &SE,
                                                  inst->getPredicate(),
                                                  inst,
                                                  result,
                                                  sc0Add,
                                                  sc1Add);
                                        updated = true;
                                    }

                                }
                            }

                        }
                    }
                }
            }
            F.dump();
            return updated;
        }

        // We don't modify the program, so we preserve all analyses.
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.setPreservesAll();
            getLoopAnalysisUsage(AU);;
        }
    };
}

char LoopSplitting::ID = 0;
static RegisterPass<LoopSplitting>
Y("loopsplit", "Hello World Pass (with getAnalysisUsage implemented)");
