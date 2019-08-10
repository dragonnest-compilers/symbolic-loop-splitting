#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
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
                                        const auto result = calculateIntersectionPoint(sc0Add, sc1Add, &F.getContext());
                                        result->dump();
                                    }

                                }
                            }

                        }
                    }
                }
            }

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
