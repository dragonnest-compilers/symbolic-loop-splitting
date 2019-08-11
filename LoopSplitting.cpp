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
            // calcula o valor do y para o x encontrado
            // assume que o y do for é o primeiro SCEV
            // podemos mudar isso para getSCEV e evaluateAtIteration
            const auto y = builder.CreateAdd(mul, b1, "y");

            // para saber se qual reta é maior antes do ponto de interseção
            // subtraimos um do X, calculamos o valor de ambas as retas para esse ponto
            // e guardamos o resultado do primeiro < segundo em "isLess"
            const auto one = ConstantInt::get(Type::getInt32Ty(F->getContext()), 1);
            const auto before = builder.CreateSub(SplitPoint, one);
            const auto beforeSCEV = SE->getSCEV(before);
            auto firstBefore = getValueFromSCEV(first->evaluateAtIteration(beforeSCEV, *SE));
            auto secondBefore = getValueFromSCEV(second->evaluateAtIteration(beforeSCEV, *SE));
            const auto isLess = builder.CreateICmp(CmpInst::ICMP_SLT,
                                                   firstBefore,
                                                   secondBefore);

            auto clonedLoop = cloneLoop(F, loop, loopInfo, "FirstLoop");

            // setamos o limite do for para o valor de y calculado
            // no nosso exemplo, isso mudaria o for de
            // for (int i = 0; i < n; i += 2)
            // para:
            // for (int i = 0; i < 60; i += 2)
            // isse assume que existe apenas um cmp dentro do header do loop
            // depois temos que alterar para pegar o CMP de alguma outra forma
            BasicBlock *header = loop->getHeader();
            for (Instruction &inst: *header) {
                if (CmpInst *cmp = dyn_cast<CmpInst>(&inst)) {
                    cmp->setOperand(1, y);
                }
            }

            // branch é um br que pula para o próximo bloco dentro
            // do loop, ou pro bloco fora
            auto branch = cast<BranchInst>(header->getTerminator());
            // condBlock é o proximo bloco dentro do loop
            // assumimos que esse bloco é o que faz a comparação if (a < i)
            // assumimos também que esse bloco é sempre o na posição 0
            // depois temos que investigar se isso é verdade, e se não
            // ver outra forma de distinguir qual bloco continua no loop
            // e qual pula pra fora
            auto condBlock = branch->getSuccessor(0);

            // setamos o segundo argumento do loop para pular para o loop clonado
            // ao invés de pular para o retorno da função
            branch->setOperand(1, clonedLoop->getLoopPreheader());

            // esa é a instruçnao que faz o if (a < i) no nosso exemplo
            if (CmpInst *cmp = dyn_cast<CmpInst>(condBlock->getFirstNonPHI())) {
                cmp->setPredicate(CmpInst::ICMP_EQ); // setamos a comparação para "=="
                // setamos o primeiro operando para se o primeiro SCEV é menos que o segundo
                // antes do ponto de interseção
                cmp->setOperand(0, isLess);

                // se o predicado for < ou <=, setamos o segundo operando para true
                // senão, false
                // dessa forma, se o primeiro for menor que o segundo, e era isso que queriamos
                // ficamos com if (true == true)
                if (predicate == CmpInst::ICMP_SLT || predicate == CmpInst::ICMP_SLE) {
                    cmp->setOperand(1, ConstantInt::getTrue(F->getContext()));
                } else {
                    cmp->setOperand(1, ConstantInt::getFalse(F->getContext()));
                }
            }

            BasicBlock *clonedHeader = clonedLoop->getHeader();
            auto clonedBranch = cast<BranchInst>(clonedHeader->getTerminator());
            // bloco com o if do loop clonado
            auto clonedCondBlock = clonedBranch->getSuccessor(0);

            // mesma coisa que em cima, só que agora ao contrário
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
            // temporário, adiciona no phi a segunda instrução do header
            // do bloco clonado por enquanto
            // iterando sobre todos pq não sei pegar só o segundo =/
            // alteramos esse phi pois ele esperava receber o jmp
            // do fim do primeiro loop, mas agora que vai pular
            // para ele é o do segundo loop
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

            // alteramos os phis do header do loop clonado para
            // receberem o valor final dos equivalentes no loop original
            // na primeira iteração do loop clonado
            auto original = originalPhis.begin();
            auto cloned = clonedPhis.begin();
            for (; original != originalPhis.end() && cloned != clonedPhis.end(); original++, cloned++) {
                cloned->setIncomingValue(0, &*original);
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
