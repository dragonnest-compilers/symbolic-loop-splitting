#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include <typeinfo>

using namespace llvm;

#define DEBUG_TYPE "hello"

namespace {
    struct SplitInfo {
        Value *point;
        Value *iterationValue;
        Value *isTrueAtPoint;
        Value *nextValue;
        Value *isTrueAtNextPoint;
        CmpInst *comparison;
        
        SplitInfo(Value *point, Value *iterationValue, Value *isTrueAtPoint, Value *nextValue, Value *isTrueAtNextPoint, CmpInst *comparison) {
            this->point = point;
            this->isTrueAtPoint = isTrueAtPoint;
            this->comparison = comparison;
            this->iterationValue = iterationValue;
            this->nextValue = nextValue;
            this->isTrueAtNextPoint = isTrueAtNextPoint;

        }
    };
    // Hello2 - The second implementation with getAnalysisUsage implemented.
    struct LoopSplitting : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
    private:
        SCEVExpander *expander;
        
    public:
        LoopSplitting() : FunctionPass(ID) {}
        

        Value *calculateIntersectionPoint(const SCEVAddRecExpr *add,
                                          const SCEVConstant *constant,
                                          CmpInst *compare,
                                          IRBuilder<> &builder) {
            
            auto predicate = compare->getPredicate();
            assert(add->isAffine() && "SCEVs must be affine");
            assert((predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_ULT ||
                    predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SGT ||
                    predicate == CmpInst::ICMP_SGE || predicate == CmpInst::ICMP_SLT ||
                    predicate == CmpInst::ICMP_SLE) &&
                   "We only treat integer inequalities for now");
            add->print(errs());
            errs() << "\n";
            const auto b = this->expander->expandCodeFor(add->getOperand(0),
                                                         constant->getValue()->getType(),
                                                         compare->getParent()->getFirstNonPHI());
            const auto a = this->expander->expandCodeFor(add->getOperand(1),
                                                         constant->getValue()->getType(),
                                                         builder.GetInsertBlock()->getFirstNonPHI());
            b->print(errs());
            errs() << "\n";
            a->print(errs());
            errs() << "\n";

            const auto y = constant->getValue();
            
            // Como y = ax + b
            // colocamos como y a constante e calculamos x a partir disso:
            // Ou seja: x = (y - b) / a

            const auto temp1 = builder.CreateSub(y, b, "yMinusB"); // y - b
            const auto x = builder.CreateSDiv(temp1, a, "x"); // (y - b) / a
//            const auto biggerThanZero = builder.CreateICmpSGE(x, Constant::getNullValue(x->getType()), "biggerThan0");
//            const auto select = builder.CreateSelect(biggerThanZero, x, Constant::getNullValue(x->getType()), "select");
            
            return x;
        }

        
        std::set<CmpInst *> getLoopComparisons(const Loop &L) {
            std::set<CmpInst *> AllCmps;
            
            for (BasicBlock *BB : L.blocks()) {
                for (Instruction &I : *BB) {
                    if (SelectInst *Sel = dyn_cast<SelectInst>(&I)) {
                        if (CmpInst *Cmp = dyn_cast<CmpInst>(Sel->getCondition()))
                            AllCmps.insert(Cmp);
                    }
                }
                
                if (!L.isLoopExiting(BB)) {
                    BranchInst *Br = dyn_cast<BranchInst>(BB->getTerminator());
                    if (Br && Br->isConditional()) {
                        if (CmpInst *Cmp = dyn_cast<CmpInst>(Br->getCondition()))
                            AllCmps.insert(Cmp);
                    }
                }
            }
            
            return AllCmps;
        }
        
        std::set<CmpInst *> collectCandidateInstructions(Loop &loop) {
            auto comparisons = getLoopComparisons(loop);
            for (Loop *subloop : loop.getSubLoops()) {
                auto subLoopComparisons = getLoopComparisons(*subloop);
                comparisons.insert(subLoopComparisons.begin(), subLoopComparisons.end());
            }
            return comparisons;
        }
        
        std::set<CmpInst *> collectCandidateInstructions(LoopInfo &loopInfo) {
            auto allComparisons = std::set<CmpInst *>();
            for (Loop *loop : loopInfo) {
                auto loopComparisons = collectCandidateInstructions(*loop);
                allComparisons.insert(loopComparisons.begin(), loopComparisons.end());
            }
            return allComparisons;
        }
        
        bool isAffineAndConstantComparison(ScalarEvolution &SE, CmpInst &comparison) {
            auto first = SE.getSCEV(comparison.getOperand(0));
            auto second = SE.getSCEV(comparison.getOperand(1));
            if ((first->getSCEVType() == scConstant || second->getSCEVType() == scConstant) &&
                (first->getSCEVType() == scAddRecExpr || second->getSCEVType() == scAddRecExpr)) {
                auto *addRec = dyn_cast<SCEVAddRecExpr>(first);
                if (addRec == nullptr) {
                    addRec = dyn_cast<SCEVAddRecExpr>(second);
                }
                return addRec->isAffine();
            }
            return false;
        }
        
        bool isBothAffineComparison(ScalarEvolution &SE, CmpInst &comparison) {
            auto first = SE.getSCEV(comparison.getOperand(0));
            auto second = SE.getSCEV(comparison.getOperand(1));
            if (first->getSCEVType() == scAddRecExpr || second->getSCEVType() == scAddRecExpr) {
                auto *firstAddRec = cast<SCEVAddRecExpr>(first);
                auto *secondAddRec = cast<SCEVAddRecExpr>(second);
                return firstAddRec->isAffine() && secondAddRec->isAffine();
            }
            return false;
        }
        
        Loop * getLoop(CmpInst *comparison, LoopInfo &LI, ScalarEvolution &SE) {
            const SCEVConstant *constant;
            const SCEVAddRecExpr *affine;

            if (isAffineAndConstantComparison(SE, *comparison)) {
                auto first = SE.getSCEV(comparison->getOperand(0));
                auto second = SE.getSCEV(comparison->getOperand(1));
                
                bool firstIsConstant = false;
                if (first->getSCEVType() == scConstant) {
                    constant = cast<SCEVConstant>(first);
                    affine = cast<SCEVAddRecExpr>(second);
                    firstIsConstant = true;
                } else {
                    constant = cast<SCEVConstant>(second);
                    affine = cast<SCEVAddRecExpr>(first);
                }
            } else {
                return nullptr;
            }

            auto loop = affine->getLoop();
            auto tempLoop = LI.getLoopFor(comparison->getParent());

            while (true) {
                if (loop == tempLoop) {
                    return tempLoop;
                }
                tempLoop = tempLoop->getParentLoop();
            }
        }
        
        std::vector<SplitInfo> comparisonToSplitInfo(ScalarEvolution &SE,
                                                     LoopInfo &LI,
                                                     std::set<CmpInst *> &comparisons) {
            auto splitInfoVector = std::vector<SplitInfo>();
            for (CmpInst *instruction : comparisons) {
                if (isAffineAndConstantComparison(SE, *instruction)) {
                    auto first = SE.getSCEV(instruction->getOperand(0));
                    auto second = SE.getSCEV(instruction->getOperand(1));
                    
                    const SCEVConstant *constant;
                    const SCEVAddRecExpr *affine;
                    bool firstIsConstant = false;
                    if (first->getSCEVType() == scConstant) {
                        constant = cast<SCEVConstant>(first);
                        affine = cast<SCEVAddRecExpr>(second);
                        firstIsConstant = true;
                    } else {
                        constant = cast<SCEVConstant>(second);
                        affine = cast<SCEVAddRecExpr>(first);
                    }
                    
                    auto loop = getLoop(instruction, LI, SE);
                    auto insertionPoint = loop->getLoopPreheader()->getFirstNonPHI();
                    auto builder = IRBuilder<>(insertionPoint);

                    auto value = calculateIntersectionPoint(affine, constant, instruction, builder);
                    auto scevValue = SE.getSCEV(value);
                    auto iterationScev = affine->evaluateAtIteration(scevValue, SE);
                    auto iterationValue = expander->expandCodeFor(iterationScev, constant->getValue()->getType(), insertionPoint);
                    
                    auto nextScevValue = SE.getAddExpr(scevValue, SE.getOne(value->getType()));
                    auto nextIterationScev = affine->evaluateAtIteration(nextScevValue, SE);
                    auto nextIterationValue = expander->expandCodeFor(nextIterationScev,
                                                                      constant->getValue()->getType(), insertionPoint);
                    

                    Value *v = builder.CreateICmp(instruction->getPredicate(),
                                                  firstIsConstant ? constant->getValue() : iterationValue,
                                                  firstIsConstant ? iterationValue : constant ->getValue());
                    Value *nextPoint = builder.CreateICmp(instruction->getPredicate(),
                                                          firstIsConstant ? constant->getValue() : nextIterationValue,
                                                          firstIsConstant ? nextIterationValue : constant ->getValue());
                    
                    auto loopBranch = cast<BranchInst>(loop->getExitingBlock()->getTerminator());
                    assert(loopBranch->isConditional() && "Expected to be conditional!");
                    CmpInst *exitCmp = cast<CmpInst>(loopBranch->getCondition());
                    auto loopScev = cast<SCEVAddRecExpr>(SE.getSCEV(exitCmp->getOperand(0)));
                    auto loopEndValue = expander->expandCodeFor(loopScev->evaluateAtIteration(scevValue, SE), constant->getValue()->getType(), insertionPoint);
                    
                    auto valueAfterLoop = expander->expandCodeFor(loopScev->evaluateAtIteration(nextScevValue, SE), constant->getValue()->getType(), insertionPoint);
                    auto splitInfo = SplitInfo(value, loopEndValue, v, valueAfterLoop, nextPoint, instruction);
                    splitInfoVector.push_back(splitInfo);
                }
            }
            return splitInfoVector;
        }
        
        Loop *cloneLoop(Function *F, Loop *L, LoopInfo *LI, const Twine &NameSuffix,
                        ValueToValueMapTy &VMap) {
            
            // original preheader of the loop
            const auto PreHeader = L->getLoopPreheader();
            
            // keep track of the original predecessors
            std::set<BasicBlock *> AllPredecessors;
            for (auto PredIt = pred_begin(PreHeader), E = pred_end(PreHeader);
                 PredIt != E; PredIt++)
                AllPredecessors.insert(*PredIt);
            
            BasicBlock *ExitBlock = L->getExitBlock();
            
            auto DT = DominatorTree(*F);
            
            SmallVector<BasicBlock *, 8> Blocks;
            const auto ClonedLoop = cloneLoopWithPreheader(PreHeader, PreHeader, L, VMap, NameSuffix, LI, &DT, Blocks);
            VMap[ExitBlock] = PreHeader; // chain: cloned loop -> original loop
            remapInstructionsInBlocks(Blocks, VMap);
            
            // remap original predecessors to the cloned loop
            for (BasicBlock *PredBB : AllPredecessors) {
                Instruction *TI = PredBB->getTerminator();
                for (unsigned i = 0; i < TI->getNumOperands(); i++) {
                    if (TI->getOperand(i) == PreHeader)
                        TI->setOperand(i, ClonedLoop->getLoopPreheader());
                }
            }
            
            return ClonedLoop;
        }

        void splitLoop(ScalarEvolution &SE, Function *F, Loop *loop, LoopInfo *LI, SplitInfo *info) {
            
            const CmpInst::Predicate predicate = info->comparison->getPredicate();
            assert((predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_ULT ||
                    predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SGT ||
                    predicate == CmpInst::ICMP_SGE || predicate == CmpInst::ICMP_SLT ||
                    predicate == CmpInst::ICMP_SLE) &&
                   "We only treat integer inequalities for now");
            
            // só funciona para < e >
            auto comparisonPredicate = info->comparison->getPredicate();
            info->comparison->setOperand(0, ConstantInt::getFalse(F->getContext()));
            info->comparison->setOperand(1, info->isTrueAtNextPoint);

            info->comparison->setPredicate(ICmpInst::ICMP_EQ);
            
            ValueToValueMapTy VMap;
            auto clonedLoop = cloneLoop(F, loop, LI, "FirstLoop", VMap);
            info->comparison->setOperand(0, ConstantInt::getTrue(F->getContext()));


            BranchInst *ClonedBr = cast<BranchInst>(clonedLoop->getExitingBlock()->getTerminator());
            assert(ClonedBr->isConditional() && "Expected to be conditional!");
            if (CmpInst *ExitCmp = dyn_cast<CmpInst>(ClonedBr->getCondition())) {
                if (comparisonPredicate == CmpInst::ICMP_SLT || comparisonPredicate ==  CmpInst::ICMP_SGE) {
                    ExitCmp->setPredicate(CmpInst::ICMP_SLT);
                } else {
                    ExitCmp->setPredicate(CmpInst::ICMP_SLE);
                }
                if (VMap[info->iterationValue]) {
                    ExitCmp->setOperand(1, VMap[info->iterationValue]);
                } else {
                    ExitCmp->setOperand(1, info->iterationValue);
                }
            }

            int i = 0;
            for (PHINode &PHI : loop->getHeader()->phis()) {
                PHI.print(errs());
                errs() << "\n";
                PHINode *ClonedPHI = dyn_cast<PHINode>(VMap[&PHI]);
                ClonedPHI->print(errs());
                errs() << "\n";

                Value *LastValue = ClonedPHI;
                if (clonedLoop->getExitingBlock() == clonedLoop->getLoopLatch()) {
                    LastValue =
                    ClonedPHI->getIncomingValueForBlock(clonedLoop->getLoopLatch());
                } else
                    assert(clonedLoop->getExitingBlock() == clonedLoop->getHeader() &&
                           "Expected exiting block to be the loop header!");
                if (i == -1) {
//                    ClonedPHI->setIncomingValue(0, ConstantInt::get(ClonedPHI->getType(), 0));
                    PHI.setIncomingValue(0, info->nextValue);
                } else {
                    PHI.setIncomingValue(PHI.getBasicBlockIndex(loop->getLoopPreheader()),
                                         LastValue);
                }
                i++;
            }
        }
        
        bool runOnFunction(Function &F) override {
            auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
            auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();
            
            this->expander = new SCEVExpander(SE, DataLayout(F.getParent()), "name");

            auto allComparisons = collectCandidateInstructions(LI);
            auto splitInfo = comparisonToSplitInfo(SE, LI, allComparisons);
            for (SplitInfo info : splitInfo) {
                splitLoop(SE, &F, getLoop(info.comparison, LI, SE), &LI, &info);
            }
            F.print(errs());
            return true;
        }
        
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.setPreservesAll();
            getLoopAnalysisUsage(AU);
        }

    };
} // namespace

char LoopSplitting::ID = 0;
static RegisterPass<LoopSplitting>
Y("loopsplit", "Hello World Pass (with getAnalysisUsage implemented)");
