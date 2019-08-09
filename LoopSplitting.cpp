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
                                          LLVMContext *context) {
            assert(first->isAffine() && second->isAffine() && "SCEVs must be affine");

            const auto b1 = getValueFromSCEV(first->getOperand(0));
            const auto a1 = getValueFromSCEV(first->getOperand(1));
            const auto b2 = getValueFromSCEV(second->getOperand(0));
            const auto a2 = getValueFromSCEV(second->getOperand(1));

//            qual código gerar quando as linhas são paralelas?
//            (int) (((double) b2 - (double) b1) / ((double) a1 - (double) a2));
//            %conv = sitofp i32 %b2 to double
//            %conv1 = sitofp i32 %b1 to double
//            %sub = fsub double %conv, %conv1
//            %conv2 = sitofp i32 %a1 to double
//            %conv3 = sitofp i32 %a2 to double
//            %sub4 = fsub double %conv2, %conv3
//            %div = fdiv double %sub, %sub4
//            %conv5 = fptosi double %div to i32

            IRBuilder<> builder(*context);
            const auto b2Double = builder.CreateSIToFP(b2, Type::getDoubleTy(*context), "b2Double");
            const auto b1Double = builder.CreateSIToFP(b1, Type::getDoubleTy(*context), "b1Double");
            const auto bSub = builder.CreateFSub(b2Double, b1Double, "bSub");
            const auto a2Double = builder.CreateSIToFP(a2, Type::getDoubleTy(*context), "a2Double");
            const auto a1Double = builder.CreateSIToFP(a1, Type::getDoubleTy(*context), "a1Double");
            const auto aSub = builder.CreateFSub(a1Double, a2Double, "aSub");
            const auto div = builder.CreateFDiv(bSub, aSub, "div");
            const auto convInt = builder.CreateFPToSI(div, Type::getInt32Ty(*context));

            return convInt;
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
