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
                    if(sc0Add->isAffine() && sc1Add->isAffine())
                      print("sucesso");

                  }
              }

            }
          }
        }
      }

      return updated;
    }

    //Saída no console
		void print(Value* value){
			errs() << *value << "\n";
		}
    void print(char text[]){
      errs() << text << "\n";
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
