#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
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
    assert((predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_ULT ||
            predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SGT ||
            predicate == CmpInst::ICMP_SGE || predicate == CmpInst::ICMP_SLT ||
            predicate == CmpInst::ICMP_SLE) &&
           "We only treat integer inequalities for now");

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
    const auto b = builder->CreateSub(b2, b1, "b");    // b2 - b1
    const auto a = builder->CreateSub(a1, a2, "a");    // a1 - a2
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
      const auto divisible = builder->CreateICmp(
          CmpInst::ICMP_NE, rem, zero, "divisible"); // rem == 0 ? 0 : 1
      const auto extended =
          builder->CreateZExt(divisible, IntegerType::getInt32Ty(*context),
                              "extended"); // extends to 32 bits
      const auto result = builder->CreateAdd(div, extended, "result");
      return result;
    }
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
    const auto ClonedLoop = cloneLoopWithPreheader(
        PreHeader, PreHeader, L, VMap, NameSuffix, LI, &DT, Blocks);
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

  void splitLoop(Function *F, Loop *loop, LoopInfo *loopInfo,
                 ScalarEvolution *SE, CmpInst *Cmp) {

    const CmpInst::Predicate predicate = Cmp->getPredicate();

    assert((predicate == CmpInst::ICMP_UGE || predicate == CmpInst::ICMP_ULT ||
            predicate == CmpInst::ICMP_ULE || predicate == CmpInst::ICMP_SGT ||
            predicate == CmpInst::ICMP_SGE || predicate == CmpInst::ICMP_SLT ||
            predicate == CmpInst::ICMP_SLE) &&
           "We only treat integer inequalities for now");

    ValueToValueMapTy VMap;
    auto clonedLoop = cloneLoop(F, loop, loopInfo, "FirstLoop", VMap);

    auto builder =
        IRBuilder<>(clonedLoop->getLoopPreheader()
                        ->getTerminator()); // builder a partir de onde?

    const SCEV *sc0 = SE->getSCEV(Cmp->getOperand(0));
    const SCEV *sc1 = SE->getSCEV(Cmp->getOperand(1));
    const SCEVAddRecExpr *sc0Add = dyn_cast<SCEVAddRecExpr>(sc0);
    const SCEVAddRecExpr *sc1Add = dyn_cast<SCEVAddRecExpr>(sc1);

    Value *SplitPoint = calculateIntersectionPoint(sc0Add, sc1Add, predicate,
                                                   &builder, &F->getContext());

    const SCEVAddRecExpr *first = sc0Add;
    const SCEVAddRecExpr *second = sc1Add;

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
    auto firstBefore =
        getValueFromSCEV(first->evaluateAtIteration(beforeSCEV, *SE));
    auto secondBefore =
        getValueFromSCEV(second->evaluateAtIteration(beforeSCEV, *SE));
    const auto isLess =
        builder.CreateICmp(CmpInst::ICMP_SLT, firstBefore, secondBefore);

    // setamos o limite do for para o valor de y calculado
    // no nosso exemplo, isso mudaria o for de
    // for (int i = 0; i < n; i += 2)
    // para:
    // for (int i = 0; i < 60; i += 2)
    // isse assume que existe apenas um cmp dentro do header do loop
    // depois temos que alterar para pegar o CMP de alguma outra forma
    /*
        BasicBlock *header = loop->getHeader();
        for (Instruction &inst: *header) {
          if (CmpInst *cmp = dyn_cast<CmpInst>(&inst)) {
            cmp->setOperand(1, y);
          }
        }
        */
    BranchInst *ClonedBr =
        dyn_cast<BranchInst>(clonedLoop->getExitingBlock()->getTerminator());
    assert(ClonedBr->isConditional() && "Expected to be conditional!");
    if (CmpInst *ExitCmp = dyn_cast<CmpInst>(ClonedBr->getCondition())) {
      // TODO: improve this update
      ExitCmp->setOperand(1, y);
    }

    // Desnecessário:
    // branch é um br que pula para o próximo bloco dentro
    // do loop, ou pro bloco fora
    // auto branch = cast<BranchInst>(header->getTerminator());
    // condBlock é o proximo bloco dentro do loop
    // assumimos que esse bloco é o que faz a comparação if (a < i)
    // assumimos também que esse bloco é sempre o na posição 0
    // depois temos que investigar se isso é verdade, e se não
    // ver outra forma de distinguir qual bloco continua no loop
    // e qual pula pra fora
    // auto condBlock = branch->getSuccessor(0);
    // setamos o segundo argumento do loop para pular para o loop clonado
    // ao invés de pular para o retorno da função
    // branch->setOperand(1, clonedLoop->getLoopPreheader());

    // I'm not sure what you wanted to do here, but OK for now
    // essa é a instruçnao que faz o if (a < i) no nosso exemplo
    //            if (CmpInst *cmp =
    //            dyn_cast<CmpInst>(condBlock->getFirstNonPHI())) {
    Cmp->setPredicate(CmpInst::ICMP_EQ); // setamos a comparação para "=="
    // setamos o primeiro operando para se o primeiro SCEV é menos que o segundo
    // antes do ponto de interseção
    Cmp->setOperand(0, isLess);

    // se o predicado for < ou <=, setamos o segundo operando para true
    // senão, false
    // dessa forma, se o primeiro for menor que o segundo, e era isso que
    // queriamos ficamos com if (true == true)
    if (predicate == CmpInst::ICMP_SLT || predicate == CmpInst::ICMP_SLE) {
      Cmp->setOperand(1, ConstantInt::getTrue(F->getContext()));
    } else {
      Cmp->setOperand(1, ConstantInt::getFalse(F->getContext()));
    }
    //}

    // BasicBlock *clonedHeader = clonedLoop->getHeader();
    // auto clonedBranch = cast<BranchInst>(clonedHeader->getTerminator());
    // bloco com o if do loop clonado
    // auto clonedCondBlock = clonedBranch->getSuccessor(0);

    // mesma coisa que em cima, só que agora ao contrário
    if (CmpInst *ClonedCmp = dyn_cast<CmpInst>(VMap[Cmp])) {
      ClonedCmp->setPredicate(CmpInst::ICMP_EQ);
      ClonedCmp->setOperand(0, isLess);

      if (predicate == CmpInst::ICMP_SLT || predicate == CmpInst::ICMP_SLE) {
        ClonedCmp->setOperand(1, ConstantInt::getFalse(F->getContext()));
      } else {
        ClonedCmp->setOperand(1, ConstantInt::getTrue(F->getContext()));
      }
    }

    /*
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
        for (; original != originalPhis.end() && cloned != clonedPhis.end();
       original++, cloned++) { cloned->setIncomingValue(0, &*original);
        }
        */

    for (PHINode &PHI : loop->getHeader()->phis()) {
      PHINode *ClonedPHI = dyn_cast<PHINode>(VMap[&PHI]);
      Value *LastValue = ClonedPHI;
      if (clonedLoop->getExitingBlock() == clonedLoop->getLoopLatch()) {
        LastValue =
            ClonedPHI->getIncomingValueForBlock(clonedLoop->getLoopLatch());
      } else
        assert(clonedLoop->getExitingBlock() == clonedLoop->getHeader() &&
               "Expected exiting block to be the loop header!");
      PHI.setIncomingValue(PHI.getBasicBlockIndex(loop->getLoopPreheader()),
                           LastValue);
    }
  }

  bool isAValidLoop(Loop *L) {
    if (!L->getSubLoops().empty())
      return false;

    BasicBlock *ExitingBB = L->getExitingBlock();
    if (ExitingBB == nullptr)
      return false;

    BranchInst *ExitingBr = dyn_cast<BranchInst>(ExitingBB->getTerminator());
    if (ExitingBr == nullptr)
      return false;

    return true;
  }

  std::set<CmpInst *> GetAllCmps(Loop *L) {
    std::set<CmpInst *> AllCmps;

    for (BasicBlock *BB : L->blocks()) {
      for (Instruction &I : *BB) {
        if (SelectInst *Sel = dyn_cast<SelectInst>(&I)) {
          if (CmpInst *Cmp = dyn_cast<CmpInst>(Sel->getCondition()))
            AllCmps.insert(Cmp);
        }
      }

      if (!L->isLoopExiting(BB)) {
        BranchInst *Br = dyn_cast<BranchInst>(BB->getTerminator());
        if (Br && Br->isConditional()) {
          if (CmpInst *Cmp = dyn_cast<CmpInst>(Br->getCondition()))
            AllCmps.insert(Cmp);
        }
      }
    }

    return AllCmps;
  }

  std::vector<std::pair<Loop *, CmpInst *>>
  getPairFromCmp(ScalarEvolution &SE, std::set<CmpInst *> AllCmps, Loop *L) {

    std::vector<std::pair<Loop *, CmpInst *>> WorkList;
    for (CmpInst *Cmp : AllCmps) {
      Value *op0 = Cmp->getOperand(0);
      Value *op1 = Cmp->getOperand(1);
      if (SE.isSCEVable(op0->getType()) && SE.isSCEVable(op1->getType())) {
        const SCEV *sc0 = SE.getSCEV(op0);
        const SCEV *sc1 = SE.getSCEV(op1);

        if (dyn_cast<SCEVAddRecExpr>(sc0) && dyn_cast<SCEVAddRecExpr>(sc1)) {
          const SCEVAddRecExpr *sc0Add = dyn_cast<SCEVAddRecExpr>(sc0);
          const SCEVAddRecExpr *sc1Add = dyn_cast<SCEVAddRecExpr>(sc1);
          if (sc0Add->isAffine() && sc1Add->isAffine()) {
            // Cmp->dump();
            // sc0->dump();
            // sc1->dump();

            WorkList.push_back(std::pair<Loop *, CmpInst *>(L, Cmp));
          }
        }
      }
    }

    return WorkList;
  }

  bool analyseLoops(Function &F, llvm::LoopInfo &LI,
                    llvm::ScalarEvolution &SE) {
    bool updated = false;
    std::vector<std::pair<Loop *, CmpInst *>> WorkList;

    for (Loop *L : LI) {

      if (!isAValidLoop(L)) {
        continue;
      }

      std::set<CmpInst *> AllCmps = GetAllCmps(L);

      if (AllCmps.size() != 1)
        continue;

      WorkList = getPairFromCmp(SE, AllCmps, L);
    }

    for (auto &Pair : WorkList) {
      Loop *L = Pair.first;

      for (BasicBlock *BB : L->getBlocks()) {
        errs() << *BB;
      }

      CmpInst *Cmp = Pair.second;

      splitLoop(&F, L, &LI, &SE, Cmp);

      updated = true;
    }
    errs() << "Modified Function:\n";
    return updated;
  }

  bool runOnFunction(Function &F) override {
    auto &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    auto &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();

    bool updated = false;
    updated = analyseLoops(F, LI, SE);

    return updated;
  }

  // We don't modify the program, so we preserve all analyses.
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    getLoopAnalysisUsage(AU);
    ;
  }
};
} // namespace

char LoopSplitting::ID = 0;
static RegisterPass<LoopSplitting>
    Y("loopsplit", "Hello World Pass (with getAnalysisUsage implemented)");