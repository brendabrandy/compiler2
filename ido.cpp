#include "llvm/Pass.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h" // analysis for loops
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Instruction.def"

#include <vector>

using namespace llvm;

namespace{
    struct bso_ido :  public LoopPass{
        static char ID;
        bso_ido() : LoopPass(ID) {};

        void getAnalysisUsage(AnalysisUsage &Info) const{
            // Info.setPreservesCFG();
            Info.addRequired<ScalarEvolutionWrapperPass>();
        }

        struct triplet{
            // stores triplet j = a*i +b, where i is basic induction variable 
            // %t1 = %a * %i
            // %j = %t1 + %b
            Instruction * i_mult;
            Instruction * i_add;
        };

        bool runOnLoop(Loop * L, LPPassManager &LPM) override{
            bool isChanged = false;

            PHINode* induction_var;
            std::vector<BasicBlock*> l_blocks;
            std::vector<Instruction*> induction_vars;
            std::vector<triplet*> indvar_family;
            l_blocks = L->getBlocks();
            triplet* curr_triplet;
            ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();

            // find all induction variables!
            for (auto BB : l_blocks){
                for (BasicBlock::iterator DI = BB->begin(); DI != BB->end();){
                    Instruction *I = &(*DI++);
                    // to detect and analyze induction variables, use ScalarEvolution 
                    // we need to get hold of ScalarEvolution object and use ScalarEvolution::getSCEV
                    // method to translate llvm::Value to an llvm::SCEV. If the llvm::SCEV* you get back
                    // is an llvm::SCEVAddRecExpr*, then the llvm::Value* is an induction variable
                    if ((induction_var = dyn_cast<PHINode>(I))){
                        const SCEV * S = SE.getSCEVAtScope(I,L);
                        const SCEVAddRecExpr * SARE = dyn_cast<SCEVAddRecExpr>(S);
                        if (SARE != NULL){
                            errs() <<  "Found induction variable : " <<  I->getName() <<  "\n";
                            // find out how much the induction variable steps by
                            // add to induction vars if it is simple addition and subtraction by a constant
                            induction_vars.push_back(I);
                            S = SARE->getStepRecurrence(SE);
                            S->dump();
                        }
                    }
                }
            }
            
            // for each induction variable, go through 
            for (unsigned i = 0 ; i < induction_vars.size(); i++){
                Instruction *curr_induction_var = induction_vars[i];
                indvar_family.clear();
                for (auto BB : l_blocks){
                    for (BasicBlock::iterator DI = BB->begin(); DI != BB->end(); ){
                        Instruction *I = &(*DI++);
                        if (I->getOpcode() == Instruction::Mul){
                            // if one of the operands is i and the other is loop invariant
                            // add it as a new triplet
                            // TODO: Data dependence on loop invariant variable
                            if ((I->getOperand(0) == curr_induction_var and 
                                L->isLoopInvariant(I->getOperand(1))) or
                                (I->getOperand(1) == curr_induction_var and
                                L->isLoopInvariant(I->getOperand(0)))){
                                curr_triplet = new triplet;
                                curr_triplet->i_mult = I;
                                curr_triplet->i_add = NULL;
                                indvar_family.push_back(curr_triplet);
                            }
                        }else if (I->getOpcode() == Instruction::Add){
                            // check if one of the operands is loop invariant and the other 
                            // already exist in the list of triplets that we are keeping track of
                            // if so, add the addition to the list
                            // TODO: what happens if the i_mult is used twicec?
                            for (unsigned i = 0 ; i < indvar_family.size(); i++){
                                if (indvar_family[i]->i_add == NULL)
                                    if ((I->getOperand(0) == indvar_family[i]->i_mult and
                                         L->isLoopInvariant(I->getOperand(1))) or
                                        (I->getOperand(1) == indvar_family[i]->i_mult and
                                        L->isLoopInvariant(I->getOperand(0)))){
                                        indvar_family[i]->i_add = I;
                                        break;
                                    }
                                }
                            }
                        }
                    
                    }
                
                // now go through all the triplets and pull them out of the loop
                for (unsigned i = 0 ; i <  indvar_family.size(); i++){
                    indvar_family[i]->i_mult->dump();
                    if (indvar_family[i]->i_add != NULL){
                        indvar_family[i]->i_add->dump();
                    }
                    errs() << "----------------------------------\n";
                }               
            }
             

            // go through the list of variables
            // if both mult and add are not null
            // add it to the preheader
            // and add s = i*c right after increment of i
            return isChanged;
        }
    };
}

char bso_ido::ID = 0;
static RegisterPass<bso_ido> A("bso_ido", "BSO: Induction Variable Optimization");
