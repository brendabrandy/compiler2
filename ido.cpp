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
#include "llvm/IR/IRBuilder.h"

#include <string>
#include <vector>

using namespace llvm;

namespace{
    struct bso_ido :  public LoopPass{
        static char ID;
        bso_ido() : LoopPass(ID) {};
        int counter = 0;

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
            Value * coef_mult;
        };

        bool runOnLoop(Loop * L, LPPassManager &LPM) override{
            
            bool isChanged;
            PHINode* induction_var;
            std::vector<BasicBlock*> l_blocks;
            std::vector<Instruction*> induction_vars;
            std::vector<triplet*> indvar_family;
            BasicBlock* loop_begin;

            isChanged = false;
            l_blocks = L->getBlocks();
            triplet* curr_triplet;
            ScalarEvolution &SE = getAnalysis<ScalarEvolutionWrapperPass>().getSE();

            if (L->getLoopPreheader() != NULL){
                loop_begin = &(*(L->getLoopPreheader()));
            }else{
                return false;
            }

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
                        }
                    }
                }
            }
            
            // for each induction variable, go through the basic blocks again and find the 
            // variables that are in the form j = a*i + b, where a and b are loop invariant
            // and i is the induction variable. If such a variable is found, we store them
            // in the family of triplets of induction variable i
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
                                if (L->isLoopInvariant(I->getOperand(0))){
                                    curr_triplet->coef_mult = I->getOperand(0);
                                }else{
                                    curr_triplet->coef_mult = I->getOperand(1);
                                }
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
                

                // entry expression
                Value* entry = dyn_cast<PHINode>(curr_induction_var)->getIncomingValue(0);
                entry->dump();
                // increment expression
                Value* increment = dyn_cast<PHINode>(curr_induction_var)->getIncomingValue(1);
                increment->dump();
                // now go through all the triplets and pull them out of the loop
                for (unsigned i = 0 ; i <  indvar_family.size(); i++){
                    
                    // first, move the a*i + b instruction to the preheader
                    if (indvar_family[i]->i_add != NULL){
                    if (indvar_family[i]->i_mult->getOperand(0) == curr_induction_var){
                        indvar_family[i]->i_mult->setOperand(0, entry);
                    }else{
                        indvar_family[i]->i_mult->setOperand(1, entry);
                    }
                    indvar_family[i]->i_mult->moveBefore(loop_begin->getTerminator());
                    indvar_family[i]->i_add->moveBefore(loop_begin->getTerminator());
                    IRBuilder<> Builder1(indvar_family[i]->i_add);
                    
                    // set the new increment to be a * (increment of i)
                    Value *new_increment;
                    if (dyn_cast<Instruction>(increment)->getOperand(0) != curr_induction_var){
                        new_increment = Builder1.CreateBinOp(Instruction::Mul, 
                                    curr_triplet->coef_mult, dyn_cast<Instruction>(increment)->getOperand(0),
                                    "bso_newincrement"+std::to_string(counter));
                    }else{
                        new_increment = Builder1.CreateBinOp(Instruction::Mul,
                                    curr_triplet->coef_mult,dyn_cast<Instruction>(increment)->getOperand(1),
                                    "bso_newincrement"+std::to_string(counter));
                    }
                
                    // add the phi node at the entry block
                    IRBuilder<> Builder(curr_induction_var);
                    PHINode* PN = Builder.CreatePHI(indvar_family[i]->i_add->getType(),
                                                    2, "bso_newPHI"+std::to_string(counter));
                    PN->addIncoming(indvar_family[i]->i_add, 
                                    dyn_cast<PHINode>(curr_induction_var)->getIncomingBlock(0));
                    
                    // then, insert the addition increment after the increment of the induction
                    // variable
                    IRBuilder<> Builder2(dyn_cast<Instruction>(increment));
                    auto *new_inst = Builder2.CreateBinOp(Instruction::Add, PN, new_increment, 
                                        "bso_newAdd"+std::to_string(counter));
                    PN->addIncoming(new_inst, dyn_cast<PHINode>(curr_induction_var)->getIncomingBlock(1));
                    
                    isChanged = true;
                    counter++;
                    }
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
