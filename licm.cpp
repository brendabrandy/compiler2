#include "llvm/Pass.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h" // analysis for loops
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"

#include <vector>
// find invariant code
// NOTE: need to make it work for nested loops
using namespace llvm;

namespace{
    struct bso_licm :  public LoopPass{
        static char ID;
        bso_licm() : LoopPass(ID) {};

        bool runOnLoop(Loop * L, LPPassManager &LPM) override{
            // get all instructions inside a loop llvm
            L->dump();
            
            // set invariant code to be null set
            std::vector<Instruction*> invariant_set;
            std::vector<Instruction*> inloop_defs;
            std::vector<BasicBlock* > l_blocks;
            bool is_invariant_changed;
            bool is_invariant_expr;
            bool isChanged;
            Constant* CI;
            BasicBlock* Loop_begin;

            is_invariant_changed = false;
            isChanged = false;
            l_blocks = L->getBlocks();
            if (L->getLoopPreheader() != NULL){
                Loop_begin = &(*(L->getLoopPreheader()));
            }else{
                return false; // NOTE : look into loop simplify
            }
            do{
                is_invariant_changed =false;       
                inloop_defs.clear();      
                for (auto BB : l_blocks){
                    errs() << BB->getName() << "\n" ;
                    for (BasicBlock::iterator DI = BB->begin(); DI != BB->end(); ){
                        Instruction *I = &(*DI++);
                     
                        for (unsigned i = 0 ; i< I->getNumOperands(); i++){
                            is_invariant_expr = false;
                            Value *opnd = I->getOperand(i);
                            
                            // Check 1 : see if operands are constant
                            if ((CI = dyn_cast<Constant>(opnd))){
                                is_invariant_expr = true;
                                continue;
                            }
                            
                            
                            // Check 2 : see if operands are defined outside of the loop
                            for (unsigned i = 0; i < inloop_defs.size(); i++){
                                if (inloop_defs[i] == opnd){
                                    break;
                                }
                                if (i == inloop_defs.size()-1){
                                    is_invariant_expr = true;
                                }
                            }
                            
                            // Check 3 : see if its definition is in invariant set
                            for (unsigned i = 0 ; i < invariant_set.size(); i++){
                                if (invariant_set[i] == opnd){
                                    is_invariant_expr = true;
                                    break;
                                }
                            }
                            
                            if (!is_invariant_expr) {
                                break;
                            }
                        }
                        
                        if (is_invariant_expr){
                            //remove from body
                            if (!(I->isTerminator())){
                                Loop_begin->getTerminator()->dump();
                                I->moveBefore(Loop_begin->getTerminator());
                            
                                invariant_set.push_back(I);
                                is_invariant_changed = true;
                                isChanged = true;
                            }
                        }else{
                            
                            inloop_defs.push_back(I);
                        }           
                    }
                } 
             
            }while(is_invariant_changed);

            return isChanged;
        }
    };
}

char bso_licm::ID = 0;
static RegisterPass<bso_licm> Z("bso_licm", "BSO: Loop Invariant Code Motion");
