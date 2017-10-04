#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.def"
using namespace llvm;

#define DEBUG_TYPE "bso_cp"
STATISTIC(NumXForms, "# of instructions deleted");

namespace{
    struct bso_cp : public FunctionPass{
        static char ID;
        bso_cp() : FunctionPass(ID) {};

        bool runOnFunction(Function &F) override{
            ConstantInt* CI1, *CI2;
            Value * newVal;
            int op1, op2, fin_val, opcode;
            bool is_change;

            is_change = false;
            // for every basic block in Function
            for (Function::iterator b = F.begin(); b != F.end(); ){
                // for every instruction in basic block
                BasicBlock *BB = &(*b++);
                for(BasicBlock::iterator DI = BB->begin(); DI != BB->end(); ){
                    Instruction *I = &(*DI++);
                    // if it is a binary operator
                    if (auto* op = dyn_cast<BinaryOperator>(I)){
                        // if both operands are constants
                        if ((CI1 = dyn_cast<ConstantInt>(I->getOperand(0))) and
                                (CI2 =dyn_cast<ConstantInt>(I->getOperand(1)))){
                            // evaluate the expression
                            op1 = CI1->getSExtValue();
                            op2 = CI2->getSExtValue();
                            opcode = I->getOpcode();
                            if (opcode == Instruction::Mul){
                                fin_val = op1 * op2;    
                            }else if (opcode == Instruction::Add){
                                fin_val = op1 + op2;
                            }else if (opcode == Instruction::Sub){
                                fin_val = op1 - op2;
                            }else if (opcode == Instruction::SDiv){
                                fin_val = op1 / op2;
                            }else if (opcode == Instruction::SRem){
                                fin_val = op1 % op2;
                            }else{
                                continue;
                            }
                            newVal = ConstantInt::get(CI1->getType(), fin_val);
                            // replae all uses with the new constant
                            I->replaceAllUsesWith(newVal);
                            // remove that instruction
                            I->eraseFromParent();
                            ++NumXForms;
                            is_change = true;
                        }
                    }
                }
            }
            return is_change;
        }
    };
}

char bso_cp::ID = 0;
static RegisterPass<bso_cp> Y("bso_cp", "BSO: Simple Constant Propagation");
