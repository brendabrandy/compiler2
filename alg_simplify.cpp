#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instruction.def"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

namespace{
    struct bso_alg_simplify : public BasicBlockPass{
        static char ID;
        bso_alg_simplify() : BasicBlockPass(ID){};

        // check whether val is a power of two
        // if not, return 0
        // else, return n, where val = 2^n
        int isTwoPower(int val){
            int tempval;
            int counter = 0;
            while (val > 0){
                tempval = val % 2;
                val = val / 2;
                if (tempval == 1){
                    return 0;
                }else{
                    counter++;
                }
            }
            return counter;
        }

        bool runOnBasicBlock(BasicBlock &BB) override{
            int temp;
            int constant_val;
            bool isChange = false;
            for (BasicBlock::iterator DI = BB.begin(); DI != BB.end(); ){
                Instruction *I = &(*DI++);
                ConstantInt *C1;
                if ((C1 = dyn_cast<ConstantInt>(I->getOperand(1)))){
                    temp = 1;
                }else if ((C1 = dyn_cast<ConstantInt>(I->getOperand(0)))){
                    temp = 0;
                }else{
                    continue;
                }   
                if (I->getOpcode() == Instruction::Add){
                    // i + 0 = i, 0 + i = i
                    if (C1->isZero()){
                        temp = (temp == 1) ? 0 : 1;     // address the non-zero operand
                        I->replaceAllUsesWith(I->getOperand(temp));
                        I->eraseFromParent();
                        isChange = true;
                    }
                }else if (I->getOpcode() == Instruction::Sub){
                    // i - 0 = i
                    if (C1->isZero()){
                        temp = (temp == 1) ? 0 : 1;
                        if (temp == 1){
                            I->replaceAllUsesWith(I->getOperand(temp));
                            I->eraseFromParent();
                            isChange = true;
                        }
                    }
                }else if (I->getOpcode() == Instruction::Mul){
                    // 1 * i = i, i * 1 = i, i * 0 = 0, 0 * i = 0
                    if(C1->isZero()){
                        I->replaceAllUsesWith(I->getOperand(temp));
                        isChange = true;
                    }else if (C1->isOne()){
                        temp = (temp == 1)? 0 : 1;
                        I->replaceAllUsesWith(I->getOperand(temp));
                        I->eraseFromParent();
                        isChange = true;
                    }else{
                        // check whether it is a power of two
                        constant_val = isTwoPower(C1->getSExtValue());
                        IRBuilder<> Builder(I);
                        Value* new_val = ConstantInt::get(C1->getType(), constant_val);
                        auto *new_inst = Builder.CreateShl(I->getOperand(0), new_val);
                        I->replaceAllUsesWith(new_inst);
                        I->removeFromParent();
                        isChange = true;
                    }
                }else if (I->getOpcode() == Instruction::SDiv){
                    // i / 1 = i
                    if (temp == 1){
                        if (C1->isOne()){
                            I->replaceAllUsesWith(I->getOperand(0));
                            I->eraseFromParent();
                            isChange = true;
                        }
                    }
                    
                }
            }
            return isChange;
        }
    };
}

char bso_alg_simplify::ID = 0;
static RegisterPass<bso_alg_simplify> B("bso_alg_simplify", "BSO: Algebraic Simplification");
