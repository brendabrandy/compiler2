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

        bool runOnBasicBlock(BasicBlock &BB) override{
            int temp;
            bool isChange = false;
            for (BasicBlock::iterator DI = BB.begin(); DI != BB.end(); ){
                Instruction *I = &(*DI++);
                ConstantInt *C1, *C2;
                if ((dyn_cast<ConstantInt>(I->getOperand(1)))){
                    temp = 1;
                }else if ((dyn_cast<ConstantInt>(I->getOperand(0)))){
                    temp = 0;
                }else{
                    continue;
                }   
                if (I->getOpcode() == Instruction::Add){
                    // i + 0 = i, 0 + i = i
                    C1 = dyn_cast<ConstantInt>(I->getOperand(temp));
                    if (C1->isZero()){
                        temp = (temp == 1) ? 0 : 1;     // address the non-zero operand
                        I->replaceAllUsesWith(I->getOperand(temp));
                        I->eraseFromParent();
                        isChange = true;
                    }
                }else if (I->getOpcode() == Instruction::Sub){
                    // i - 0 = i
                    C1 = dyn_cast<ConstantInt>(I->getOperand(temp));
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
                    C1 = dyn_cast<ConstantInt>(I->getOperand(temp));
                    if(C1->isZero()){
                        I->replaceAllUsesWith(I->getOperand(temp));
                        isChange = true;
                    }else if (C1->isOne()){
                        temp = (temp == 1)? 0 : 1;
                        I->replaceAllUsesWith(I->getOperand(temp));
                        I->eraseFromParent();
                        isChange = true;
                    }
                }else if (I->getOpcode() == Instruction::SDiv){
                    // i / 1 = i
                    if (temp == 1){
                        C1 = dyn_cast<ConstantInt>(I->getOperand(temp));
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
