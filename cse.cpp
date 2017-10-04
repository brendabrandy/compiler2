#include"llvm/ADT/Statistic.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

#define DEBUG_TYPE "bso_cse"
STATISTIC(NumXForms, "# of instructions deleted");

namespace{
struct bso_cse : public BasicBlockPass{
    
    static char ID;
    bso_cse() : BasicBlockPass(ID) {};
    
    // A building block for available instructions
    struct AEB{
        int pos;
        int opcode;
        Value * op1;
        Value * op2;
        Value * tmp;
        AEB* next;
    };

    
    // This function matches an expression  with an instruction
    // match op1, opcode and op2 between a and inst
    bool match(AEB* a, int opcode, Value * lhs, Value * rhs){
        if (a->opcode == opcode and lhs == a->op1 and rhs == a->op2){
            return true;
        }
        return false;
    }
    
    // print AEB out for debugging purposes
    void printAEB(AEB* head){
        
        AEB* curr;
        
        curr = head;
        while(curr != NULL){
            errs() << "Counter: " << curr->pos << "\n";
            errs() << "opcode: " << curr->opcode << "\n";   
            errs() << "op1: " << curr->op1->getName() << "\n";
            errs() << "op2: " << curr->op2->getName() <<  "\n";
            errs() << "tmp: " << curr->tmp->getName() << "\n";
            errs() << "--------------------------------------\n";
            curr = curr->next;
        }
    }

    bool runOnBasicBlock(BasicBlock &BB) override{
        // errs() <<  "In Basic Block!\n"; 
        int counter;
        bool no_match, is_change;
        AEB *head, *curr, *temp, *match_aeb;

        int opcode;
        Value *lhs, *rhs, *tmp_val;

        counter = 0;
        no_match = true;
        is_change = false;
        head = NULL;

        // for every instruction in basic block
        for (BasicBlock::iterator DI = BB.begin(); DI != BB.end(); ){
            Instruction* I = &(*DI++);
            if(auto* op = dyn_cast<BinaryOperator>(I)){
                IRBuilder<> builder(op);
                curr = head;
                opcode = op->getOpcode();   
                lhs = op->getOperand(0);
                rhs = op->getOperand(1);
                no_match = true;

                // for every available expression in AEB chain
                while (curr != NULL){
                    // match op1, opcode and op2 between the AEB and the inst
                    if (match(curr, opcode, lhs, rhs)){
                        no_match = false;
                        match_aeb = curr;
                        break;
                    }
                    if (op->isCommutative()){
                        // if inst is commutative, commute the operands and match again
                        if (match(curr, opcode, rhs, lhs)){
                            no_match = false;
                            match_aeb = curr;
                            break;
                        }
                    }
                    curr = curr->next;
                }

                // if noMatch is true
                if (no_match){
                    // insert another AEB
                    temp = new AEB;
                    temp->pos = counter;
                    temp->opcode = opcode;
                    temp->op1 = lhs;
                    temp->op2 = rhs;
                    temp->tmp = dyn_cast<Value>(I);
                    temp->next = NULL;
                    curr = head;
                    if (head == NULL){
                        head = temp;
                    }else{
                        while (curr->next != NULL){
                            curr = curr->next;
                        }
                        curr->next = temp;
                    }
                }else{
                    // if noMatch is false
                    // replace all uses with the temp value in AEB
                    I->replaceAllUsesWith(match_aeb->tmp);  // HAVE TO CHECK THIS!
                    // remove the instruction
                    I->eraseFromParent();
                    ++NumXForms;
                    is_change = true;
                }

                curr = head;
                tmp_val = dyn_cast<Value>(I);
                // go through AEB with the assigned value
                while(curr != NULL){
                    // if operand 1 or operand 2 is the same value as the assigne value, 
                    // remove that specific expression
                    if (curr->op1 == tmp_val or curr->op2 == tmp_val){
                        temp = curr->next;
                        curr = temp->next;
                        free(temp);
                    }
                    curr = curr->next;
                }

            }
            counter ++;
        }
        // printAEB(head);
        
        return is_change;
    }

};

    

}



char bso_cse::ID = 0;
static RegisterPass<bso_cse> X("bso_cse", "BSO : Common Subexpression Elimination");
