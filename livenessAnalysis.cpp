#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.def"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include <set>
#include <vector>
#include <map>

using namespace llvm;

// how does phi node come into play in liveness analysis

namespace{
    struct bso_liveness_analysis : public FunctionPass{
        static char ID;
        bso_liveness_analysis() : FunctionPass(ID) {};

        std::map<BasicBlock*, std::vector<bool> > in;      // in[B]
        std::map<BasicBlock*, std::vector<bool> > out;     // out[B]
        std::map<Value*, int> value_mapper;     // maps a value to the index on in the bit vector        

        struct bb_info{
            BasicBlock* BB;
            std::vector<bool> uses;
            std::vector<bool> defs;
        };

        std::map<BasicBlock*, bb_info*> bb_info_map;
       
        void getAnalysisUsage(AnalysisUsage &AU) const{
            AU.addRequiredID(InstructionNamerID);   // force temporary variables to have a name
        }

        // meet vectors in mymap referenced by BB in bb_set, returns the bitset of the meet operation 
        // in liveness analysis, the meet operator is the union
        std::vector<bool> meet (std::vector<BasicBlock*> bb_set, 
                                std::map<BasicBlock*, std::vector<bool> > mymap){

            std::vector<bool> res;
            if (bb_set.size() == 0) return res;

            for (unsigned i = 0 ; i < bb_set.size(); i++){
                if (mymap[bb_set[i]].size() != 0){
                    if (res.size() == 0){                   // if res is not set yet
                        res = mymap[bb_set[i]];             // set res to be the boolean vector
                    }else{                                  // else
                        for (unsigned j = 0 ; j < res.size(); j++){
                            res[j] = res[j] || mymap[bb_set[i]][j];  // perform the union operation
                        }
                    }
                }
            }
            return res;
        }       
 
        // iterative transfer function that transforms in[B] to out[B]
        std::vector<bool> xfer_fn(BasicBlock* B, std::vector<bool> x){
            std::vector<bool> res, propagated_vars;
            bb_info* curr_bb_info = bb_info_map[B];
            res  = curr_bb_info->uses;
            propagated_vars = x;
            
            for (unsigned i = 0 ; i < x.size(); i++){
                // remove all the propagated variables that are redefined in the basic blocks
                if (curr_bb_info->defs[i] == true){
                    propagated_vars[i] = false;
                }
                // compute the union between the used variables and the propagated variables
                res[i] = res[i] || propagated_vars[i];
            }
            return res;
        }

        void printBitVector(std::vector<bool> v){
            for (unsigned i = 0 ; i < v.size(); i++){
                if (v[i]){
                    errs() << "1";
                }else{
                    errs() <<  "0";
                }
            }
        }

        void printUseDefs(){
            for (std::map<BasicBlock*, bb_info*>::iterator it2 = bb_info_map.begin();
                it2 != bb_info_map.end(); ++it2){
                errs() << "--------------------------------\n";
                errs() <<  it2->first->getName() << "\n";
                errs() << "Use : ";
                printBitVector(it2->second->uses);
                errs() << "\n";
                errs() << "Def : " ;
                printBitVector(it2->second->defs);
                errs() << "\n";
                errs() << "--------------------------------\n";
            } 
        }

        bool runOnFunction(Function &F) override{
            int num_var_counter = 0;
            bool isChange = true;
            std::vector<bool> temp_out, temp_in;
            std::vector<BasicBlock*> s_list;
            
            // determine variables in the function 
            for (BasicBlock &BB : F){
                for (BasicBlock::iterator DI = BB.begin(); DI != BB.end(); ){
                    Instruction *I = &(*DI++);
                    // put the value in the mapper
                    Value *v = dyn_cast<Value>(I);
                    if(!(I->isTerminator()) and (I->getOpcode() != Instruction::Store)
                        and (value_mapper.find(v) == value_mapper.end())){
                        // if not a terminating IR, put the value in the mapper
                        value_mapper[v] = num_var_counter;
                        num_var_counter++;
                    }

                    for (unsigned i = 0 ; i < I->getNumOperands(); i++){
                        v = I->getOperand(i);
                        if (!(dyn_cast<Constant>(v)) and !(v->getType()->isLabelTy()
                                                    or v->getType()->isVoidTy())){
                            if(value_mapper.find(v) == value_mapper.end()){
                                value_mapper[v] =num_var_counter;
                                num_var_counter++;
                            }
                        }
                    }
                    // if it is not a branching instruction
                    // get the operands and put it in the value mapper
                
                }
            }

            // fill in bb_info
            for (Function::iterator b = F.begin(); b != F.end(); b++){
                BasicBlock* BB = &(*b);
                bb_info*  curr_bb_info = new bb_info;
                curr_bb_info->BB = BB;
                in[BB] = {};
                out[BB] = {};
                for (int i = 0 ; i < num_var_counter; i++){
                    curr_bb_info->uses.push_back(false);
                    curr_bb_info->defs.push_back(false);
                }
                for (BasicBlock::iterator DI = BB->begin(); DI != BB->end(); ){
                    Instruction *I = &(*DI++);
                    Value *v = dyn_cast<Value>(I);
                    // fill in bit vector where a certain value is defined
                    if (!(I->isTerminator()) and (I->getOpcode() != Instruction::Store)){
                        curr_bb_info->defs[value_mapper[v]] = true;
                    }   
                    // fill in bit vector where a certain value is used
                    for (unsigned i = 0; i < I->getNumOperands(); i++){
                        v =I->getOperand(i);
                        if (!(dyn_cast<Constant>(v)) and !(v->getType()->isLabelTy()
                                                    or v->getType()->isVoidTy())){
                            // if the variable is not defined in the same basic block
                            // set def to be use
                            if (curr_bb_info->defs[value_mapper[v]] == false){
                                curr_bb_info->uses[value_mapper[v]] = true;
                            }
                        }

                    }
                }
                bb_info_map[BB] = curr_bb_info;
            }

            errs() <<  "location of bits for each variable used" << "\n";
            for (std::map<Value*, int>::iterator it = value_mapper.begin(); it != value_mapper.end(); ++it){
                errs() << it->first->getName() << " => " << it->second << "\n" ;
            }
            errs() << "Number of variables: " << num_var_counter << "\n";
            printUseDefs();

            while (isChange){
                isChange = false;
                for (Function::iterator b = F.begin(); b != F.end(); b++){
                    
                    BasicBlock* BB = &(*b);
                    s_list.clear();
                    for (unsigned i = 0 ; i < BB->getTerminator()->getNumSuccessors(); i++){
                        s_list.push_back(BB->getTerminator()->getSuccessor(i));
                    }
                    
                    temp_out = meet(s_list, in);
                    
                    temp_in = xfer_fn(BB,temp_out);
                    // check whether out[BB] and in[BB] has changed
                    if (temp_out.size() != out[BB].size() or temp_in.size() != in[BB].size()){
                        isChange = true;
                    }else{
                        for (unsigned i = 0 ;i < temp_out.size(); i++){
                            if (temp_out[i] != out[BB][i]){
                                isChange = true;
                                break;
                            }
                        }
                    
                        for (unsigned i = 0 ; i < temp_in.size(); i++){
                            if (temp_in[i] != in[BB][i]){
                                isChange = true;
                                break;
                            }
                        }
                    }
                    out[BB] = temp_out;
                    in[BB] = temp_in;
                }
            }

            // print out liveness analysis result
            for (Function::iterator b = F.begin(); b != F.end(); b++){
                BasicBlock* BB = &(*b);
                errs() << "BasicBlock : " << BB->getName() << "\n";
                errs() <<  "in: ";
                printBitVector(in[BB]);
                errs() <<  "\nout: ";
                printBitVector(out[BB]);
                errs() << "\n";
            }

            return false;
        }
    };
}

char bso_liveness_analysis::ID = 0;
static RegisterPass<bso_liveness_analysis> C("bso_liveness_analysis", "BSO : Iterative Algorithm for liveness analysis");
