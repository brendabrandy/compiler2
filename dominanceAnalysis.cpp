// Name : Brenda So
// Date : 11/3/2017
// Goal : Perform dominance analysis on each basic block, printing out, for each BB :
// dominators, immediate dominator, inverse dominators, and strict dominators

#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h"
#include <vector>
#include <map>

using namespace llvm;

namespace{
    struct bso_dominance_analysis : public FunctionPass{
        static char ID;
        bso_dominance_analysis() : FunctionPass(ID) {};
        
        struct bb_info{
            BasicBlock* BB;
            std::vector<bool> dominators;
            std::vector<bool> strict_dominators;
            std::vector<bool> immediate_dominators;
            std::vector<bool> inverse_dominators; 
        };

        std::map<BasicBlock*, int> value_mapper;    // maps BB to location on bit vector
        std::map<BasicBlock*, bb_info*> bb_info_mapper;
        
        // utility to check whether two boolean vectors are equal
        bool isEqual(std::vector<bool> a, std::vector<bool> b){
            if (a.size() != b.size()) return false;
            for (unsigned i = 0 ; i < a.size(); i++){
                if (a[i] != b[i]) return false;
            }
            return true;
        }

        
        // utility to implement meet operation in dominance analysis, which is 
        // intersection of dominator list
        std::vector<bool> meet(std::vector<BasicBlock*> bb_list){
            std::vector<bool> ret;
            if (bb_list.size() == 0) return ret;
            for (unsigned i = 0; i <  bb_list.size(); i++){
                if (i == 0){
                    ret = bb_info_mapper[bb_list[i]]->dominators;
                }else{
                    for (unsigned j = 0 ; j < bb_info_mapper[bb_list[i]]->dominators.size(); j++){
                        if (!(ret[j] == true and bb_info_mapper[bb_list[i]]->dominators[j] == true)){
                            ret[j] = false;
                        }
                    }
                }
            }
            return ret;
        }

        // utility to perform union between Basic block and the dominator list
        std::vector<bool> un(BasicBlock* BB, std::vector<bool> p_list){
            p_list[value_mapper[BB]] = true;
            return p_list;
        }

        void printBitVector(std::vector<bool> b){
            for (unsigned i = 0 ; i < b.size(); i++){
                if (b[i] == false){
                    errs() << "0";
                }else{
                    errs() << "1";
                }
            }

        }

        void printResult(BasicBlock* BB){
            errs() << "BasicBlock : " << BB->getName() << "\n";
            errs() << "Dominators: ";
            printBitVector(bb_info_mapper[BB]->dominators);
            errs() << "\n";
            errs() <<  "Strict Dominators: ";
            printBitVector(bb_info_mapper[BB]->strict_dominators);
            errs() << "\n";
            errs() <<  "Inverse Dominators: ";
            printBitVector(bb_info_mapper[BB]->inverse_dominators);
            errs() << "\n";
            errs() <<  "Immediate Dominators: ";
            printBitVector(bb_info_mapper[BB]->immediate_dominators);
            errs() << "\n";

        }
        
        bool runOnFunction(Function &F) override{

            unsigned counter;
            bool isChanged, isImmDom;
            std::vector<bool> new_dom;
            std::vector<BasicBlock*> p_list;
            std::vector<bool> p_i;  // boolean to keep track of intersection of predecessors
            counter = 0;
            isChanged = true;

            // setup value_mapper
            for (Function::iterator b = F.begin(); b != F.end(); b++){
                BasicBlock* BB = &(*b);

                if (value_mapper.find(BB) == value_mapper.end()){
                    value_mapper[BB] = counter;
                    bb_info_mapper[BB] = new bb_info;
                    counter++;
                }
                
            }

            // initialize the dominator set 
            for (Function::iterator b = F.begin(); b != F.end(); b++){
                BasicBlock *BB = &(*b);
                // set dom(BB) = whole set of basic blocks
                for (unsigned i = 0 ; i< counter; i++){
                    bb_info_mapper[BB]->dominators.push_back(true);
                    bb_info_mapper[BB]->inverse_dominators.push_back(false);
                    bb_info_mapper[BB]->immediate_dominators.push_back(false);
                }
                if (BB == &(F.getEntryBlock())){
                    // set dom(entry) = entry only
                    for (unsigned i = 0  ; i < counter; i++){
                        if (i != value_mapper[BB]){
                            bb_info_mapper[BB]->dominators[i] = false;
                        }
                    }
                }
            }

            // go through the algorithm for finding dominators
            while (isChanged){
                isChanged = false;
                for (Function::iterator b = F.begin(); b != F.end(); b++){
                    BasicBlock *BB = &(*b);
                    // for every block except the entry block
                    if (BB != &(F.getEntryBlock())){
                        bb_info_mapper[BB]->dominators;
                        // find the intersection of BB of dominators of predecessors
                        p_list.clear();
                        for (BasicBlock* predecessor : predecessors(BB)){
                            p_list.push_back(predecessor);
                        }
                        p_i = meet(p_list);
                        new_dom = un(BB, p_i);
                        if (!isEqual(new_dom, bb_info_mapper[BB]->dominators)){
                            bb_info_mapper[BB]->dominators = new_dom;
                            isChanged = true;
                        }
                    }
                }
            }

            // find strict dominators
            for (Function::iterator b = F.begin(); b != F.end(); b++){
                BasicBlock *BB = &(*b);
                bb_info_mapper[BB]->strict_dominators = bb_info_mapper[BB]->dominators;
                bb_info_mapper[BB]->strict_dominators[value_mapper[BB]] = false;
            }

            // find immediate dominators
            // the definition of immediate dominators is that it is the closest dominator to d
            // meaning that other dominators that dominate d also dominate the immediate dominator
            // it is proven that every block has a unique immediate dominator
            for (Function::iterator b = F.begin(); b !=  F.end(); b ++){
                BasicBlock *BB = &(*b);
                // loop through strict dominators
                if (BB != &(F.getEntryBlock())){
                    p_list.clear();     // use this list to save dominators
                    
                    for (Function::iterator b2 =F.begin(); b2 != F.end(); b2++){
                        BasicBlock *BB2 = &(*b2);
                        if (bb_info_mapper[BB]->strict_dominators[value_mapper[BB2]] == true){
                            p_list.push_back(BB2);
                        }
                    }
                    
                    for (unsigned i = 0 ; i < p_list.size(); i++){
                        isImmDom = true;
                        for (unsigned j = 0 ; j < p_list.size(); j++){
                            if (i != j){
                                // check whether p_list[j] is a strict dominator of p_list[i]
                                if (bb_info_mapper[p_list[i]]->
                                    strict_dominators[value_mapper[p_list[j]]] != true){
                                // if not, then p_list[i] is not an immediate dominator of BB
                                    isImmDom = false;
                                    break;
                                }
                            }
                        }
                        if (isImmDom){
                            bb_info_mapper[BB]->immediate_dominators[value_mapper[p_list[i]]] = true;
                            break;
                        }
                    }
                }
            }

            // find inverse dominators
            for (Function::iterator b = F.begin(); b != F.end(); b++){
                BasicBlock *curr_bb = &(*b);
                for (Function::iterator b2 = F.begin(); b2 != F.end(); b2++){
                    BasicBlock *other_bb = &(*b);
                    if (bb_info_mapper[other_bb]->dominators[value_mapper[curr_bb]] == true){
                        bb_info_mapper[curr_bb]->inverse_dominators[value_mapper[other_bb]] = true;
                    }
                }
            }

            // print out result
            for (Function::iterator b = F.begin(); b != F.end(); b++){
                BasicBlock *BB = &(*b);
                printResult(BB);
            }

            return false;
        }
    };
}


char bso_dominance_analysis::ID = 0;
static RegisterPass<bso_dominance_analysis> D("bso_dominance_analysis","BSO: Iterative Algorithm for Dominance Analysis");
