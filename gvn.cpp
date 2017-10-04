#include "llvm/Pass.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.def"
using namespace llvm;

#define DEBUG_TYPE "bso_gvn"
STATISTIC(NumXForms, "# of instructions deleted");

namespace{
    struct bso_gvn : public FunctionPass{
        static char ID;
        bso_gvn() : FunctionPass(ID) {};

        bool runOnFunction(Function &F) override{
            // build value graph for SSA
            // Initialize the work list
            // compute congruence of variables
            // for variables that are in the same congruence
            // we can delete that variable and replace all uses with the other variable

            return is_change;
        }
    };
}

char bso_cp::ID = 0;
static RegisterPass<bso_gvn> Y("bso_gvn", "BSO: Global Value Numbering");
