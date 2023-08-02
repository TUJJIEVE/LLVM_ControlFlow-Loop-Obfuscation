#include "llvm/Pass.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Value.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Casting.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Type.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/Transforms/Scalar/Reg2Mem.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/ValueHandle.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "llvm/IR/User.h"
#include "llvm/Analysis/MemorySSAUpdater.h"
#include <random>
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/CFG.h"
#include <map>
#include <cstdlib>
#include <utility>
#include <string>
#include <algorithm>
using namespace llvm;

namespace{
    struct BFlattening : public FunctionPass{
        static char ID ;
        BFlattening():FunctionPass(ID){} 
       
        Instruction * insertAllocaInPreHeader(Function * F , BasicBlock * pB , BasicBlock * B) {
            auto * terminatorPB = pB->getTerminator() ;
//            auto  Ctx = F->getContext() ;
            Instruction * allocaI = new AllocaInst(Type::getInt32Ty(F->getContext()),0,Twine(B->getName()),terminatorPB);
            Instruction * storeI = new StoreInst(llvm::ConstantInt::get(llvm::Type::getInt32Ty(F->getContext()),2),llvm::cast<llvm::Value>(allocaI),terminatorPB);
            return allocaI ;
        } 
        void  createLoop(Function * F , BasicBlock * pB , BasicBlock *B , Instruction * alloc){
                BasicBlock * leftB = (B->getTerminator())->getSuccessor(0)  ;
                BasicBlock * rightB = (B->getTerminator())->getSuccessor(1) ;
                BasicBlock * endB = (leftB->getTerminator())->getSuccessor(0) ;
                //---------------
                //create nessary basic blocks 
                //auto Ctx = F->getContext() ;
                dbgs() << "entered to create basic blocks\n";
                BasicBlock * header = BasicBlock::Create( F->getContext(),Twine("header"+B->getName()),B->getParent()) ; //Twine: B->getName() + "header" !debug
                BasicBlock * switchdef = BasicBlock::Create( F->getContext(),Twine("switchdef"+B->getName()),B->getParent())  ;
                BasicBlock * latch = BasicBlock::Create( F->getContext(),Twine("inc"+B->getName()),B->getParent())   ; 
                dbgs() << "created basic blocks\n";
                //---------------
                //add instructions in header
                auto * terminatorPB = pB->getTerminator() ;
                if(terminatorPB->getSuccessor(0) == B) terminatorPB->setSuccessor(0,header) ; //sets preblock successor to new header
                else terminatorPB->setSuccessor(1,header) ;
                dbgs() << "replaced basic block in preHeader : all preheder changes done\n" << *pB << "\n"; 
                Instruction * loadI = new LoadInst((Value *)(alloc),Twine("header"+B->getName()),header); //inserts at the end of basicblock
                dbgs() << "created load instruction in header\n";
                auto * switchI  = SwitchInst::Create((Value *)(loadI),switchdef,0,header);      //inserts switch with 0 cases at end of header
                dbgs() << "created switch instruction in header\n";
                switchI->addCase(ConstantInt::get(IntegerType::get(F->getContext(), 32),2,false),B);
                switchI->addCase(ConstantInt::get(IntegerType::get(F->getContext() , 32),1,false),leftB);
                switchI->addCase(ConstantInt::get(IntegerType::get(F->getContext() , 32),0,false),rightB);
                switchI->addCase(ConstantInt::get(IntegerType::get(F->getContext(), 32),3,false),endB);
                dbgs() <<"all changes to header are finished\n" << *header << "\n" ;
                //----------------
                //modify instructions in B block
                BranchInst * branchinstB = dyn_cast<BranchInst>(B->getTerminator()) ; //terminator of branch Instruction
                Value * conditionV = branchinstB->getCondition() ; 
                Instruction * zextI = new ZExtInst(conditionV,IntegerType::get(F->getContext(), 32),Twine("condition"),B);
                Instruction * storeInB = new StoreInst((Value *)zextI ,(Value *)(alloc) , B );
                dbgs() << "created a new store inst in B block which changes value to conditionV\n";
                branchinstB->eraseFromParent() ;
                BranchInst::Create(latch,B);           
                dbgs() << "all changes to B block has been made\n" << *B << "\n" ;
                //-----------------
                //modify instructions in leftB
                BranchInst * branchinstLeftB = dyn_cast<BranchInst>(leftB->getTerminator()); 
                Instruction * storeInleftB = new StoreInst(llvm::ConstantInt::get(llvm::Type::getInt32Ty(F->getContext()),3),(Value *)(alloc),branchinstLeftB);
                dbgs() << "inserted store inst in leftB to 3\n";
                    branchinstLeftB->eraseFromParent();
                BranchInst::Create(latch,leftB);           
                dbgs() << "all changes are made to left \n" << *leftB << "\n";
                //-----------------
                //modify instructions in rightB
                BranchInst * branchinstRightB = dyn_cast<BranchInst>(rightB->getTerminator()); 
                Instruction * storeInrightB = new StoreInst(llvm::ConstantInt::get(llvm::Type::getInt32Ty(F->getContext()),3),(Value *)(alloc),branchinstRightB);
                branchinstRightB->eraseFromParent();
                BranchInst::Create(latch,rightB);           
                //-----------------
                //modify instructions in latch 
                BranchInst::Create(header,latch);
                //----------------
                //modify instructions in switchdef
                BranchInst::Create(latch,switchdef);
                //-----------------
                //finished all modifications 
            
        }
        bool runOnBranchBB(Function * F , BasicBlock * b){
            BasicBlock * preHeader = b->getUniquePredecessor() ;
            if(preHeader){ 
                    Instruction * allocaI = insertAllocaInPreHeader(F ,preHeader , b); //inserts alloca and stores 0 in in it
                    dbgs() << "completed creating alloca instruction\n";
                    createLoop(F ,preHeader,b,allocaI);
            }
            return false;
        }


        bool runOnFunction(Function &F) { //override {

            //detect basicblocks with conditional branches and same end block and store in blist   
            SmallVector <BasicBlock *,5> blist ;
            detectBBwithSameTerminator(&F,&blist) ;
            for(BasicBlock* b : blist){
                dbgs() <<"printing in blist\n" << *b << "finished printing in blist\n" ;

                runOnBranchBB(&F, b);
                
            }
                    
    
            return false;
        }

        void detectBBwithSameTerminator(Function * F,SmallVector<BasicBlock * , 5> *blist){
            for(Function::iterator b = F->begin() , be = F->end() ; b != be ; ++b){
                BasicBlock * BB = &(*b) ;
               // Instruction * terminatorI = BB->getTerminator() ;
                dbgs() << "checking this label" << BB->getName() << "\n" ;
                if(auto * terminatorI = dyn_cast<BranchInst>(BB->getTerminator())){
                    if(terminatorI->isConditional()){
                        dbgs() << "basic block has conditional branching\n" ;
                        BasicBlock * left = terminatorI->getSuccessor(0) ;
                        BasicBlock * right = terminatorI->getSuccessor(1) ;
                        BranchInst * leftBBTerminator =  dyn_cast<BranchInst>(left->getTerminator()) ;  
                        BranchInst * rightBBTerminator = dyn_cast<BranchInst>(right->getTerminator()) ;
                        if( leftBBTerminator && rightBBTerminator ){
                            dbgs() << "left and right blocks has branchinst\n" ;
                            if(leftBBTerminator->isUnconditional() && rightBBTerminator->isUnconditional()){
                                dbgs() << "both left and right are unconditional\n";
                               if(leftBBTerminator->getSuccessor(0) == rightBBTerminator->getSuccessor(0)){
                                        //push BB to blist
                                        dbgs() <<"adding to Blist\n";            
                                        blist->push_back(BB);
                                 }
                            }
                        }
                    }
                }        
            }
        }
        
    };  
}

char BFlattening::ID = '1' ;
static RegisterPass<BFlattening> Hi("bflatten","unconditional branch flattening");

static void registerMyPass(const PassManagerBuilder &, legacy::PassManagerBase &PM){
	PM.add(new BFlattening());
}
static RegisterStandardPasses RegisterMyPass ( PassManagerBuilder::EP_EarlyAsPossible,registerMyPass);

