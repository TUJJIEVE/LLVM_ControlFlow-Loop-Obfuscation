    #include "llvm/Pass.h"
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

	/// Transformation pass to obfucate the loop by adding switch, and pre blocks to latch, body and end block
	/// The pass uses LoopInforWrapper pass for getting the loop information
    namespace{

        struct Flattening : public FunctionPass{

            static char ID;
            static bool hi;
            Flattening():FunctionPass(ID){}
            void getAnalysisUsage(AnalysisUsage &AU) const{
                AU.addRequired<LoopInfoWrapperPass>();
                AU.addRequired<DominatorTreeWrapperPass>();
            }
		/// Creates the swtich block needed for the transformation
		static BasicBlock * createSwitchBlock(Function * F,SmallVector<Value *,5> randInstructions ,SmallVector<BasicBlock * , 10> Blocks,
												 BasicBlock * HB,Instruction * randomAlloca){

			assert(F && "function ptr cant be nullptr");
			assert(HB && "headder cant be nullptr");
			 BasicBlock * BB = BasicBlock::Create(F->getContext(),"Switch",F);
			unsigned i = rand()%(Blocks.size() +1);
			BasicBlock * defBlock;
			/// To calculate the default block done at compile time
			if (i==Blocks.size()) defBlock=HB;
			else {
				defBlock = Blocks[i];
				// To handle the case where if a phi node present in the default block 
				for (Instruction &I : *defBlock){
					if (auto * phi = dyn_cast<PHINode>(&I)){
						Type * phiType = ((Value*)&I)->getType(); 
							// Add a default value 
							if (phiType->isAggregateType()) phi->addIncoming( ConstantAggregateZero::get(phiType),BB);
                            else if(phiType->isPointerTy()) phi->addIncoming(ConstantPointerNull::get((PointerType * )phiType),BB);
							else phi->addIncoming( Constant::getAllOnesValue(phiType),BB);

						
					}
				}

			}
			// Function to create the switch instructions
			createSwitchInst(F,defBlock,randInstructions,Blocks,HB,randomAlloca,BB);
			return BB;
		}
		/// Function to create switch instruction 
		static void createSwitchInst(Function * F,BasicBlock * defBlock,SmallVector<Value *,5> randInstructions,
										SmallVector<BasicBlock * , 10> Blocks , BasicBlock * HB,Instruction * randomAlloca,BasicBlock* BB){
			
			randInstructions.push_back((Value *) BinaryOperator::Create(Instruction::SRem,randInstructions[randInstructions.size()-1],(Value *)ConstantInt::get(IntegerType::get(F->getContext(),32),Blocks.size()+1,false),"randomNumber"));			
			// Insert the instructions needed to generate the random jump 
			for (unsigned i=0;i<randInstructions.size();i++){
				BB->getInstList().push_back((Instruction *) randInstructions[i]);
			}
			// Creating the store instruction to store the random value generated in the location randomAlloca
			Instruction * storeInst = new StoreInst(randInstructions[randInstructions.size()-1],randomAlloca);
			BB->getInstList().push_back(storeInst);
			SwitchInst * SW = SwitchInst::Create(randInstructions[4],defBlock,4,BB);
			// Used in the case statments
			SmallVector<ConstantInt * , 5> constants;
			for (unsigned i=0;i<=Blocks.size();i++){
				constants.push_back(ConstantInt::get( IntegerType::get(F->getContext() , 32) ,i , false));
			}
			SW->addCase(constants[0],HB);
			for (unsigned i=0;i<Blocks.size();i++){
				SW->addCase(constants[i+1],Blocks[i]);
		
			}


		}
		/// Function to create pre Blocks
		static BasicBlock * createPreBlock(Function * F , int key , BasicBlock * label1 ,BasicBlock * label2 ,
											 SmallVector<BasicBlock*,10> &prevBlock ,Instruction * randomAlloca){
									
			BasicBlock * preBlock = BasicBlock::Create(F->getContext(),Twine(".pre"+label2->getName()),F) ;
			std::map<BasicBlock*,Value*> phiValues;
			Type * phiType;
			SmallVector<PHINode*,10> newPhiList;
			/// Loop to check to populate the newPhiList 
			/// Checks for presence of the phi nodes in the label2 block
			for (Instruction &I : *label2 ){
					if ( auto * ph = dyn_cast<PHINode>(&I)){
						dbgs() <<" The number of incoming Blocks are :" << ph->getNumIncomingValues() <<"\n";
						for (unsigned i = 0 ; i< ph->getNumIncomingValues();i++){
							phiValues.insert(std::make_pair(ph->getIncomingBlock(i),ph->getIncomingValue(i) ));
						}
							phiType = ((Value*)(&I))->getType();
							newPhiList.push_back(PHINode::Create(phiType,0));
							for (unsigned i=0;i<prevBlock.size();i++){
							newPhiList[newPhiList.size()-1]->addIncoming(phiValues.at(prevBlock[i]),prevBlock[i]);    
						} 
						phiValues.clear();                            
					}
			}
			// Loop to replace all the uses with the new phi node
			int count = 0;
			SmallVector<Instruction*,5> phiToErase;  /// vector to store the phi nodes to remove
			for (Instruction &I : *label2 ){
					if ( auto * ph = dyn_cast<PHINode>(&I)){
							for (auto uses: ph->users()){
							if (auto I = dyn_cast<Instruction>(uses)) I->dump();
							}
					((Instruction*)ph)->replaceAllUsesWith(newPhiList[count++]);
					phiToErase.push_back((Instruction*)ph);
				}
			}   
			// Loop to delete the old phi node
			for (unsigned i = 0 ; i<phiToErase.size();i++){
				phiToErase[i]->eraseFromParent();

			}
			/// For adding the load and compare instructions
			/// Load instruction to load the random number generated
			/// Compare Instruction to compare the random number with the number associated with the block
			Instruction * loadInst = new LoadInst((Value *)randomAlloca,"randmp"); 
			Value * V = Constant::getIntegerValue(Type::getInt32Ty(F->getContext()),APInt(32,key+1));
			Instruction * cmpInst = new ICmpInst(CmpInst::ICMP_EQ,V, loadInst);
			
			// Inserting the instructions in the block
			for (unsigned i = 0 ; i<newPhiList.size();i++){
				preBlock->getInstList().push_back(newPhiList[i]);
			}
			preBlock->getInstList().push_back(loadInst);
			preBlock->getInstList().push_back(cmpInst);
			preBlock->getInstList().push_back(BranchInst::Create(label1,label2,cmpInst)) ;
			return preBlock ;

	
		}
		/// Function to alter the branch instruction in the preHeader to jump to the Switch block
		static void AlterPreHeader(BasicBlock * preHeader, BasicBlock * switchBlock , BasicBlock * headerBlock){
			/// Setting the branch instruction of the preheader that is jumping to header to jump to Switch block instead
			if(auto * branch = dyn_cast<BranchInst>(preHeader->getTerminator())){
				if (branch -> isConditional()){
					if (branch->getSuccessor(0)== headerBlock){
						branch->setSuccessor(0,switchBlock);
					}
					if (branch->getSuccessor(1) == headerBlock){
						branch->setSuccessor(1,switchBlock);
					}
				}
				else if (branch->isUnconditional()){
					if (branch->getSuccessor(0)==headerBlock){
						branch->setSuccessor(0,switchBlock);
					}
				}
			}
		}
		/// Function to alter the branch instruction in the header or end block to jump to the preBlocks
		/// Only if the old branch is jumping to latch or first body block or endblock then the branch instruction is modified
		static void AlterHeaderOrEndBlock(BasicBlock * HeaderBlock ,SmallVector<BasicBlock * , 10> Body,
											BasicBlock * Latch, BasicBlock * endBlock,std::map<BasicBlock*,BasicBlock*>&newBlocksMap){

			if (auto * branch = dyn_cast<BranchInst>(HeaderBlock->getTerminator())){
				BasicBlock * succ1 = branch->getSuccessor(0);
				BasicBlock * succ2 = nullptr;
				if (branch->isConditional()){
					succ2 = branch->getSuccessor(1);
    			}
            	if ( (Body.size()>0 && succ1 == Body[0]) || succ1 == Latch || succ1 == endBlock){
						if (newBlocksMap.find(succ1)!=newBlocksMap.end())
							branch->setSuccessor(0,newBlocksMap.at(succ1));
				}
				if ( succ2 && ( (Body.size()>0 && succ2 == Body[0]) || succ2 == Latch || succ2 == endBlock )){
					branch -> setSuccessor(1,newBlocksMap.at(succ2));
				}

			}		
		}
		/// Function to alter the branch instructions in the body
		/// Only those branch instruction which are jumping to the latch or endblock or header block are modified
		static void AlterBody(SmallVector<BasicBlock * , 10> Body , BasicBlock * Latch ,Function * F,
								BasicBlock * HeaderBlock,BasicBlock* endBlock,std::map<BasicBlock*,BasicBlock*>&newBlocksMap){
	
			for (unsigned i=0;i<Body.size();i++){
                for (Instruction &I : *Body[i]){ 
                     if (BranchInst * branch = dyn_cast<BranchInst>(&I)){
				    	if(branch->isConditional()){
					    	BasicBlock * succ1 = branch->getSuccessor(0);
					    	BasicBlock * succ2 = branch->getSuccessor(1);
					    	if (succ1==HeaderBlock || succ1 == Latch || succ1 == endBlock){
					    		branch->setSuccessor(0, newBlocksMap.at(succ1));
					    	}
					    	if (succ2 == HeaderBlock || succ2 == Latch || succ2 == endBlock){
					    		branch->setSuccessor(1 , newBlocksMap.at(succ2));
					       	}
				    	}
					    else if  (branch->isUnconditional()){
					    	BasicBlock * succ1 = branch->getSuccessor(0);
					    	if (succ1 == HeaderBlock || succ1 == Latch || succ1 == endBlock){
						    	branch->setSuccessor(0,newBlocksMap.at(succ1));
						    }
					    }
				    }

			    }
            }
			
		}
		/// Function to prepare the random instructions that will be insrted int the switch blocks
		static void prepareRandInstructions(SmallVector<Value * , 5> &RandInstructions,Function * F){
			assert(F && "Function cant be null , missing function pointer");
            //inserting rand, time, srand functions in module
			Constant * randFunc = F->getParent()->getOrInsertFunction("rand",FunctionType::get(Type::getInt32Ty(F->getContext()),false));
			Constant * timeFunc = F->getParent()->getOrInsertFunction("time", FunctionType::get ( Type::getInt64Ty ( F->getContext() ) ,ArrayRef<Type*>( Type::getInt64PtrTy( F->getContext() ) ), false));
			Constant * srandFunc = F->getParent()->getOrInsertFunction("srand", FunctionType::get( Type::getVoidTy (F->getContext() ), ArrayRef<Type*>(Type::getInt32Ty(F->getContext())),false));
			//storing random number generator instructions
            RandInstructions.push_back((Value *) CallInst::Create( (Value *)timeFunc , ArrayRef<Value *>( (Value *)ConstantPointerNull::get(Type::getInt64PtrTy(F->getContext()))) ,"timeCall"));
			RandInstructions.push_back((Value *) new TruncInst((Value *) RandInstructions[0],Type::getInt32Ty(F->getContext()),"truncTime"));
			RandInstructions.push_back((Value *) CallInst::Create((Value *)srandFunc,ArrayRef<Value *>(RandInstructions[1])));
			RandInstructions.push_back((Value *) CallInst::Create((Value *)randFunc,ArrayRef<Value *>(),"randCall"));

			return;

		}
		/// Function to prepare the new blocks 
		
		static void prepareNewBlocks(Function * F, SmallVector<BasicBlock * , 10> &NewBlocks,BasicBlock * HeaderBlock, BasicBlock * Latch,
										BasicBlock * endBlock , SmallVector<BasicBlock *,10> Body,SmallVector<Value * , 5> &RandInstructions,
											std::map<BasicBlock*,BasicBlock*>&newBlocksMap,std::map<BasicBlock*,SmallVector<BasicBlock*,10> >&prevBlocksMap,
												Instruction * randomAlloca){

			assert(HeaderBlock && "missing headerblock");
			assert(F && "missing Function poiter , cant be null");
			int count = 0;
			// If body is present then create pre block for the body
			if(Body.size()>0) {
				NewBlocks.push_back(createPreBlock(F,count++,HeaderBlock,Body[0],prevBlocksMap.at(Body[0]),randomAlloca));
				newBlocksMap.insert(std::make_pair(Body[0],NewBlocks[count-1]));
			}
			// Two different cases not needed
			if(Latch && Body.size()>0) {
				NewBlocks.push_back(createPreBlock(F,count++,HeaderBlock,Latch,prevBlocksMap.at(Latch),randomAlloca));
				newBlocksMap.insert(std::make_pair(Latch,NewBlocks[count-1]));
			}
			
			if(Latch && Body.size()==0) {
				NewBlocks.push_back(createPreBlock(F,count++,HeaderBlock,Latch,prevBlocksMap.at(Latch),randomAlloca));
				newBlocksMap.insert(std::make_pair(Latch,NewBlocks[count-1]));
			}
			if(endBlock) {
				NewBlocks.push_back(createPreBlock(F,count++,HeaderBlock,endBlock,prevBlocksMap.at(endBlock),randomAlloca));
				newBlocksMap.insert(std::make_pair(endBlock,NewBlocks[count-1]));
			
			}
			/// Finally the switch block is inserted
			NewBlocks.push_back(createSwitchBlock(F,RandInstructions,NewBlocks,HeaderBlock,randomAlloca));
		
			return;

		}
		/// Processing the latch after transformation
		/// Altering the branch instruction of the latch
        static void postProcess(BasicBlock* Latch,BasicBlock* endBlock,SmallVector<BasicBlock*,10>& Body,std::map<BasicBlock*,BasicBlock*>&newBlocksMap){

           if ( BranchInst * latchBranch = dyn_cast<BranchInst>(Latch->getTerminator())){
                BasicBlock* succ1 = latchBranch->getSuccessor(0);
                BasicBlock* succ2 = nullptr;
                if (latchBranch->isConditional()) succ2 = latchBranch->getSuccessor(0);
                if (succ1 == Latch || succ1 == endBlock || (Body.size()>0 && succ1 == Body[0])) latchBranch->setSuccessor(0,newBlocksMap.at(succ1));
                if (succ2 != nullptr && ( succ2 == Latch || succ2 == endBlock || (Body.size()>0 && succ2 == Body[0]))) latchBranch->setSuccessor(1,newBlocksMap.at(succ2));

            }
            return ;

        }  
		/// Special case handled seperately 
		/// Case when only header block is present	
		static bool specialCaseHandle(SmallVector<Value*,5>&randInstructions,BasicBlock * preHeader,BasicBlock * HB,
										Function * F ,BasicBlock * L , BasicBlock * Body,BasicBlock * endBlock,Instruction* randomAlloca){

			if (HB == L && Body == nullptr && endBlock == nullptr){
				BasicBlock * newHB = BasicBlock::Create(F->getContext(),Twine("new"+HB->getName()),F) ;
				BasicBlock * BB = BasicBlock::Create(F->getContext(),"Switch",F);
				PHINode * headerPhi = nullptr;
				PHINode * newHeaderPhi = nullptr;
		
				SmallVector<BasicBlock*,10> block ;
				block.push_back(HB);
				block.push_back(newHB);
				randInstructions.push_back((Value *) BinaryOperator::Create(Instruction::SRem,randInstructions[randInstructions.size()-1],(Value *)ConstantInt::get(IntegerType::get(F->getContext(),32),2,false),"randomNumber"));			
				// Random instruction inserted in the switch block
				for (unsigned i=0;i<randInstructions.size();i++){
					BB->getInstList().push_back((Instruction *) randInstructions[i]);
				}
				/// The store instruction is to store the random number in the randomAlloca location
				Instruction * storeInst = new StoreInst(randInstructions[randInstructions.size()-1],randomAlloca);
				BB->getInstList().push_back(storeInst);

				/// Creating switch instructions and constants for the case statements
				SwitchInst * SW = SwitchInst::Create(randInstructions[4],BB,4,BB);
				SmallVector<ConstantInt * , 5> constants;
				for (unsigned i=0;i<2;i++){
					constants.push_back(ConstantInt::get( IntegerType::get(F->getContext() , 32) ,i , false));
				}
				
				SW->addCase(constants[0],HB);
				SW->addCase(constants[1],newHB);
				///////////
				//// Altering the pre header to point to the switch block
				AlterPreHeader(preHeader,BB,HB);
				/// For cloning the instructions in the header block
				SmallVector<Instruction *,10> Inst;
				ValueToValueMapTy vmap;
				for (Instruction &I : *HB){
					Instruction * i =I.clone();
					vmap[&I]= i;
					Inst.push_back(i);
					if (isa<PHINode>(&I)) {headerPhi = dyn_cast<PHINode>(&I); newHeaderPhi= dyn_cast<PHINode>(i);}
					RemapInstruction(i,vmap,RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
				}
				/// Cloned instruction inserted in the newly created block
				for (unsigned i=0;i<Inst.size();i++){
					newHB->getInstList().push_back(Inst[i]);
				}

				BranchInst * HBbranch = dyn_cast<BranchInst>(HB->getTerminator());
				BranchInst * newHBbranch = dyn_cast<BranchInst>(newHB->getTerminator());

				/// Altering the branch instructions of the header block and the new block
				if (HBbranch!=nullptr && HBbranch->isConditional()){
					if (HBbranch->getSuccessor(0)==HB) {
						HBbranch->setSuccessor(0,newHB);
						newHBbranch->setSuccessor(0,HB);
					}
					else if (HBbranch->getSuccessor(1)==HB) {
						HBbranch->setSuccessor(1,newHB);
						newHBbranch->setSuccessor(1,HB);
					}
				}
				else if (HBbranch->isUnconditional()){
					if (HBbranch->getSuccessor(0)==HB){
						HBbranch->setSuccessor(0,newHB);
						newHBbranch->setSuccessor(0,HB);
					} 
				}
				/// If phi Node present in the header block the alter the incoming blocks
				if (headerPhi != nullptr){
					if (headerPhi->getIncomingBlock(0)==HB){
						headerPhi->setIncomingBlock(0,newHB);
						Instruction * V =(Instruction *) headerPhi->getIncomingValue(0);
						headerPhi->setIncomingValue(0,vmap[V]);
						headerPhi->setIncomingBlock(1,BB);
						newHeaderPhi->setIncomingBlock(1,BB);
						
					}
					if (headerPhi->getIncomingBlock(1)==HB){
						headerPhi->setIncomingBlock(1,newHB);
						Instruction * V =(Instruction *) headerPhi->getIncomingValue(1);
						headerPhi->setIncomingValue(1,vmap[V]);
						headerPhi->setIncomingBlock(0,BB);
						newHeaderPhi->setIncomingBlock(0,BB);
					}
				}
				return true;
			}	
			return false;		
		}
		/// Dominance issue checking for the Body . For body the dominance issue will only come if the value is defined in 
		/// the header block.
		static bool checkBody(Loop * L,SmallVector<BasicBlock*,10> Body,BasicBlock* preBlock,BasicBlock* HB){
			// Looping over all the blocks of the body 
			for (unsigned j = 0 ; j<Body.size(); j++){
                 SmallVector<Value*,5> dontDominate;
				 // Looping over the instruction in a body to find instructions with dominance issues
                 for (Instruction &I : * Body[j]){
                    if (!isa<PHINode>(&I)){
                         for (auto op = I.op_begin();op!=I.op_end();op++){
                            Value * v = op->get();
                            if (!isa<Constant>(v) && !isa<AllocaInst>(v) ){
                                BasicBlock * parentBlock = ((Instruction*)v)->getParent();
                                if (L->contains(parentBlock) && parentBlock==HB ){
                                    dontDominate.push_back(v);
                                  }             
    		                }             
        	             }   
			        }
	            }
				/// Adding phi instruction in the preBody for resolving the dominance issues
				for(unsigned i = 0 ; i < dontDominate.size() ; i++){
						BasicBlock * pB = ((Instruction*)dontDominate[i])->getParent();
						PHINode * phi1 = PHINode::Create(dontDominate[i]->getType(),0);
						for(BasicBlock* b : predecessors(preBlock)){
							if(b == pB){
								phi1->addIncoming(dontDominate[i],pB);
							}
							else{
								Type * phiType = dontDominate[i]->getType();
									if (phiType->isAggregateType()) phi1->addIncoming( ConstantAggregateZero::get(phiType),b);
									else if(phiType->isPointerTy()) phi1->addIncoming(ConstantPointerNull::get((PointerType * )phiType),b);
									else  phi1->addIncoming( Constant::getAllOnesValue(phiType),b);
							}
						
						}
						
					dontDominate[i]->replaceAllUsesWith(phi1);
					
					preBlock->getInstList().push_front(phi1);
					}
            }
            return false;
            
    


        }

		/// For checking the dominate issues in the latch or endblock
        static bool checkIfInstDominatesUses(BasicBlock * B,Loop * L,BasicBlock * preBlock){
            SmallVector <Value *,5> dontDominate ;
            
			/// Loop to detect the instructions for which dominate issues are present
            for (Instruction &inst : *B ){
                    if (!isa<PHINode>(inst) && !isa<BranchInst>(inst)){ //and not branch inst
                          for(auto op = inst.op_begin();op!=inst.op_end() ; op++){
                            Value * v = op->get() ;
                            if(!isa<Constant>(v)){
                                  BasicBlock * pB = ((Instruction*)v)->getParent() ;
                                  if(L->contains(pB) && pB != B){
                                    
                                    dontDominate.push_back(v);
                                }
        
                            }
                        }
					}
			}
			/// Adding phi node in the preblocks to resolve the dominance issue
            for(unsigned i = 0 ; i < dontDominate.size() ; i++){
                BasicBlock * pB = ((Instruction*)dontDominate[i])->getParent() ;
             	PHINode * phi1 = PHINode::Create(dontDominate[i]->getType(),0);
                for(BasicBlock* b : predecessors(preBlock)){
                    if(b == pB){
                        phi1->addIncoming(dontDominate[i],pB);
                    }
                    else{  // case when the edge is coming from a block which has no dominance issue
						Type * phiType = dontDominate[i]->getType();
							if (phiType->isAggregateType()) phi1->addIncoming( ConstantAggregateZero::get(phiType),b);
                            else if(phiType->isPointerTy()) phi1->addIncoming(ConstantPointerNull::get((PointerType * )phiType),b);
                            else  phi1->addIncoming( Constant::getAllOnesValue(phiType),b);
                    }
                
                }
                // Place the phi node in the preblock
               dontDominate[i]->replaceAllUsesWith(phi1);
               preBlock->getInstList().push_front(phi1); 
                
            }
            return false;
        }
		/// For changing the preExisting srand function to userSrand This is called only once
		 static bool preProcessModule(Module * M){
                Function * srandPtr = nullptr ;
               
                srandPtr = M->getFunction("srand");
                if(srandPtr!=nullptr) {
                    srandPtr->setName("userSrand");
                    return true;
                }
                return false;
        }
		/// Function to run the transformation on the innermost loop
		static void RunInnermostLoop(Loop * L,Function * F , bool *changed){

 			for (Loop * NL : *L){
				if (NL->getSubLoops().size()>0){
					 RunInnermostLoop(NL,F,changed);
				}
				else {
					*changed = runOnLoop(NL,F);
				}
			}
		}


		bool runOnFunction(Function &F) override{
			
			legacy::FunctionPassManager FPM(F.getParent());
			FPM.add(createLoopSimplifyPass());

			FPM.run(F);
			//dbgs()<<"****### running on "<<F.getParent()->getName();

			srand(time(NULL));
            //***** Uncomment to test the name changing of srand function
			//if (!hi) hi = preProcessModule(F.getParent());
			
			LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
			bool changedLoop = false;
			// First run on the innermost loop then the outer loop
			for (Loop * L : LI){
				if (L->getSubLoops().size()==0) runOnLoop(L,&F);
				else RunInnermostLoop(L,&F,&changedLoop);
			}
			for (Loop *L : LI){
			 	if (L->getSubLoops().size()>0) changedLoop=runOnLoop(L,&F);
			}
			return changedLoop;
		
		}
		
		static bool runOnLoop(Loop *L , Function *F) {
	
			std::map<BasicBlock*,BasicBlock*> newBlocksMap;  // For storing the mapping between the block and their preblock
			std::map<BasicBlock*,SmallVector<BasicBlock*,10>> prevBlocksMap; // For storing the mapping between block and the list containing prev blocks
			std::map<BasicBlock*,BasicBlock*> succBlocksMap; 
			/// Getting the header , latch 
			BasicBlock * HeaderBlock = L->getHeader();
			BasicBlock * Latch = L->getLoopLatch();
			BranchInst * headerBranch=dyn_cast<BranchInst>(HeaderBlock->getTerminator());

			BasicBlock * PreHeader = L->getLoopPreheader();
            if (!PreHeader || !headerBranch) return false;
			// Preparing the Random instructions 
			SmallVector<Value * ,5> RandInstructions;
			prepareRandInstructions(RandInstructions,F);
			/// Alloca instruction for storing the random integer generated during runtime
			/// Alloca inserted in the preheader
			Instruction * randomAlloca = new AllocaInst(Type::getInt32Ty(F->getContext()),0,"randomU");
			F->getEntryBlock().getInstList().push_front(randomAlloca);
            /// if header block == latch then handling seperately
			if (HeaderBlock == Latch) {
               	specialCaseHandle(RandInstructions,PreHeader,HeaderBlock,F,Latch,nullptr,nullptr,randomAlloca);
				return true; 
            }
			// Adding the store instruction in the header block to reset the value stored in random alloca
			Instruction *storeInst = new StoreInst((Value*)Constant::getIntegerValue(Type::getInt32Ty(F->getContext()),APInt(32,0)),randomAlloca);
            HeaderBlock->getInstList().push_front(storeInst);
			/// Populating the prevblocks map for latch
			if (Latch && prevBlocksMap.find(Latch)==prevBlocksMap.end()){
     			SmallVector<BasicBlock *,10> predLatch;   		
  	    		prevBlocksMap.insert(std::make_pair(Latch,predLatch));
                for (BasicBlock * Pred : predecessors(Latch)){
	   			prevBlocksMap.at(Latch).push_back(Pred);
		    	}
			}
			BasicBlock * endBlock;
			if (headerBranch && headerBranch->getNumSuccessors()==1){
				endBlock = nullptr;
    		}
			/// Populating the prevBlocks map for endblock
			else {
                endBlock = headerBranch->getSuccessor(1);
				if (prevBlocksMap.find(endBlock)==prevBlocksMap.end()){
					SmallVector<BasicBlock * , 10> predEnd;
					prevBlocksMap.insert(std::make_pair(endBlock,predEnd));
					for (auto * Pred : predecessors(endBlock)){
						prevBlocksMap.at(endBlock).push_back(Pred);
					}
                }
			}


			SmallVector<BasicBlock * , 10> Body;
			/// Populating the body vector from the body blocks of the loop
			for (unsigned i = 0 ; i < L->getBlocks().size() ; i++){
				if (L->getBlocks()[i]!=HeaderBlock && L->getBlocks()[i]!=Latch && L->getBlocks()[i]!=endBlock){
					Body.push_back(L->getBlocks()[i]);
    				if (prevBlocksMap.find(L->getBlocks()[i])==prevBlocksMap.end()){
						SmallVector<BasicBlock * , 10> predBody;
						prevBlocksMap.insert(std::make_pair(L->getBlocks()[i],predBody));
						for (auto * Pred : predecessors(L->getBlocks()[i])){
							prevBlocksMap.at(L->getBlocks()[i]).push_back(Pred);
						}
					}


				}
			}

			SmallVector<BasicBlock * , 10 > NewBlocks;
			/// Part where transformation and updation happens
			prepareNewBlocks(F,NewBlocks,HeaderBlock,Latch,endBlock,Body,RandInstructions,newBlocksMap,prevBlocksMap,randomAlloca);
			if (PreHeader) {
				AlterPreHeader(PreHeader,NewBlocks[NewBlocks.size()-1],HeaderBlock);
			}
     		AlterHeaderOrEndBlock(HeaderBlock,Body,Latch,endBlock,newBlocksMap);
			if (endBlock) AlterHeaderOrEndBlock(endBlock,Body,Latch,HeaderBlock,newBlocksMap);
			if(Body.size()>0) AlterBody(Body,Latch,F,HeaderBlock,endBlock,newBlocksMap);
			/// Loop to add an incoming value from the switch block 
			for (unsigned i= 0 ;i<NewBlocks.size();i++){
				for (Instruction &I : *NewBlocks[i] ){

					if ( auto * ph = dyn_cast<PHINode>(&I)){
							Type * phiType = ((Value*)(&I))->getType();
							if (phiType->isAggregateType()) ph->addIncoming( ConstantAggregateZero::get(phiType),NewBlocks[NewBlocks.size()-1]);
                            else if(phiType->isPointerTy()) ph->addIncoming(ConstantPointerNull::get((PointerType * )phiType),NewBlocks[NewBlocks.size()-1]);
							else ph->addIncoming( Constant::getAllOnesValue(phiType),NewBlocks[NewBlocks.size()-1]);
						
                            continue ; 
					}
                    else break;
				}
			}
			/// Post process and check of the dominate issues and resolving it
            if (Latch) checkIfInstDominatesUses(Latch,L,newBlocksMap.at(Latch));
            if (Latch) postProcess(Latch,endBlock,Body,newBlocksMap);
            if (endBlock) checkIfInstDominatesUses(endBlock,L,newBlocksMap.at(endBlock));
			if (Body.size()>0) checkBody(L,Body,newBlocksMap.at(Body[0]),HeaderBlock);        

            
   			return true;

		}



	};
       

}

char Flattening::ID = '1';
bool Flattening::hi = false;
/// For running the pass from opt using -flatten command
static RegisterPass<Flattening> Hi("flatten","Control flow flattening");
/// For running the pass directly from clang 
static void registerMyPass(const PassManagerBuilder &, legacy::PassManagerBase &PM){
	PM.add(new Flattening());
}
static RegisterStandardPasses RegisterMyPass ( PassManagerBuilder::EP_EarlyAsPossible,registerMyPass);