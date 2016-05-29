/*
 * Authors: Name(s) <email(s)>
 * 
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/Analysis/CFG.h"
#include <algorithm>
#include <cstdlib>
#include <stack>
#include <stdlib.h>
 
using namespace llvm;
 
class compare {
public:
	bool operator() (const BasicBlock* x, const BasicBlock* y) {return x->getName() < y->getName();}
};

typedef std::map<const BasicBlock*, std::vector<const BasicBlock*>, compare> set;
typedef std::map<std::pair<Value*, Value*>, GlobalVariable*> eM;
typedef	std::map<const BasicBlock*, GlobalVariable*, compare> bbM;

namespace {

	static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
		std::vector<Type*> printf_arg_types;
		printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
 	
		FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
		Function *func = mod->getFunction("printf");
		if(!func)
		  func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
		func->setCallingConv(CallingConv::C);
		return func;
	}

	struct CS201Profiling : public FunctionPass {

		
		static char ID;
		LLVMContext *Context;
		bbM bbMap;
		eM edgeMap;
		GlobalVariable *bbCounter = nullptr;
		GlobalVariable *prevBB = nullptr;
		BasicBlock *prevBlock;


    	GlobalVariable *BasicBlockPrintfFormatStr = NULL;
		Function *printf_func = NULL;
		CS201Profiling() : FunctionPass(ID) {}


		//----------------------------------
		void FindPredecessorSet(Function &F, set &PredSet);
		void FindDominatorSet(Function &F, set &PredSet, set &AllDomSets);
		void printV(std::vector<const BasicBlock*> & v);
		void printSet(set s);
		void FindBackEdges(set& AllDomSets, std::vector<std::pair<const BasicBlock*, const BasicBlock*>> &BackEdges);
		void LoopConstruction(std::vector<std::pair<const BasicBlock*, const BasicBlock*>> &BackEdges, std::vector<std::vector<const BasicBlock*>> &LoopSet);
		void Insert(const BasicBlock* node, std::vector<const BasicBlock*> &loop, std::stack<const BasicBlock*> &s);
		


		bool doInitialization(Module &M) {
		errs() << "\n---------Starting BasicBlockDemo---------\n";
		 
		errs() << "Module: " << M.getName() << "\n";
		Context = &M.getContext();

	  
	    bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
	    const char *finalPrintString = "BB Count: %d\n";
	    Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	    BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
	    printf_func = printf_prototype(*Context, &M);
 
 		
		for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I) {
			for (Function::iterator b = I->begin(), E = I->end(); b != E; ++b) {

				//Set name for all basic blocks
				BasicBlock * BB = b;
				std::string s = "0";
				b->setName(s);
				++s.at(0);

				// Initialize bbMap
				bbMap[BB] = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbMap");
				

				// Initialize edgeMap
				IRBuilder<> IRB(BB->getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
				int i;
				BB->getName().getAsInteger(0, i);
				Value * curr = IRB.getInt32(i);
				for (succ_iterator I = succ_begin(BB), E = succ_end(BB); I != E; ++I) {
	 				BasicBlock *S = *I;
	 				IRBuilder<> IRB(S->getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
					int j;
					S->getName().getAsInteger(0, j);
					Value * succ = IRB.getInt32(j);
	 				std::pair<Value*, Value*> p(curr,succ);
	 				edgeMap[p] = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "edgeMap");
					
					IRB.CreateStore(IRB.getInt32(0),edgeMap[p]);
				}

	    }

		//	errs() << bbMap.size() << '\n';
	
		}
		//errs() << bbMap.size() << '\n';


		return true;
		}
	 
		//----------------------------------
		bool doFinalization(Module &M) {
		errs() << "-------Finished CS201Profiling----------\n";
	
		return false;
		}
		//----------------------------------
		bool runOnFunction(Function &F) override {

			errs() << "Function: " << F.getName() << '\n';
			
			// for(Function::iterator b = F.begin(); b!= F.end(); ++b) {
			// 	BasicBlock * BB = b;
			// 	IRBuilder<> IRB(BB->getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
			// 	int i;
			// 	BB->getName().getAsInteger(0, i);
			// 	Value * curr = IRB.getInt32(i);
			// 	for (succ_iterator I = succ_begin(BB), E = succ_end(BB); I != E; ++I) {
		 // 				BasicBlock *S = *I;
		 // 				IRBuilder<> IRB(S->getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
			// 			int j;
			// 			S->getName().getAsInteger(0, j);
			// 			Value * succ = IRB.getInt32(j);
		 // 				std::pair<Value*, Value*> p(curr,succ);
		 // 				edgeMap[p] = new GlobalVariable(*F.getParent(), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "edgeMap");
						
			// 			IRB.CreateStore(IRB.getInt32(0),edgeMap[p]);
			// 	 }
			// }
			// Output predecessors
			set PredSet, AllDomSets;
			std::vector<std::pair<const BasicBlock*, const BasicBlock*>> BackEdges;
			std::vector<std::vector<const BasicBlock*>> LoopSet;

			FindPredecessorSet(F, PredSet);
			FindDominatorSet(F,PredSet, AllDomSets);
			FindBackEdges(AllDomSets, BackEdges);
			LoopConstruction(BackEdges, LoopSet);
			

			for(auto &BB: F) {
				// Add the footer to Main's BB containing the return 0; statement BEFORE calling runOnBasicBlock
				if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())) { // major hack?
					addFinalPrintf(BB, Context, bbMap, bbCounter, BasicBlockPrintfFormatStr, printf_func);
				}

					runOnBasicBlock(BB);
			}

			return true;
		}

		    //----------------------------------
		bool runOnBasicBlock(BasicBlock &BB) {

			IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction

			Value *loadAddr = IRB.CreateLoad(bbMap[&BB]);
			Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
			IRB.CreateStore(addAddr, bbMap[&BB]);

			// int j;
			// BB.getName().getAsInteger(0, j);
			// Value* currBB = new GlobalVariable(*((BB.getParent())->getParent()), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "currBB");	
			// IRB.CreateStore(IRB.getInt32(j), currBB);
			// Value *loadCurrBB = IRB.CreateLoad(currBB);
			// loadCurrBB->setName("loadCurrBB");
			// errs() <<" CURR NAME: " << loadCurrBB->getName() << '\n';
			// // Load Prev
			// //Value *pBB = IRB.CreateLoad(prevBB);
			// if(!prevBB) {
			// 	prevBB = new GlobalVariable(*((BB.getParent())->getParent()), Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, ConstantInt::get(Type::getInt32Ty(*Context), 0), "prevBB");
			// 	IRB.CreateStore(loadCurrBB, prevBB);
			// 	errs() <<"CURR: " << loadCurrBB->getName() << '\n' << "PREV: " << prevBB->getName() << '\n';
			// 	return true;
			// }
			//currBB->print(errs()); errs() << '\n';
			//prevBB->print(errs()); errs() << '\n';
			// std::pair<Value*, Value*> p(prevBB, currBB);
			// if (edgeMap[p]) {
			// }
			// // for(auto&I:BB)
			// // 	errs() << I << '\n';

			//IRB.CreateLoad(edgeMap[p]);
			//IRB.CreateStore()
			// Store Curr into Prev

			// Load Curr into new value object
			//GlobalVariable * currBB;

	//IRB.CreateStore(s,prevBB);
			

			//IRB.CreateStore(s, prevBlock);

			// int i;
			// BB.getName().getAsInteger(0, i);
			// //errs() << i << '\n';			

			// if(prevBlock->hasName()) {
			// 	std::pair<const BasicBlock*, const BasicBlock*> edge(prevBlock, BB);
			// 	// Value *loadAddr1 = IRB.CreateLoad(edgeMap[edge]);
			// 	// Value *addAddr1 = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr1);
			// 	// IRB.CreateStore(addAddr1, edgeMap[edge]);
			// }


      		

			return true;
		}


		void addFinalPrintf(BasicBlock& BB, LLVMContext *Context, bbM &bbMap,  GlobalVariable *bbCounter, GlobalVariable *var, Function *printf_func) {
			IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
			std::vector<Constant*> indices;
			Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
			indices.push_back(zero);
			indices.push_back(zero);
			Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);

			for(bbM::iterator i = bbMap.begin(); i != bbMap.end(); ++i) {

				Value *bbc = builder.CreateLoad(i->second);
				bbc->setName(i->first->getName());
				std::string s = i->first->getName();
				s.append(": %d\n");
				const char *finalPrintString = s.c_str();
	    		Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
	    		BasicBlockPrintfFormatStr = new GlobalVariable(*((BB.getParent())->getParent()), llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
		
				Constant *var_ref1 = ConstantExpr::getGetElementPtr(BasicBlockPrintfFormatStr, indices);
				CallInst *call1 = builder.CreateCall2(printf_func, var_ref1, bbc);
				call1->setTailCall(false);


			}
			// Value *bb = builder.CreateLoad(bbCounter);
   //   		CallInst *call1 = builder.CreateCall2(printf_func, var_ref, bb);
   //    		call1->setTailCall(false);
			

		}



	};

}


bool predCompare(const BasicBlock* lhs, const BasicBlock* rhs)
{
	return lhs->getName() < rhs->getName();
}
void CS201Profiling::printSet(set s)
{
	for(set::iterator it = s.begin(); it!= s.end(); ++it)
	{
		errs() << "[" << it->first->getName() << "] => ";
		for(size_t j = 0; j < it->second.size(); ++j)
		{
			errs() << it->second.at(j)->getName() << ' ';
		}
		errs() << '\n';
	}
	errs() << '\n';
}


void CS201Profiling::FindPredecessorSet(Function &F, set & PredSet) {

	// Obtain each node's pedecessors
	for(Function::iterator i = F.begin(), e = F.end(); i != e; ++i){
	 	const BasicBlock * block = i;
	 	std::vector<const BasicBlock*> current;
	 	for (const_pred_iterator PI = pred_begin(block), E = pred_end(block); PI != E; ++PI) {
	 		const BasicBlock *P = *PI;
	    	current.push_back(P);
	    }
	    PredSet[block] = current;	
	}
	errs() << "Predecessors:" << '\n';
	printSet(PredSet);	

}

void CS201Profiling::FindDominatorSet( Function &F, set & PredSets, set & AllDomSets) {


	// // D(n_0) = {n_0}
	std::vector<const BasicBlock*> start;
	start.push_back(F.begin());
	AllDomSets[F.begin()] = start;

	std::vector<const BasicBlock*> current;

	// collect all nodes (N)
	for(Function::iterator i = F.begin(), e = F.end(); i != e; ++i){
		BasicBlock * block = i;
		current.push_back(block);
	}
	
	// for all n in N s.t. n != n_0, do D(n) = N
	for(Function::iterator i = ++F.begin(), e = F.end(); i != e; ++i){
		BasicBlock * block = i;
		AllDomSets[block] = current;
	}

	bool change = 0;

	// // for n in N - {n_0} do
	do {
	 	change = 0;
		for(set::iterator it = ++AllDomSets.begin(); it != AllDomSets.end(); ++it){

			// Set of n's predecessors
			std::vector<const BasicBlock*> NPS;

			// Set of predecessor's dominators
			std::vector<const BasicBlock*> PDS1;
			std::vector<const BasicBlock*> PDS2;

			//get all predecessors of current node n
			NPS =  PredSets[it->first];
		
			// Get node's first predecessor's dominator set
			PDS1 = AllDomSets[NPS.at(0)];

			//Interesction of all D(p)
			for(size_t j = 1; j < NPS.size(); ++j) {
				PDS2 = AllDomSets[NPS.at(j)];
		
				std::vector<const BasicBlock*> intersection;
				std::set_intersection(PDS1.begin(), PDS1.end(), PDS2.begin(), PDS2.end(), back_inserter(intersection), predCompare);
				PDS1 = intersection;
				
			}

		//	Union with n
		//	D(n) = {n} U intersection of D(p)
			PDS1.push_back(it->first);

			if(PDS1 != it->second)
				change = 1;

			it->second = PDS1;
		}
	}while(change);

	errs() << "DominatorSet: " << '\n';
	printSet(AllDomSets);

}

void CS201Profiling::FindBackEdges(set& AllDomSets, std::vector<std::pair<const BasicBlock*, const BasicBlock*>> &BackEdges)
{
	for(set::iterator it = AllDomSets.begin(); it != AllDomSets.end(); ++it)
	{
		// Iterate through all node's successsors
		for (succ_const_iterator PI = succ_begin(it->first), E = succ_end(it->first); PI != E; ++PI) {
	 		const BasicBlock *P = *PI;
	    	// Find successor in node's dominator set
	    	std::vector< const BasicBlock*>::iterator f;
	    	f = find(it->second.begin(), it->second.end(), P); 

	    	if( f != it->second.end()) { // successor found (successor dominates current node)
	    		std::pair<const BasicBlock*, const BasicBlock*> p(it->first, *f);
	    		BackEdges.push_back(p);
			}
	    }
	}
	for(size_t i = 0; i < BackEdges.size(); ++i)
	{
		errs() << "Back Edge: " << BackEdges.at(i).first->getName() << "->" <<  BackEdges.at(i).second->getName() << "\n\n";
	}
}

void CS201Profiling::Insert(const BasicBlock* node, std::vector<const BasicBlock*> &loop, std::stack<const BasicBlock*> &s)
{
	std::vector<const BasicBlock*>::iterator it;
	it = find(loop.begin(), loop.end(), node);
	if( it == loop.end())
	{
		loop.push_back(node);
		s.push(node);
	}
}

void CS201Profiling::LoopConstruction(std::vector<std::pair<const BasicBlock*, const BasicBlock*>> &BackEdges, std::vector<std::vector<const BasicBlock*>> &LoopSet) {
	
	for(size_t i = 0; i < BackEdges.size(); ++i){
		std::stack<const BasicBlock*> s;
		std::vector<const BasicBlock*> loop;
		loop.push_back(BackEdges.at(i).second);

		Insert(BackEdges.at(i).first, loop, s);
		while(s.size()) {
			const BasicBlock* m = s.top();
			s.pop();
			for (const_pred_iterator PI = pred_begin(m), E = pred_end(m); PI != E; ++PI) {
	 			const BasicBlock *P = *PI;
	    		Insert(P, loop, s);
	    	}
		}
		LoopSet.push_back(loop);
	}
	errs() << "Loops: \n";
	for(size_t i = 0; i < LoopSet.size(); ++i) {
		for(size_t j = 0; j < LoopSet.at(i).size(); ++j) 
			errs() << LoopSet.at(i).at(j)->getName() << ' ';
		errs() << '\n';
	}
	errs() << "\n\n";
}

char CS201Profiling::ID = 0;
static RegisterPass<CS201Profiling> X("pathProfiling", "CS201Profiling Pass", false, false);
