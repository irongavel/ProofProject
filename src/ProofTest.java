import static org.junit.Assert.*;

import org.junit.Test;


public class ProofTest{
  @Test
	public void testReasonDelagation(){
		TheoremSet mythm= new TheoremSet();
		Proof tester = new Proof(mythm);
		try{
			tester.extendProof("show ((a=>b)=>((b=>c)=>(a=>c)))");
			tester.extendProof("assume (a=>b)");
			tester.extendProof("show ((b=>c)=>(a=>c))");
			tester.extendProof("assume (b=>c)");
			tester.extendProof("show (a=>c)");
			tester.extendProof("assume a");
			tester.extendProof("show c");
			tester.extendProof("assume ~c");
			tester.extendProof("mt 3.2.2.1 3.1 ~b");
			tester.extendProof("mt 2 3.2.2.2 ~a");
			tester.extendProof("co 3.2.2.3 3.2.1 c");
			tester.extendProof("ic 3.2.2 (a=>c)");
			tester.extendProof("ic 3.2 ((b=>c)=>(a=>c))");
			tester.extendProof("ic 3 ((a=>b)=>((b=>c)=>(a=>c)))");
			assertTrue(tester.isComplete());
		}catch(IllegalInferenceException e){
			System.out.println(e);
		} catch (IllegalLineException e) {
			// TODO Auto-generated catch block
			System.out.println(e);
		}
		//Running through given ProofExamples
	
		//Test nested show/assumes, mt, co, ~logic, and ic
		//errors thrown: wrong number of args, out ofLine Scope
		String [] myTxts1 = {"thmSetOne.txt","proof01_Revised.txt"};
		ProofChecker myChecker = new ProofChecker(myTxts1);
		// Test mp, ic
		String [] myTxts2 = {"thmSetOne.txt","proof02_Revised.txt"};
		myChecker = new ProofChecker(myTxts2);
		//test assuming ~show, co, ic, double ~
		String [] myTxts3 = {"thmSetOne.txt","proof03_Revised.txt"};
		myChecker = new ProofChecker(myTxts3);
		//Test Theorem Use, and/or logic, mp, co, ic
		String [] myTxts4 = {"thmSetTwo.txt","proof04_Revised.txt"};
		myChecker = new ProofChecker(myTxts4);
		//test Theorem with double tilde, tilde logic, co, mp, ic
		String [] myTxts5 = {"thmSetTwo.txt","proof05_Revised.txt"};
		myChecker = new ProofChecker(myTxts5);
		//Test mp, ic, nesting
		String [] myTxts6 = {"thmSetOne.txt","proof06_Revised.txt"};
		myChecker = new ProofChecker(myTxts6);
		//tests Error Catching
		String [] myTxts7 ={"thmSetTwo.txt","proofExample.txt"};
		myChecker = new ProofChecker(myTxts7);
		//tests Repeat
		String [] myTxts8 = {"thmSetOne.txt","repeatProof.txt"};
		myChecker=new ProofChecker(myTxts8);
	}


}
