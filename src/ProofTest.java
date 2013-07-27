import static org.junit.Assert.*;

import org.junit.Test;


public class ProofTest{
  @Test
	public void testReasonDelagation(){
		String[] test= new String[2];
		test[0]="show";
		test[1]="(a=>b)";
		TheoremSet mythm= new TheoremSet();
		Proof tester = new Proof(mythm);
		try{
			tester.reasonDelagation(test);
		}catch(IllegalInferenceException e){
			System.out.println(e);
		}
		test[1]="((a=>b)=>c)";
		try{
			tester.reasonDelagation(test);
		}catch(IllegalInferenceException e){
			System.out.println(e);
		}
		test[1]="ab";
		try{
			tester.reasonDelagation(test);
		}catch(IllegalInferenceException e){
			System.out.println(e);
		}
	}
	

}
