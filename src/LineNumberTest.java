import static org.junit.Assert.*;

import org.junit.Test;


public class LineNumberTest {

  @Test
	public void testLineNumber() {
    //test Constructor, toString, lineNumberSize
		LineNumber test= new LineNumber();
		assertTrue(test.toString().equals("1"));
		assertEquals(test.lineNumberSize(),1);
		//test Step
    test.step();
		assertTrue(test.toString().equals("2"));
		assertEquals(test.lineNumberSize(),1);
		//test layerMinus
    test.layerMinus();
		assertTrue(test.toString().equals("2.1"));
		assertEquals(test.lineNumberSize(),2);
		test.step();
		assertTrue(test.toString().equals("2.2"));
		assertEquals(test.lineNumberSize(),2);
		//test layerUp, CurrentSuper
    test.layerUp();
		assertTrue(test.toString().equals("3"));
		assertEquals(test.lineNumberSize(),1);
		assertTrue(test.currentSuper().equals("1"));
		assertEquals(test.lineNumberSize(),1);
		//test longer arrays
    test.layerMinus();
		test.step();
		test.layerMinus();
		test.step();
		test.step();
		test.layerMinus();
    //test readyAssume true, currentSuper
		assertTrue(test.toString().equals("3.2.3.1"));
		assertEquals(test.lineNumberSize(),4);
		assertEquals(test.currentSuper(),"3.2.3");
		assertTrue(test.readyAssume());
		//test readyAssume false, currentSuper
    test.step();
		assertTrue(test.toString().equals("3.2.3.2"));
		assertEquals(test.lineNumberSize(),4);
		assertEquals(test.currentSuper(),"3.2.3");
		assertFalse(test.readyAssume());	
	}
}

