import java.util.*;

public class LineNumber {


	// CLASS VARIABLES//

	/*
	 * Main ArrayList that holds the line number integers (layers) in different elements
	 */
	private ArrayList<Integer> currentPosition = new ArrayList<Integer>();


	// METHODS //

	/*
	* Constructor for creating a LineNumber object
	* Starts main layer at 1 (for first proof to be implemented)
	*/
	public LineNumber() {
		currentPosition.add(0,1);
	}


	/*
	* Method that "goes along" a given layer; increments given layer
	* Does not remove subcurrentPosition behind it
	* I.e. 3.4.2 --> 3.4.3
	*/
	public void step() {
		int last = currentPosition.size() - 1;
		currentPosition.set(last, currentPosition.get(last) + 1);
	}  


	/*
	* Shuffles up to the next sublayer, despite what the sub-sublayer is
	* I.e. 3.4.2 --> 3.5
	*/
	public void layerMinus() {
		currentPosition.add(new Integer(1));	
	}


	/*
	* Shuffles down to the next sublayer, despite what the sub-sublayer is
	* I.e. 3.4.5 --> 3.4
	*/
	public void layerUp() {
		currentPosition.remove(currentPosition.size() - 1);
		this.step();
	}


	/*
	* returns Line Number of current Show
	*/
	public String currentSuper()
	{
		if(this.toString().length()!=1)
		{
			return this.toString().substring(0, this.toString().length()-2);
		}
		return "1";
	}


	/*
	* Returns the current line number as a String object
	*/
	public String toString() {
		String rtn = "";
		//for (int i : currentPosition)
		for (int i = 0; i < currentPosition.size(); i++)
		{
			if (i != 0)
			{
				rtn += ".";
			}
			rtn += currentPosition.get(i);
		}
		return rtn;
	}

	// HELPER METHODS //

	/*
	* Returns size of a line number
	* Size of a line number = quantity of integers
	* I.e. 1.2.3 has a size of three
	* Used only in LineNumberTest.java
	*/
	public int lineNumberSize() {
		return currentPosition.size();
	}
	//returns whether last bit of LineNumber is 1 (ready to assume)
	public boolean readyAssume(){
	    Integer temp = currentPosition.get(currentPosition.size()-1);
		return temp==1;
	}

// Ends LineNumber class
 }
