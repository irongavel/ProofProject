import java.util.Hashtable;
import java.util.LinkedList;

public class TheoremSet{

	public Hashtable<String,LinkedList<String>> myTheorems;

	public TheoremSet ( ) {
		//Constructs a TheoremSet Object, with empty hashTable myTheorems
		myTheorems = new Hashtable<String,LinkedList<String>>();
	}

	public void put (String s, Expression e) {
		//stores the expression e's queue to key s
		myTheorems.put(s,e.Queue);
	}
	
	public void put (String s, LinkedList<String> e)
	{
		//stores the queue e to key s
		myTheorems.put(s,e);
	}

	public LinkedList<String> get (String s)
	{
		//returns the queue stored under key s
		return myTheorems.get(s);
	}
}
