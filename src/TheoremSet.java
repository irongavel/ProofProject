import java.util.Hashtable;
import java.util.LinkedList;

public class TheoremSet{

	public Hashtable<String,LinkedList<String>> myTheorems;

	public TheoremSet ( ) {
		myTheorems = new Hashtable<String,LinkedList<String>>();
	}

	public void put (String s, Expression e) {
		myTheorems.put(s,e.Queue);
	}

	//public void put (String s, String e) {
	//	myTheorems.put(s,e);
	//}

	public LinkedList<String> get (String s)
	{
		return myTheorems.get(s);
	}

	public boolean contains (String s)
	{
		return myTheorems.containsValue(s);
	}
}
