import java.util.*;

public class Proof {
	//Private Variables
	private TheoremSet myTheoremSet;
		//contains proven statements, Input Theorems
	private LineNumber myLineNumber;
		//contains current LineNumber
	private Hashtable<String,LinkedList<String>> showTable;
		//contains show statements waiting to be proven
	private ArrayList<String> printList;
		//contains User input lines to be printed given the print command
	private Hashtable<String,String> operands;
		//contains all operands found while checking Theorem Equivalence, is cleared after checkTheoremEquivalence is called
	
	//Constructors
	public Proof (TheoremSet theorems) {
		myTheoremSet=theorems;
		myLineNumber=new LineNumber();
		showTable=new Hashtable<String,LinkedList<String>>();
		printList=new ArrayList<String>();
		operands = new Hashtable<String,String>();
		//takes in expression stuff from Theorems
	}
	
	//Called by ProofChecker
	public LineNumber nextLineNumber () {
		//returns current LineNumber
		return myLineNumber;
	}
	
	public void extendProof (String x) throws IllegalLineException, IllegalInferenceException{
		/*
		 * Uses StringSplitter to split String x into a String [], checks for null args
		 * Calls LineChecker on String[] statement, looking for syntax errors
		 * Calls ReasonDelegation on String[] Statement, Looks for Inference Errors then 
		 * 	deals with the args accordingly
		 * 
		 */
		String[] statement;
		try{
			statement = StringSplitter(x);
			LineChecker(statement);
			reasonDelegation(statement);
		//Proves a show if it exists in the theorem set
		}catch (IllegalLineException e){
			throw e;
		}catch (IllegalInferenceException e){
			throw e;
		}
	}

	public boolean isComplete ( ) {
		//stops looping in Proofchecker by returning true
		//returns true when showTable is empty
		if(ProofChecker.iAmDebugging){
		System.out.println(myTheoremSet.myTheorems.toString());
		}
		return showTable.isEmpty();
	}
	//Helper Methods
	
	//Syntax Checking
	public static String[] StringSplitter(String x) throws IllegalLineException{
		//Splits string x by looking for " ", checks for wildly wrong numbers of args or null args
		String[] rtn=x.split(" ");
		if ((rtn.length<1)||rtn.length>4){
			throw new IllegalLineException("***Too many Arguments: " + x);
		}else for(int i=0;i<rtn.length;i++){
			if (rtn[i]==null){
				throw new IllegalLineException("***Use only one space between Arguments: " + x);
			}
		}
		return rtn;
	}

	private boolean LineChecker(String[] statement) throws IllegalLineException, IllegalInferenceException {
		//check for correct space placement
		//checks for Line errors, returns true if isOK, returns false if error
		int numArgs;
		String command = statement[0];

		try{

			if (command.equals("print"))
			{
				numArgs = 1;
			}
			else if(command.equals("show")||
					command.equals("assume"))

					{numArgs = 2;

			}
			else if(command.equals("repeat")
					||command.equals("ic")
				    ||command.equals("theorem"))

					{numArgs = 3;
			}
			else if(command.equals("mp")||
					command.equals("mt")||
					command.equals("co"))

					{numArgs = 4;
			}
			else
			{
				if (this.myTheoremSet.get(command) == null)
				{
					throw new IllegalLineException("***Invalid Reason: " + command);
				}
				else
				{
					numArgs = 2;
				}
				
			}

			if (statement.length!=numArgs){
				throw new IllegalLineException("***Invalid Number of Args For: "+ statement [0]);
			}

			if (numArgs != 1)
			{
				ExpressionChecker(statement[numArgs-1]);

				if (numArgs==3)
				{
					LineNumberChecker(statement[1]);
					checkLineScope(statement[1]);
				}
				if (numArgs==4)
				{
					LineNumberChecker(statement[1]);
					LineNumberChecker(statement[2]);
					checkLineScope(statement[1]);
					checkLineScope(statement[2]);
				}
			}

		
		if (command.equals("repeat")){
			if(!new Expression(statement[2]).Queue.equals(myTheoremSet.myTheorems.get(statement[1]))){
				throw new IllegalLineException("***Named Expression is not at given line: "+ statement[2]);
			}
		}
		}
		catch (IllegalLineException e)
		{
			throw e;
		}

		return true;
	}
	
	public boolean checkLineScope(String input) throws IllegalLineException
	{	//Checks given input string as a lineNumber, Checks that given linenumber is in the 
		//scope of the current LineNumber
		
		String test = input.substring(0,input.length()-1);
		String temp = myLineNumber.toString();
		if (!myTheoremSet.myTheorems.containsKey(input)){
			throw new IllegalLineException("***Line Number is not in scope: "+input);
		}else if (input.length()>temp.length()){
			throw new IllegalLineException("***Line Number is too deep to be in scope: "+input);
		}else if (Character.getNumericValue((input.charAt(input.length()-1)))>=Character.getNumericValue((temp.charAt(input.length()-1)))){
			throw new IllegalLineException("***Line Number is not in scope: "+input);
		}else if (!temp.startsWith(test)&&input.length()!=1){
			throw new IllegalLineException("***Line Number is not in scope: "+input);
		}
		
		return true;
	}
	
	public static void LineNumberChecker(String x)throws IllegalLineException{
		//checks that x is just ints and .
		//checks that x has no . on the ends
		if ((Character.toString(x.charAt(0)).equals('.'))&&(Character.toString(x.charAt(x.length()-1)).equals('.')))
		{
			throw new IllegalLineException("***Invalid Line Number: "+x);
		}
		String[] test = x.split(".");
		for (int i=0;i<test.length;i++){
			try{
				Integer.parseInt(test[i]);
			}catch (NumberFormatException e){
				throw new IllegalLineException("***Invalid Line Number:" + x);
			} 
		}
	}

	public static void ExpressionChecker(String x) throws IllegalLineException{
		//checks Expression for valid Parentheses, typos
		//checks for nesting, operators within nesting, and syntax
		//uses an absolutely lovely double boolean array to index previous and current
		//characters while iterating to see if the combination is valid
		int a=0;
		int b=0;
		char test=0;
		int canHold=0;
		int needRight=0;
		boolean[][] dictionary=new boolean[][]{{false,false,true,false,true,false,false},
							{true,true,false,true,false,false,true},
							{false,false,true,false,true,false},
							{true,true,false,true,false,false,true},
							{true,true,false,true,false,false,true},
							{false,false,true,false,true,false,false},
							{false,false,false,false,false,true,false}};

		for(int i=0;i<x.length();i++){
			test=x.charAt(i);
			a=indexer(test);
			if (a==100){
				throw new IllegalLineException("***Invalid Expression: "+x);
			}
			if (!dictionary[a][b]){
				throw new IllegalLineException("***Invalid Expression: "+x);
			}
			if (test==')'){
				needRight--;
			}else if(test=='('){
				needRight++;
				canHold++;
			}else if(test=='='){
				canHold--;
			}else if(test=='|'||test=='&'){
				canHold--;
			}else if(test=='~'){
			}else if(!Character.isLetter(test)&&test!='>'){
				throw new IllegalLineException("***Invalid Expression: "+x);
			}
			if (canHold<0||needRight<0){
				throw new IllegalLineException("***Invalid Expression: "+x);
			}
			b=a;
		}
		if (canHold!=0||needRight!=0){
			throw new IllegalLineException("***Invalid Expression: "+x);
		}
	}

	public static int indexer(char x)throws IllegalLineException{
		//takes in a char and returns int to be used for indexing with Expression Checker's dictionary
		//throws IllegalLineException when the char is not of expected type
		switch(x){
			case '|':case'&': return 0;
			case '(': return 1;
			case ')': return 2;
			case '~': return 3;
			case '=': return 5;
			case '>': return 6;
			default: if(!Character.isLetter(x)){
						throw new IllegalLineException("***Invalid Expression: "+x);
					}else{
						return 4;
					}
		}
	}

	//Logic Checking
	
	public void reasonDelegation(String[] args) throws IllegalInferenceException
		{
			//Main Machine, reads args[0] and reacts according to the given reason
			//further details in the if blocks
			//various things done usually include stepping the line number, 
			//storing to myTheoremSet or showTable, and storing to printList
		String command = args[0];
		if (ProofChecker.iAmDebugging){
		System.out.println(args[0]);
		System.out.println(args[1]);
		}
		if (command.equals("show"))
		{	
			//Stores Given Expression in the show Table
			Expression temp = new Expression(args[1]);
			if (ProofChecker.iAmDebugging){
			System.out.println(temp.Queue);
			}
			this.storeprint(args);
			this.showTable.put(myLineNumber.toString(), temp.Queue);

			if(ProofChecker.iAmDebugging){
				System.out.println(myLineNumber);
				System.out.println(showTable.get(myLineNumber.toString()));
				System.out.println((myTheoremSet.myTheorems.isEmpty()));
			}
			if(myLineNumber.toString().equals("1"))
			{
				myLineNumber.step();
			}
			else
			{
				myLineNumber.layerMinus();
			}

		}
		if (command.equals("assume"))
		{
			//checks if at valid lineNumber, and that given Expression is valid
			//then adds given Expression to myTheoremSet
			if(!myLineNumber.toString().equals("2"))
			{
				if (!myLineNumber.readyAssume())
				{
					throw new IllegalInferenceException("***Must Use assume After a show");
				}
			}
			
			LinkedList<String> temp = showTable.get(myLineNumber.currentSuper());
			
			if (temp==null)
			{
				throw new IllegalInferenceException("***Show was not made at LineNumber: "+temp);
			}
			else if(temp.toString().equals("[~, "+(new Expression(args[1])).Queue.toString().substring(1))
					||("[~, "+temp.toString().substring(1)).equals((new Expression(args[1])).Queue.toString()))
			{
				this.storeprint(args);
				myTheoremSet.put(myLineNumber.toString(), new Expression(args[1]));
				myLineNumber.step();
				return;
			}
			else if (!findAssumption(temp).toString().equals((new Expression(args[1])).Queue.toString())||!temp.peek().equals("=>"))
			{
				throw new IllegalInferenceException("***Can Only Assume Left Side of => or ~ of Show: "+ args[1]);
			}
			
			this.storeprint(args);
			myTheoremSet.put(myLineNumber.toString(), new Expression(args[1]));
			myLineNumber.step();
		}
		if (command.equals("mp"))
		{
			//Runs the mp checker to see if the arguments given make a valid mp inference
			//Then if it is, it adds the inference to the theoremset and steps the line number
			if(mpChecker((LinkedList<String>) myTheoremSet.get(args[1]).clone(),
							(LinkedList<String>) myTheoremSet.get(args[2]).clone(),
							(LinkedList<String>) new Expression(args[3]).Queue.clone()))
			{
				this.storeprint(args);
				if(showTable.get(myLineNumber.currentSuper()).toString().equals((new Expression(args[3])).Queue.toString()))
				{
					myTheoremSet.myTheorems.put(myLineNumber.currentSuper(), showTable.get(myLineNumber.currentSuper()));
					showTable.remove(myLineNumber.currentSuper());
					if(showTable.size()!=0)
					{
						myLineNumber.layerUp();
					}
				}
				else
				{
					this.myTheoremSet.put(this.myLineNumber.toString(), new Expression(args[3]));
					myLineNumber.step();
				}
			}
			else
			{
				throw new IllegalInferenceException("***Invalid Inference: "+ args[3]);
			}
		}
		if (command.equals("mt"))
		{
			//Runs the mt checker to see if the arguments given make a valid mt inference
			//Then if it is, it adds the inference to the theoremset and steps the line number
			if(mtChecker((LinkedList<String>) myTheoremSet.get(args[1]).clone(),
						(LinkedList<String>) myTheoremSet.get(args[2]).clone(),
						(LinkedList<String>) new Expression(args[3]).Queue.clone()))
			{
				this.storeprint(args);
				if(showTable.get(myLineNumber.currentSuper()).toString().equals((new Expression(args[3])).Queue.toString()))
				{
					myTheoremSet.myTheorems.put(myLineNumber.currentSuper(), showTable.get(myLineNumber.currentSuper()));
					showTable.remove(myLineNumber.currentSuper());
					if(showTable.size()!=0)
					{
						myLineNumber.layerUp();
					}
				}
				else
				{
					this.myTheoremSet.put(this.myLineNumber.toString(), new Expression(args[3]));
					myLineNumber.step();
				}
			}
			else
			{
				throw new IllegalInferenceException("***Invalid Inference: "+args[3]);
			}
		}
		if (command.equals("co"))
		{
			//Checks to see if args[1] and args[2] reference contradictions. If so, we
			//convert args[3] to an expression list and add it to the theorem set.
			if (contradiction((LinkedList<String>)this.myTheoremSet.get(args[1]).clone(), 
							(LinkedList<String>)this.myTheoremSet.get(args[2]).clone()))
			{
				this.storeprint(args);
				if(showTable.get(myLineNumber.currentSuper()).toString().equals((new Expression(args[3])).Queue.toString()))
				{
					myTheoremSet.myTheorems.put(myLineNumber.currentSuper(), showTable.get(myLineNumber.currentSuper()));
					showTable.remove(myLineNumber.currentSuper());
					if(showTable.size()!=0)
					{
						myLineNumber.layerUp();
					}
				}
				else
				{
					this.myTheoremSet.put(this.myLineNumber.toString(), new Expression(args[3]));
					myLineNumber.step();
				}
			}
			else
			{
				throw new IllegalInferenceException("***Invalid Inference: "+ args[3]);
			}

		}
		if (command.equals("ic"))
		{
			//Checks to see if the given arguments are valid in proving the current subproof
			LinkedList<String> proveExpr = myTheoremSet.get(args[1]);
			LinkedList<String> showExpr = (new Expression(args[2])).Queue;
			if(showTable.get(myLineNumber.currentSuper()).toString().equals(showExpr.toString()))
			{
				if(findConsequent(showExpr).toString().equals(proveExpr.toString()))
				{
					this.storeprint(args);
					showTable.remove(myLineNumber.currentSuper());
					myTheoremSet.put(myLineNumber.currentSuper(), showExpr);
					if(showTable.size()!=0)
					{
						myLineNumber.layerUp();
					}
				}
				else
				{
					throw new IllegalInferenceException("***Invalid Inference: "+args[2]);
				}
			}
			else
			{
				throw new IllegalInferenceException("***Invalid Inference"+args[2]);
			}
		}
		if (command.equals("repeat"))
		{
			//Checks if given expression and repeated expression are equal
			//then modifies showtable and theorem set accordingly
			LinkedList<String> proveExpr = showTable.get(myLineNumber.currentSuper());
			LinkedList<String> showExpr = (new Expression(args[2])).Queue;
			if (!proveExpr.equals(showExpr)){
				throw new IllegalInferenceException("***Repeated expression doesn't match unproven show: "+ args[2]);
			}
			showTable.remove(myLineNumber.currentSuper());
			myTheoremSet.put(myLineNumber.currentSuper(), showExpr);
			this.storeprint(args);
			myTheoremSet.put(myLineNumber.toString(), myTheoremSet.myTheorems.get(args[1]));
			myLineNumber.step();
		}
		if (command.equals("print"))
		{
			//prints stored printList
			for (int i=0;i<printList.size();i++){
				System.out.println(printList.get(i));
			}
		}
		else if (this.myTheoremSet.get(command) != null)
		{
			//checks imported stuff for given command, then handles it
			if (checkTheoremEquivalence((LinkedList<String>) myTheoremSet.get(command).clone(), new Expression(args[1]).Queue))
			{
				this.storeprint(args);
				if(showTable.get(myLineNumber.currentSuper()).toString().equals((new Expression(args[1])).Queue.toString()))
				{
					myTheoremSet.myTheorems.put(myLineNumber.currentSuper(), showTable.get(myLineNumber.currentSuper()));
					showTable.remove(myLineNumber.currentSuper());
					if(showTable.size()!=0)
					{
						myLineNumber.layerUp();
					}
				}
				else
				{
					this.myTheoremSet.put(this.myLineNumber.toString(), new Expression(args[1]));
					myLineNumber.step();
				}
				operands = new Hashtable<String,String>();
			}
			else
			{
				throw new IllegalInferenceException(
						"***Invalid Inference, the provided theorem " +
						"is not equivalent to stored theorem of same name: " + command);
			}
		}
	}

	public void storeprint(String[] args){
		//adds to printList
		String output= myLineNumber.toString();
		for (int i = 0;i<args.length;i++){
			output+=" "+args[i];
		}
		this.printList.add(output);
	}

	private boolean mpChecker(LinkedList<String>left,LinkedList<String>middle, LinkedList<String>consequent)
	{
		//verifies logic for mp
		LinkedList<String> fullExpression;
		LinkedList<String> predicate;


		if (left.size() > middle.size())
		{
			fullExpression = left;
			predicate = middle;
		}
		else
		{
			fullExpression = middle;
			predicate = left;
		}
		if (ProofChecker.iAmDebugging){
		System.out.println(fullExpression.toArray().toString());
		System.out.println(predicate.toArray().toString());
		}
		if (fullExpression.pop().equals("=>"))
		{
			String fullBuff = "";

			//check predicate matches left side of full expression
			for(int i=0; i < predicate.size();i++)
			{
				try
				{
					fullBuff = fullExpression.pop();
					assert predicate.pop().equals(fullBuff);
				}
				catch (Exception e)
				{
					return false;
				}
			}

			//check consequent matches right side of full expression
			for(int i=0; i < consequent.size();i++)
			{
				try
				{
					fullBuff = fullExpression.pop();
					assert consequent.pop().equals(fullBuff);
				}
				catch (Exception e)
				{
					return false;
				}
			}

			try
			{
				assert fullExpression.size()==0;
				return true;
			}
			catch (Exception e)
			{
				return false;
			}
			
		}
		return false;
		
	}

	private boolean mtChecker(LinkedList<String>left,LinkedList<String>middle, LinkedList<String>consequent)
	{
		//verifies for mt
		filterTildes(left);
		filterTildes(middle);
		filterTildes(consequent);
		
		if(ProofChecker.iAmDebugging){
		System.out.println(left.toString());
		System.out.println(middle.toString());
		System.out.println(consequent.toString());
		}
		
		LinkedList<String> fullExpression;
		LinkedList<String> predicate;

		if (left.size() > middle.size())
		{
			fullExpression = left;
			predicate = middle;
		}
		else
		{
			fullExpression = middle;
			predicate = left;
		}

		if (fullExpression.pop().equals("=>"))
		{	
			if (ProofChecker.iAmDebugging){
			System.out.println(middle.toString());
			}
			String fullBuff = "";

			//check consequent matches left side of full expression, but has tilda
			if(!consequent.peek().equals("~"))
			{
				return false;
			}
			consequent.pop();

			for(int i=0; i < consequent.size();i++)
			{

				try
				{
					fullBuff = fullExpression.pop();
					assert consequent.pop().equals(fullBuff);
				}
				catch (Exception e)
				{
					return false;
				}
			}

			//check predicate matches right side of full expression, but has tilda
			if(!predicate.peek().equals("~"))
			{
				return false;
			}
			predicate.pop();

			for(int i=0; i < predicate.size();i++)
			{

				try
				{
					fullBuff = fullExpression.pop();
					assert predicate.pop().equals(fullBuff);
				}
				catch (Exception e)
				{
					return false;
				}
			}
			
			try
			{
				assert fullExpression.size()==0;
				return true;
			}
			catch (Exception e)
			{
				return false;
			}
			
		}
		return false;
	}
	
	private boolean checkTheoremEquivalence( LinkedList<String> storedTheoremQueue, LinkedList<String> inputTheoremQueue) {
		//checks if theorems are equivalent despite different Expression Names
		//Base Case
			if (storedTheoremQueue.size() == 0 && inputTheoremQueue.size() == 0)
			{
				return true;
			}
			if (storedTheoremQueue.size() == 0 && inputTheoremQueue.size() != 0)
			{
				return false;
			}
			if (storedTheoremQueue.size() != 0 && inputTheoremQueue.size() == 0)
			{
				return false;
			}
		
		if (storedTheoremQueue.peek().equals("=>")&&
				inputTheoremQueue.peek().equals("=>"))
		{
			storedTheoremQueue.pop();
			inputTheoremQueue.pop();
			return checkTheoremEquivalence(storedTheoremQueue,inputTheoremQueue);
		}
		if (storedTheoremQueue.peek().equals("&")&&
				inputTheoremQueue.peek().equals("&"))
		{
			storedTheoremQueue.pop();
			inputTheoremQueue.pop();
			return checkTheoremEquivalence(storedTheoremQueue,inputTheoremQueue);
		}
		if (storedTheoremQueue.peek().equals("|")&&
				inputTheoremQueue.peek().equals("|"))
		{
			storedTheoremQueue.pop();
			inputTheoremQueue.pop();
			return checkTheoremEquivalence(storedTheoremQueue,inputTheoremQueue);
		}
		if (storedTheoremQueue.peek().equals("~")&&
				inputTheoremQueue.peek().equals("~"))
		{
			storedTheoremQueue.pop();
			inputTheoremQueue.pop();
			return checkTheoremEquivalence(storedTheoremQueue,inputTheoremQueue);
		}
		else 
		{
			//Finds Left and Right Operand

			String storedOperand = storedTheoremQueue.pop();
			String inputOperand = inputTheoremQueue.pop();
			
			if(inputOperand.equals("&") || inputOperand.equals("|") || inputOperand.equals("=>") || inputOperand.equals("~"))
			{
				int numberOfOperations = 2;
				if(inputOperand.equals("~"))
				{
					numberOfOperations--;
				}
				while(numberOfOperations != 0)
				{

					String currentStr = inputTheoremQueue.pop();
					if(currentStr.equals("=>"))
					{
						numberOfOperations++;
					}
					if(currentStr.equals("&"))
					{
						numberOfOperations++;
					}
					if(currentStr.equals("|"))
					{
						numberOfOperations++;
					}
					else if(!currentStr.equals("~"))
					{
						numberOfOperations--;
					}
					inputOperand+=currentStr;
				}
			}
			if (ProofChecker.iAmDebugging){
			System.out.println(storedOperand);
			System.out.println(inputOperand);
			}
			if (this.operands.get(storedOperand) != null)
			{
				if (operands.get(storedOperand).equals(inputOperand))
				{
					return checkTheoremEquivalence(storedTheoremQueue,inputTheoremQueue);
				}
				return false;
			}
			else
			{
				this.operands.put(storedOperand, inputOperand);
			}
			return checkTheoremEquivalence(storedTheoremQueue,inputTheoremQueue);
		}
		
	}
	
	private void filterTildes(LinkedList<String> queue) {
		//handles multiple tildes
		
		if (queue.size() > 2)
		{
			if(queue.peekFirst().equals("~") && 
					queue.get(1).equals("~")) 
			{
				queue.pop();
				queue.pop();
				filterTildes(queue);
			}
		}
	}
		
	public LinkedList<String> findAssumption(LinkedList<String> Queue)
	{
		/* Takes in Queue expressing and Expression
		 * returns a Queue of the Left Operand of the Expressiong
		 *  
		 */
		LinkedList<String> rtnQueue = new LinkedList<String>();
		int numberOfOperands = 1;
		int i=1;
		while(numberOfOperands != 0)
		{
			String currentStr = Queue.get(i);
			if(currentStr.equals("=>"))
			{
				numberOfOperands++;
			}
			else if(currentStr.equals("&"))
			{
				numberOfOperands++;
			}
			else if(currentStr.equals("|"))
			{
				numberOfOperands++;
			}
			else if(!currentStr.equals("~"))
			{
				numberOfOperands--;
			}
			rtnQueue.add(currentStr);
			i++;
		}
		return rtnQueue;
	}

	public LinkedList<String> findConsequent(LinkedList<String> Queue)
	{
		int numberOfOperands = 1;
		int i = 1;

		while(numberOfOperands != 0)
		{
			String currentStr = Queue.get(i);
			if(currentStr.equals("=>"))
			{
				numberOfOperands++;
			}
			else if(currentStr.equals("&"))
			{
				numberOfOperands++;
			}
			else if(currentStr.equals("|"))
			{
				numberOfOperands++;
			}
			else if(!currentStr.equals("~"))
			{
				numberOfOperands--;
			}
			i++;
		}

		LinkedList<String> rtnQueue = new LinkedList<String>();
		numberOfOperands = 1;

		while(numberOfOperands != 0)
		{
			String currentStr = Queue.get(i);
			if(currentStr.equals("=>"))
			{
				numberOfOperands++;
			}
			else if(currentStr.equals("&"))
			{
				numberOfOperands++;
			}
			else if(currentStr.equals("|"))
			{
				numberOfOperands++;
			}
			else if(!currentStr.equals("~"))
			{
				numberOfOperands--;
			}
			rtnQueue.add(currentStr);
			i++;
		}

		return rtnQueue;
	}
		
	public boolean contradiction(LinkedList<String> first, LinkedList<String> second)
	{
		int numLeadingTildas;
		
		if (first.peek().equals("~") && second.peek().equals("~"))
		{
			first.pop();
			second.pop();
			return contradiction(first,second);
		}
		else if (first.peek().equals("~"))
		{
			first.pop();
			return contradictionHelper(first, second);
		}
		else if (second.peek().equals("~"))
		{
			second.pop();
			return contradictionHelper(first, second);
		}
		return false;
	}

	public boolean contradictionHelper(LinkedList<String> first, LinkedList<String> second)
	{			
		while(true)
		{
			String firstStr = first.pop();
			String secondStr = second.pop();
			if(!first.isEmpty())
				while(firstStr.equals("~"))
				{
					if(first.peek().equals("~"))
					{
						first.pop();
						firstStr = first.pop();
					}
					else
					{
						break;
					}
				}
			if(!second.isEmpty())
			{
				while(secondStr.equals("~"))
				{
					if(second.peek().equals("~"))
					{
						second.pop();
						secondStr = second.pop();
					}
					else
					{
						break;
					}
				}
			}
			if(!firstStr.equals(secondStr))
			{
				return false;
			}
			if(first.size() == 0 || second.size()==0)
			{
				if(first.size() == 0 && second.size()==0)
				{
					return true;
				}
				else
				{
					return false;
				}
			}
		}
	}
}
