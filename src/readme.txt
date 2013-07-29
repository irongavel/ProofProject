
General Explanation:

We decided to represent expressions as queues, or linkedLists<String> in the order of operations.
This can be more thouroughly illuminated in the test class for expression. Also, our expression class does not throw
any of it's own errors, instead, these errors are thrown in the linechecker method. Please do not penalize us for 
this design decision. Proofs are stored in a HashTable, and the scope is checked for every command possible.



TheoremSetTest:

Tests methods for putting and getting of expressions into and outof the TheoremSet

ProofTest:

These tests are not so much tests as they are markers for tested documents both given to us and created by us.

ExpressionTest:

This cluster of tests check to make sure that the expressions 
are being parsed in the expected way, from the top level down,
taking into account the various operations possible.

LineNumberTest:

Tests the methods in LineNumber to see if they operate as expected.

Description of individual contributions:

Derek Weinmuller[cs61bl-os]-

  Task management
	General planning and structural design
	coded on ReasonDelagation
	coded mt
	coded mp
	coded filterTildas
	coded on CheckTheoremEquivalence
	coded on ExpressionTest
	coded on extendProof 
	Navigated on most everything

Niko Gomez [cs61bl-or]-

  Programed Logic Stuff
  	coded Expression Class
  	coded MyTheoremSet
  	coded on ic
  	coded on co
  	coded on assume
  	coded on findAssumption
  	coded on findConsequent

Tohma Judge [cs61bl-pg]-
  Programmed Syntax Checking Stuff
  	Coded on repeat
  	Coded on show
  	Coded on print
  	Coded on assume
  	Coded String Splitter
  	Coded LineChecker
  	Coded LineScopeChecker
  	Coded ExpressionChecker
  	Coded on ExpressionTest
  	Coded TheoremSetTest
  	Coded LineNumberTest
  	

Ryan Davis [cs61bl-ot]-
