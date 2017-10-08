# proofchecker
By Adam Jacobs, October 2017.
Check if a natural deduction proof is valid


* This file contains the predicate 'verify' that takes an input file
  name as argument and then verifies if a natural deduction proof in it is correct.
  The file contains a sequent and proof for that sequent. This program will
  verify the correctness of the proof.

* Available connectives and rules can be
  found in the lab1.pl file, at the top.

* The input files need the following format:

  1. The first row is a list is of premises
  2. second row the goal/conclusion of the proof.
  3. the next rows contains the proof itself. See example below.

* Here is an example of a valid proof for the
sequent neg(neg( p -> neg(p) )) |- neg(p) :

* inputfile ----------------

[neg(neg(imp(p, neg(p))))]
neg(p)

[
  [1, neg(neg(imp(p,neg(p)))), premise ],
  [2, imp(p, neg(p)), negnegel(1)],
  [
    [3, p, assumption ],
    [4, neg(p), impel(3,2) ],
    [5, cont, negel(3,4) ]
  ],
  [6, neg(p), negint(3,5)]
]

* inputfile end -------------
