# proofchecker
By Adam Jacobs, October 2017.
Check if a natural deduction proof is valid


# The Verify predicate
This file contains the predicate 'verify' that takes an input file
name as argument and then verifies if a natural deduction proof in it is correct.
The file contains a sequent and proof for that sequent. This program will
verify the correctness of the proof.

# Available connectives and rules
Available connectives and proof rules can be found in the lab1.pl file, at the top.

# The input files format
  1. The first row is a list is of premises
  2. second row the goal/conclusion of the proof.
  3. the next rows contains the proof itself. 
  
# See example of valid and invalid proofs in the /tests/ folder.
