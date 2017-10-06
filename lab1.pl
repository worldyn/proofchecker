/* connectives and rules */
/*[neg(neg(imp(p, neg(p))))].

neg(p).

[
  [1, neg(neg(imp(p,neg(p)))), premise ],
  [2, imp(p, neg(p)), negnegel(1)],
  [
    [3, p, assumption ],
    [4, neg(p), impel(3,2) ],
    [5, cont, negel(3,4) ]
  ],
  [6, neg(p), negint(3,5)]
].*/

% connectives
neg(A) :- \+ A.
imp(A, B) :- neg(A , neg(B)). % A -> B logically equivalent to not(A and not(B))
and(A,B) :- A, B.
or(A, B) :- A ; B.

last(X,[X]).
last(X, [_|T]) :- last(X, T).

% read input and verify if proof is okay.
verify(InputFileName) :-
  see(InputFileName),
  read(Prems), read(Goal), read(Proof),
  seen,
  %last(WantedGoal, Proof), Goal == WantedGoal, % check that goal is in last row
  valid_proof(Prems, Goal, Proof, []).

valid_proof(Prems, Goal, [RowNum, Goal, Rule], Knowledge) :-
  valid_rule(Prems, [RowNum, Goal, Rule], Knowledge).
valid_proof(Prems, Goal, [ProofHead|ProofTail], Knowledge) :-
  valid_rule(Prems, ProofHead, Knowledge),
  valid_proof(Prems, Goal, ProofTail, Knowledge).

/*
Rules for the proofs
valid_rule(Prems, ProofRow, Rule)
valid_rule(Prems, [RowNum, Formula, Rule], Knowledge)
*/

% premise if Formula is member of the premises
valid_rule(Prems, [_, Formula, premise], _) :- member(Formula, Prems).
% assumption can be anything
valid_rule(_, [_, _, assumption], _).
