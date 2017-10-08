/*
  * By Adam Jacobs
    October 2017

  * This file contains the predicate verify that takes an input file
    name as argument and then verifies if a natural deduction proof is correct.

  * Available connectives and rules can be
    found in this file if you take a look.

  * The input file has the following format:

    1. The first row is a list is of premises
    2. second row the goal
    3. the next rows contains the proof itself. See example.

  * Here is an example of a valid proof for the
  sequent neg(neg( p -> neg(p) )) |- neg(p) is valid:

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

*/

% connectives
neg(A) :- \+ A.
imp(A, B) :- neg(A , neg(B)). % A -> B logically equivalent to neg(A and neg(B))
and(A,B) :- A, B.
or(A, B) :- A ; B.

last(X,[X]).
last(X, [_|T]) :- last(X, T).

% read input and verify if proof is okay.
verify(InputFileName) :-
  see(InputFileName),
  read(Prems), read(Goal), read(Proof),
  seen, !,
  %last(WantedGoal, Proof), Goal == WantedGoal, !, % check that goal is in last row
  valid_proof(Prems, Goal, Proof, []), !.

/*
  valid_proof(Prems, Goal, Proof, Knowledge)
  Prems: premisses, g
  Goal: what we want to prove,
  Proof: Each row of the natural deduction proof
  knowledge = rows that has been proven in proof
*/
% base case: evalute to true if the last row is valid based
% on the knowlege and premisses we have and formula unifies with our goal.
valid_proof(Prems, Goal, [[RowNum, Goal, Rule]], Knowledge) :-
  valid_rule(Prems, [RowNum, Goal, Rule], Knowledge), !.

% if the current row is a box that starts with an assumption it recursively
% be treated as a proof itself. The Goal of the box will be the formula in last row inside it.
valid_proof(Prems, Goal, [ [[RowStart,AssumFormula,assumption]|RestOfBox] |Rest], Knowledge) :-
  % take out last element in box at set its formula as the goal for the recursive box proof
  last([RowGoal,GoalFormula, GoalRule],[[RowStart,AssumFormula,assumption]|RestOfBox]),
  % make sure proof inside box is valid
  valid_proof([AssumFormula|Prems], GoalFormula, [ [RowStart,AssumFormula,premise]|RestOfBox ], Knowledge),
  % if box is valid then append the box with its first and last row to Knowledge. If only one row in box then take that row as first and last
  valid_proof(Prems, Goal, Rest, [[ [RowStart,AssumFormula,assumption],[RowGoal,GoalFormula, GoalRule] ]|Knowledge]).

% recursion: see if the current row is valid based on premisses and collected knowledge
valid_proof(Prems, Goal, [ProofHead|ProofTail], Knowledge) :-
  valid_rule(Prems, ProofHead, Knowledge),
  % if row is valid then add to Knowledge
  valid_proof(Prems, Goal, ProofTail, [ProofHead|Knowledge]).

/*
valid_rule(Prems, ProofRow, Rule)
valid_rule(Prems, [RowNum, Formula, Rule], Knowledge)
This predicate contains all the rules that this program can check
and also the built functionality for "boxes" with assumptions at the top.
All the connectives used here can be found at the top of this file.
*/

% PREMISE: if Formula is member of the premise list
valid_rule(Prems, [_, Formula, premise], _) :- member(Formula, Prems).

% ANDINT: and introduction with formula A and B at row X and Y
valid_rule(_, [_, and(A,B), andint(X,Y)], Knowledge) :-
  member([X, A, _], Knowledge),
  member([Y, B, _], Knowledge).

% ANDEL1: and elimination 1 for formula A with and(A,_) at row X
valid_rule(_, [_, A, andel1(X)], Knowledge) :-
  member([X, and(A,_), _], Knowledge).

% ANDEL2: and elim 2 for formula B with and(_,B) at row X
valid_rule(_, [_, B, andel2(X)], Knowledge) :-
  member([X, and(_,B), _], Knowledge).

% ORINT1: or introduction 1 for formula or(A,_) where A is at row X
valid_rule(_, [_, or(A,_), orint1(X)], Knowledge) :-
  member([X, A, _], Knowledge).

% ORINT2: or introduction 2 for formula or(_,B) where B is at row X or in premisses
valid_rule(_, [_, or(_,B), orint2(X)], Knowledge) :-
  member([X, B, _], Knowledge).

% IMPEL: implication elimination for formula Q where you have P at row X and P->Q at row Y
valid_rule(_, [_, Q, impel(X,Y)], Knowledge) :-
  member([X, P, _], Knowledge),
  member([Y, imp(P,Q), _], Knowledge).

% LEM: or(P, neg(P)) for any formula P. Lem is valid so this predicate will always be true
valid_rule(_, [_, or(P,neg(P)), lem], _).

% NEGNEGEL: double negation elimination for P where you have neg(neg(P)) at row X
valid_rule(_, [_, P, negnegel(X)], Knowledge) :-
  member([X, neg(neg(P)), _], Knowledge).

% NEGNEGINT: double negation introduction for neg(neg(P)) where you have P at row X.
valid_rule(_, [_, neg(neg(P)), negnegint(X)], Knowledge) :-
  member([X, P, _], Knowledge).

% MT: modus tempus for neg(P) where you have P->Q at row X and neg(Q) at row Y
valid_rule(_, [_, neg(P), mt(X,Y)], Knowledge) :-
  member([X, imp(P,Q), _], Knowledge),
  member([Y, neg(Q), _], Knowledge).

% NEGEL: negation elimination for contradiction cont where you have P at row X and neg(P) at row Y
valid_rule(_, [_, cont, negel(X,Y)], Knowledge) :-
  member([X, P, _], Knowledge),
  member([Y, neg(P), _], Knowledge).

% CONTEL: contradiction elimination for any formula where you have a contradiction cont at row X.
valid_rule(_, [_, _, contel(X)], Knowledge) :-
  member([X, cont, _], Knowledge).


% OREL: or elimination for C where you have a or(A,B) at row X and two boxes where both concludes to C
valid_rule(_, [_, C, orel(X,Y,U,V,W)], Knowledge) :-
  member([X, or(A,B), _], Knowledge),
  member([ [Y, A, assumption], [U, C, _] ], Knowledge),
  member([ [V, B, assumption], [W, C, _] ], Knowledge).

% IMPINT: implication introduction, introduce a A->B if there is a box where you get B from A.
valid_rule(_, [_, imp(A,B), impint(X,Y)], Knowledge) :-
  member([ [X, A, assumption], [Y, B, _] ], Knowledge).

% NEGINT: negation introduction, introduce a neg(P) if there is a box at row X that assumes P and gets a contradiction at row Y
valid_rule(_, [_, neg(P), negint(X,Y)], Knowledge) :-
  member([ [X, P, assumption], [Y, cont, _] ], Knowledge).

% PBC: get P if there is a box that assumes neg(P) at row X and gets a contradiction at row Y
valid_rule(_, [_, P, pbc(X,Y)], Knowledge) :-
  member([ [X, neg(P), assumption], [Y, cont, _] ], Knowledge).

% TODO: fix correct copy!!! Needs to be in same box or above. Can not be from external separate box
% COPY: copy formula P from row X
valid_rule(_,[_, P, copy(X)] , Knowledge) :-
  member([X, P, _], Knowledge).
