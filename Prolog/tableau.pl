?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow,
notimp, notrevimp]).
memberr(X, [Y | _]) :-
    X == Y.
memberr(X, [Y | Tail]) :-
    X \== Y,
    memberr(X, Tail).
remove(_, [], []).
remove(X, [Y|Tail], Newtail) :-
    X == Y,
    remove(X, Tail, Newtail).
remove(X, [Y | Tail], [Y | Newtail]) :-
    X \== Y,
    remove(X, Tail, Newtail).

/* conjunctive(X) :- X is an alpha formula.
*/
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

/* disjunctive(X) :- X is a beta formula.
*/
disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

/* unary(X) :- X is a double negation,
or a negated constant.
*/
unary(neg neg _).
unary(neg true).
unary(neg false).

/* binary_operator(X) :- X is a binary operator.
 */

binary_operator(X) :-
    member(X, [and, or, imp, revimp, uparrow, downarrow,
    notimp, notrevimp]).

/* components(X, Y, Z) :- Y and Z are the components of
formula X, as defined in the alpha and beta table.
*/
components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

/* component(X, Y) :- Y is the component of the
unary formula X.
*/
component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* universal(X) :- X is a gamma formula.
 */
universal(all(_,_)).
universal(neg some(_,_)).

/* existential(X) :- X is a delta formula.
 */
existential(some(_,_)).
existential(neg all(_,_)).

/* literal(X) :- X is a literal
 */
literal(X) :-
    not(conjunctive(X)),
    not(disjunctive(X)),
    not(unary(X)),
    not(universal(X)),
    not(existential(X)).

/* atomicfmla(X) :- X is an atomic formula.
 */
atomicfmla(X) :-
    literal(X),
    X \= neg _.

/* sub(Term, Variable, Formula, Newformula) :-
 *  Newformula is the result of substitutinf occurrences of Term for
 *  each free occurrence of Variable in Formula.
 */
sub(Term, Variable, Formula, Newformula) :-
    sub_(Term, Variable, Formula, Newformula), !.
sub_(Term, Var, A, Term) :- Var == A.
sub_(_, _, A, A) :- atomic(A).
sub_(_, _, A, A) :- variable(A).
sub_(Term, Var, neg X, neg Y) :-
    sub_(Term, Var, X, Y).
sub_(Term, Var, Binary_One, Binary_Two) :-
    binary_operator(F),
    Binary_One =.. [F, X, Y],
    Binary_Two =.. [F, U, V],
    sub_(Term, Var, X, U),
    sub_(Term, Var, Y, V).
sub_(_, Var, all(Var, Y), all(Var, Y)).
sub_(Term, Var, all(X, Y), all(X, Z)) :-
    sub_(Term, Var, Y, Z).
sub_(_, Var, some(Var, Y), some(Var, Y)).
sub_(Term, Var, some(X, Y), some(X, Z)) :-
    sub_(Term, Var, Y, Z).
sub_(Term, Var, Functor, Newfunctor) :-
    Functor =.. [F | Arglist],
    sub_list(Term, Var, Arglist, Newarglist),
    Newfunctor =.. [F | Newarglist].

sub_list(Term, Var, [Head | Tail], [Newhead | Newtail]) :-
    sub_(Term, Var, Head, Newhead),
    sub_list(Term, Var, Tail, Newtail).
sub_list(_, _, [], []).

/* instance(F, Term, Ins) :-
 *  F is a quantified formula, and Ins is the result of removing the
 *  quantifier and replacing all free occurrences of the quantified
 *  variable by occurrences of Term.
 */
instance(all(X,Y), Term, Z) :- sub(Term, X, Y, Z).
instance(neg some(X,Y), Term, neg Z) :- sub(Term, X, Y, Z).
instance(some(X,Y), Term, Z) :- sub(Term, X, Y, Z).
instance(neg all(X,Y), Term, neg Z) :- sub(Term, X, Y, Z).

/* funcount(N) :- N is the current Skolen function index.
 */
:- dynamic funcount/1.
funcount(1).

/* newfuncount(N) :-
 *  N is the current Skolem function index, and as a side effect, the
 *  remembered value is incremented.
 */
newfuncount(N) :-
    funcount(N),
    retract(funcount(N)),
    M is N+1,
    assert(funcount(M)).

/* reset :- the Skolem function index is reset to 1.
 */
reset :-
    retract(funcount(_)),
    assert(funcount(1)),
    !.

/* skp_fun(X, Y) :-
 *  X is a list of free variables, and Y is a previously unused Skolem
 *  function symbol applied to those free variables.
 */
sko_fun(Varlist, Skoterm) :-
    newfuncount(N),
    Skoterm =.. [fun | [N | Varlist]].

/* notation(Notated, Free) :-
 *  Notated is a notated formula, and Free is its associated free
 *  variable list.
 */
notation(n(X, _), X).

/* fmla(Notated, Formula) :-
 *  Notated is a notated formula, and Formula is its formula part.
 */
fmla(n(_, Y), Y).

/* singlestep(OldTableau, OldQdepth, NewTableau, NewQdepth) :-
 *  the application of one tableau rule to OldTableau, with a Q-depth of
 *  OldQdepth, will produce the tableau NewTableau, and will change the
 *  available Q-depth to NewQdepth.
 */
singlestep([OldBranch | Rest], Qdepth, [NewBranch | Rest], Qdepth) :-
    member(NotatedFormula, OldBranch),
    notation(NotatedFormula, Free),
    fmla(NotatedFormula, Formula),
    unary(Formula),
    component(Formula, NewFormula),
    notation(NewNotatedFormula , Free),
    fmla(NewNotatedFormula, NewFormula),
    remove(NotatedFormula, OldBranch, TempBranch),
    NewBranch = [NewNotatedFormula | TempBranch],
    write('used unary on '),
    print(Formula),
    nl.

singlestep([OldBranch | Rest], Qdepth, [NewBranch | Rest], Qdepth) :-
    member(NotatedAlpha, OldBranch),
    notation(NotatedAlpha, Free),
    fmla(NotatedAlpha, Alpha),
    conjunctive(Alpha) ,
    components(Alpha, AlphaOne, AlphaTwo),
    notation(NotatedAlphaOne, Free),
    fmla(NotatedAlphaOne, AlphaOne),
    notation(NotatedAlphaTwo, Free),
    fmla(NotatedAlphaTwo, AlphaTwo),
    remove(NotatedAlpha, OldBranch, TempBranch),
    NewBranch = [NotatedAlphaOne, NotatedAlphaTwo | TempBranch],
    write('used alpha on '),
    print(Alpha),
    nl.

singlestep([OldBranch | Rest], Qdepth, [NewBranchOne, NewBranchTwo | Rest], Qdepth) :-
    member(NotatedBeta, OldBranch),
    notation(NotatedBeta, Free),
    fmla(NotatedBeta, Beta),
    disjunctive(Beta),
    components(Beta, BetaOne, BetaTwo),
    notation(NotatedBetaOne, Free),
    fmla(NotatedBetaOne, BetaOne),
    notation(NotatedBetaTwo, Free),
    fmla(NotatedBetaTwo, BetaTwo),
    remove(NotatedBeta, OldBranch, TempBranch),
    NewBranchOne = [NotatedBetaOne | TempBranch],
    NewBranchTwo = [NotatedBetaTwo | TempBranch],
    write('used beta on '),
    print(Beta),
    nl.

singlestep([OldBranch | Rest], Qdepth, [NewBranch | Rest], Qdepth) :-
    member(NotatedDelta, OldBranch),
    notation(NotatedDelta, Free),
    fmla(NotatedDelta, Delta),
    existential(Delta) ,
    sko_fun(Free, Term),
    instance(Delta, Term, Deltalnstance),
    notation(NotatedDeltalnstance, Free),
    fmla(NotatedDeltalnstance, Deltalnstance),
    remove(NotatedDelta, OldBranch, TempBranch),
    NewBranch = [NotatedDeltalnstance | TempBranch],
    write('used delta on '),
    print(Delta),
    nl.

singlestep([OldBranch | Rest], OldQdepth, NewTree, NewQdepth) :-
    member(NotatedGamma, OldBranch),
    notation(NotatedGamma, Free),
    fmla(NotatedGamma, Gamma),
    universal(Gamma) ,
    OldQdepth > 0,
    remove(NotatedGamma, OldBranch, TempBranch),
    NewFree = [v(V) | Free],
    instance(Gamma, v(V), Gammalnstance),
    notation(NotatedGammalnstance, NewFree),
    fmla(NotatedGammalnstance, Gammalnstance),
    append([NotatedGammalnstance | TempBranch],
           [NotatedGamma], NewBranch),
    append(Rest , [NewBranch], NewTree),
    NewQdepth is OldQdepth-1,
    write('used gamma on '),
    print(Gamma),
    nl.

singlestep([Branch | OldRest], OldQdepth, [Branch | NewRest], NewQdepth) :-
    singlestep(OldRest, OldQdepth, NewRest, NewQdepth).

/* expand(Tree, Qdepth, Newtree) :-
 *  the complete expansion of the tableau Tree, allowing Qdepth
 *  applications of the gamma rule, is Newtree.
 */
expand(Tree, Qdepth, Newtree) :-
    singlestep(Tree, Qdepth, TempTree, TempQdepth),
    expand(TempTree, TempQdepth, Newtree).
expand(Tree, _, Tree).

/* variable (X) :- X is a free variable.
*/
variable(v(_)).

/* partialvalue(X, Env, y) :-
Y is the partially evaluated value of term X
in environment Env.
*/
partialvalue(X, Env, X) :-
    memberr([X, X], Env).
partialvalue(X, Env, Y) :-
    memberr([X,Z], Env),
    Z \== X,
    partialvalue(Z, Env, Y).
partialvalue(X, Env, X) :-
    not(memberr([X, _], Env)).

/* member(X, Y) :- X is a member of the list Y.

member(X, [X|-]).
member(X , [_|Y]):- member(X, Y).
*/
/* in(X, T, Env)
X occurs in term T, evaluated in environment Env.
*/
in(X, T, Env) :-
    partialvalue(T, Env, U),
    ( X == U;
    not(variable(U)), not(atomic(U)), infunctor(X, U, Env)
    ).
infunctor(X, U, Env) :-
    U =.. [_|L],
    inlist(X, L, Env).

inlist(X, [T|_], Env):-

   in(X, T, Env).

inlist(X, [_|L], Env):-
    inlist(X, L, Env).

/* unify(Term1, Term2, Env, Newenv) :-
Unifying Term1 and Term2 in environment Env
produces the new environment Newenv.
*/
unify(Term1, Term2, Env, Newenv) :-
    partialvalue(Term1, Env, Val1) ,
    partialvalue(Term2, Env, Val2) ,
    (
        (Val1 == Val2, Newenv = Env);
        (variable(Val1), not(in(Val1, Val2, Env)) ,
         not(memberr([Val1,_],Env)), not(Val1==Val2),
         Newenv=[ [Val1, Val2] | Env] );
        (variable(Val2), not(in(Val2, Val1, Env)) ,
         not(memberr([Val2,_],Env)), not(Val1==Val2),
         Newenv=[ [Val2, Val1] | Env] );
        (not(variable(Val1)), not(variable(Val2)),
         not(atomic(Val1)), not(atomic(Val2)),
         unifyfunctor(Val1, Val2, Env, Newenv))
    ).

/* unifyfunctor(Fun1, Fun2, Env, Newenv) :-
Unifying the functors Fun1 and Fun2 in
environment Env produces environment Newenv.
*/
unifyfunctor(Fun1, Fun2, Env, Newenv):-
    Fun1 =.. [FunSymb | Args1],
    Fun2 =.. [FunSymb | Args2],
    unifylist(Args1, Args2, Env, Newenv).

/* unifylist(List1, List2, Env, Newenv)
Starting in environment Env and
unifying each term in List1 with the
corresponding term in List2 produces
the environment Newenv.
*/
unifylist([ ], [], Env, Env).
unifylist([Head1 | Tail1], [Head2 | Tail2], Env, Newenv):-
    unify(Head1, Head2, Env, Temp),
    unifylist(Tail1, Tail2, Temp, Newenv).

/* unify (Term1, Term2) :-
Term1 and Term2 are unified with the occurs check.
See Sterling and Shapiro, The Art of Prolog.
*/
unify(X, Y):-
    var(X) , var(Y), X=Y.
unify(X , Y) :-
    var(X), nonvar(Y), not_occurs_in(X,Y), X=Y.
unify(X,Y) :-
    var(Y), nonvar(X), not_occurs_in(Y,X), Y=X.
unify(X,Y) :-
    nonvar(X) , nonvar(Y), atomic(X), atomic(Y), X=Y.
unify(X, Y) :-
    nonvar(X), nonvar(Y),
    compoundd(X) , compoundd(Y),
    term_unify(X,Y).

not_occurs_in(X,Y):-
    var(Y), X \== Y.
not_occurs_in(_,Y) :-
    nonvar(Y), atomic(Y).
not_occurs_in(X,Y):-
    nonvar(Y), compoundd(Y), functor(Y,_,N),
    not_occurs_in(N,X,Y) .
not_occurs_in(N,X,Y) :-
    N>0, arg(N,Y,Arg), not_occurs_in(X,Arg), N1 is N-1,
    not_occurs_in(N1,X,Y) .
not_occurs_in(0,_,_).

term_unify(X,Y) :-
    functor(X,F,N), functor(Y,F,N), unify_args(N,X,Y).

unify_args(N,X,Y) :-
    N>0, unify_arg(N,X,Y), N1 is N-1, unify_args(N1,X,Y).
unify_args(0,_,_).

unify_arg(N,X,Y) :-
    arg(N,X,ArgX), arg(N,Y,ArgY), unify(ArgX,ArgY).

compoundd(X) :- functor(X,_,N), N>0.

/* closed(Tableau) :-
 *  every branch of Tableau can be made to contain a contradiction,
 *  after a suitable free variable substitution.
 */
closed([Branch | Rest]) :-
    member(Falsehood, Branch),
    fmla(Falsehood, false),
    closed(Rest).
closed([Branch | Rest]) :-
    member(NotatedOne, Branch),
    fmla(NotatedOne, X),
    atomicfmla(X),
    member(NotatedTwo, Branch),
    fmla(NotatedTwo, neg Y),
    unify(X, Y, [], _),!,
    closed(Rest).
closed([ ]).

/* if_then_else(P, Q, R) :- either P and Q, or not P and R.
*/
if_then_else(P, Q, _):- P,!,Q.
if_then_else(_, _, R) :- R.

/* test(X, Qdepth) :-
 *  create a complete tableau expansion for neg X, allowing Qdepth
 *  applications of the gamma rule. Test for closure.
 */
test(X, Qdepth) :-
    reset,
    notation(NotatedFormula, []),
    fmla(NotatedFormula, neg X),
    expand([[NotatedFormula]], Qdepth, Tree),
    !,
    if_then_else(closed(Tree), yes(Qdepth), no(Qdepth)).
yes(Qdepth) :-
    nl,
    write('First-order tableau theorem at Q-depth '),
    write(Qdepth),
    write(.),
    nl.
no(Qdepth) :-
    nl,
    write('Not a first-order tableau theorem at Q-depth '),
    write(Qdepth),
    write('.'),
    nl.
