% swipl, may run with other prologs as well; toy examples: ./xyz*.in
% run with "test(file)." where "file" is an input file name without ".in"

% finds a model in [0..99999] assuming infty = 99999
% code can easily be adapted to GnuMultiPres and a formal +infty

% syntax
:-op(1199, xfx, =>).

% vars/1 refers to the variables in the input file with clauses Sup => Var

% get/2 and put/2 refer to the hash table frontier, STATEFUL !

init_frontier(N):- vars(Vars),forall(member(Var,Vars),put(Var,N)).
init_frontier(X,N):- forall(member(Var,X),put(Var,N)).

% try_improve/4 tries to improve Var with Sup => Var, Sup based on V, Var in W

try_improve(V,W,Sup,Var):- 
  member(Var,W)->
  based_on(V,Sup)->
  surplus(Sup,99999,M),
  get(Var,N),N<M,put(Var,M).

% based_on/2 checks whether X contains all variables occurring in Sup

based_on(X,Sup):- forall(member(T,Sup),
  (T=V+_ -> member(V,X);
  (T=V-_ -> member(V,X);
            member(T,X)))).

% surplus/3 computes the maximal upward shift of Sup
 
surplus([],Accumulator,Accumulator).
surplus([T|Ts],Sold,Snew):- 
  (T=V+O -> (get(V,N),Smid is min(Sold,N-O)) ;
  (T=V-O -> (get(V,N),Smid is min(Sold,N+O)) ;
            (get(T,N),Smid is min(Sold,N)))),
  surplus(Ts,Smid,Snew).

forward(V,W,Improved):- 
  setof(Var,Sup^((Sup=>Var),try_improve(V,W,Sup,Var)),Improved).

main:- vars(Vraw),sort(Vraw,V),main(V),print_model(V).

main(V):- forward(V,V,W) -> main(V,W) ; true.

main(V,W):- % precondition: W subset of V and both sorted
% write(V+W),nl, % check the precondition!
  V=W -> init_frontier(V,99999) ;
% the following line takes too long since \infty = 99999, see inf.in
  once((repeat, main(W), /* until */ \+forward(V,W,_))),
  subtract(V,W,VminW),
  (forward(V,VminW,I) -> oset_union(W,I,WuI),main(V,WuI); true).


%%%%%%%avoid reading this block with silly auxiliaries%%%%%%%


% hash table
:-dynamic frontier/2.
get(Var,N) :- once(frontier(Var,N)).
put(Var,N) :- retract(frontier(Var,_)) -> M is N, asserta(frontier(Var,M))
                                        ; M is N, asserta(frontier(Var,M)).
cleanup :-  retractall(frontier(_,_)).

% pretty printing

sort_frontier(F) :- bagof((Var,N),frontier(Var,N),Fu), sort(2,@=<,Fu,F).

print_model(W) :- sort_frontier(F),
                  bagof((Var=Val),(member((Var,Val),F),member(Var,W)),Model),
                  nl,write(model),nl,write(Model).

% io
ext(F,E,FE):- atom_concat(F,'.',F1),atom_concat(F1,E,FE).

test(File):- ext(File,in,Fi),cleanup,[Fi],init_frontier(0),main,nl.

% not used yet
%io(Dest,Mode,Name,DO):-open(Dest,Mode,_,[alias(Name)]),
%       (Mode=write->set_output(Name);set_input(Name)),DO,close(Name).
%out(Fi):-ext(Fi,out,Fo),io(Fo,write,out,test(Fi)).

