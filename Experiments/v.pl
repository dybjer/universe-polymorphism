% swipl, may run with other prologs as well; toy examples: ./xyz*.in
% run with "test(file)." where "file" is an input file name without ".in"

% finds a model in [0..99999] assuming infty = 99999
% code can easily be adapted to GMP and a formal +infty

% syntax
:-op(1199, xfx, =>).

% vars/1 refers to the variables in the input file with clauses Sup => Var

% get/2 and put/2 refer to the hash table frontier, STATEFUL

init_frontier(N):- vars(Vars),forall(member(Var,Vars),put(Var,N)).
init_frontier(X,N):- forall(member(Var,X),put(Var,N)).

% activated/3 tests whether Sup => Var is on X and tries to improve Var

activated(V,W,Sup,Var):- 
  member(Var,W)->
  based_on(V,Sup)->
  surplus(Sup,99999,M),
  get(Var,N),N<M,put(Var,M).

based_on(X,Sup):- forall(member(T,Sup),
  (T=V+_ -> member(V,X);
  (T=V-_ -> member(V,X);
            member(T,X)))).

surplus([],Accumulator,Accumulator).
surplus([T|Ts],Sold,Snew):- 
  (T=V+O -> (get(V,N),Smid is min(Sold,N-O)) ;
  (T=V-O -> (get(V,N),Smid is min(Sold,N+O)) ;
            (get(T,N),Smid is min(Sold,N)))),
  surplus(Ts,Smid,Snew).

improve(V,W):- setof(Var,Sup^((Sup=>Var),activated(V,V,Sup,Var)),W).

main:- vars(Vraw),sort(0,@=<,Vraw,V),main(V).

main(V):- improve(V,W) -> main(V,W) ; print_model.

main(V,W):-
  V=W -> init_frontier(V,99999) ;
  main(W), \+ improve(V,W).


step(Count,N):-
  Count>=N -> print_maxgap;
  once(((Sup => Var),
  (true -> get(Var,M),put(Var,M+1),step(Count+1,N)))).

step(_,_):- print_model.


%%%%%%%avoid reading this block with silly auxiliaries%%%%%%%


% hash table
:-dynamic frontier/2.
get(Var,N) :- once(frontier(Var,N)).
put(Var,N) :- retract(frontier(Var,_)) -> M is N, asserta(frontier(Var,M))
                                        ; M is N, asserta(frontier(Var,M)).
cleanup :-  retractall(frontier(_,_)).

% pretty printing

sort_frontier(F) :- bagof((Var,N),frontier(Var,N),Fu), sort(2,@>=,Fu,F).

print_model :- sort_frontier([(Vm,Max)|F]),
               bagof((Var,Val),N^(member((Var,N),[(Vm,Max)|F]),Val is Max-N),Model),
               nl,write(model),nl,write(Model).

print_maxgap :- sort_frontier([(Vm,Max)|F]), Fs=[(Vm,Max)|F],
                bagof(N,(between(0,Max,N), \+frontier(_,N)),Gaps), 
                reverse(Gaps,[MaxGap|_]),
                forall((member((Var,N),Fs),N>MaxGap),(write(((Var,N))),nl)),
                write(gap),nl,
                forall((member((Var,N),Fs),N<MaxGap),(write(((Var,N))),nl)).

% io
ext(F,E,FE):- atom_concat(F,'.',F1),atom_concat(F1,E,FE).

test(File):- ext(File,in,Fi),cleanup,[Fi],test,nl.

% not used yet
%io(Dest,Mode,Name,DO):-open(Dest,Mode,_,[alias(Name)]),
%       (Mode=write->set_output(Name);set_input(Name)),DO,close(Name).
%out(Fi):-ext(Fi,out,Fo),io(Fo,write,out,test(Fi)).

