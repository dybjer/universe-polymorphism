% swipl, may run with other prologs as well; toy examples: ./xyz*.in
% run with "test(file)." where "file" is an input file name without ".in"

% vars/1 refers to the variables in the input file with clauses Sup => Var

init_bound(N):- vars(Vars),length(Vars,M), N is M*(M-1)/2.

% get/2 and put/2 refer to the hash table frontier

init_frontier(N):- vars(Vars),forall(member(Var,Vars),put(Var,N)).

% satisfied/2 tests whether Sup => Var is enabled to increment Var 

satisfied(Sup,Var):- forall(member(T,Sup),
  (T=V+O -> (get(Var,N),get(V,M),+O+N < M) ;
  (T=V-O -> (get(Var,N),get(V,M),-O+N < M) ;
            (get(Var,N),get(T,M),   N < M)))).

% test/0 sparks the depth-first search for a model, or finds a gap

test :- init_bound(N),init_frontier(0),once(step(-1,N)).

step(Count,N):-
  Count>=N -> print_maxgap;
  once(((Sup => Var),
  (satisfied(Sup,Var) -> get(Var,M),put(Var,M+1),step(Count+1,N)))).

step(_,_):- print_model.


%%%%%%%avoid reading this block with silly auxiliaries%%%%%%%

% syntax
:-op(1199, xfx, =>).

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

