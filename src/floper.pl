%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%%     FASILLER: Fuzzy LOgic Programming Environment for Research.         %%%


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INTERFACE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

user_help :- menu.

title :- nl,write('######################################################################'),
	nl,nl,
	write('________________    _________.___.____    .____                 '),nl,
	write('\\_   _____/  _  \\  /   _____/|   |    |   |    |    ___________ '),nl,
	write(' |    __)/  /_\\  \\ \\_____  \\ |   |    |   |    |  _/ __ \\_  __ \\'),nl,
	write(' |     \\/    |    \\/        \\|   |    |___|    |__\\  ___/|  | \\/'),nl,
	write(' \\___  /\\____|__  /_______  /|___|_______ \\_______ \\___  >__|   '),nl,
	write('     \\/         \\/        \\/             \\/       \\/   \\/       '),nl,
	write('    **  Fuzzy  Aggregators and SImilarities in a Logic Language **  '),nl,nl,
	write('    **                           v 0.2                          **  '),nl,
	nl,
	write('ooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooooo'),nl,nl,
	write('type \'menu\' to see the options'),nl.

menu :-   nl,nl,write('		*****  PROGRAM    MENU      *******'),nl,  
	write('**  parse  --> Parse/load a fuzzy prolog file (.fpl) 	**'),nl,
	write('**  save   --> Parse/load/save a fuzzy prolog file.  	**'),nl,
	write('**  load   --> Consult a prolog file (.pl). 	    	**'),nl,
	write('**  list   --> Displays the last loaded clauses.     	**'),nl,  
	write('**  clean  --> Clean the database 			**'),nl,nl,

	write('		*****  LATTICE    MENU      *******'),nl,  
	write('**  lat    --> Load a Multi-Adjoint lattice	     	**'),nl,
	write('**  show   --> Show current Multi-Adjoint lattice	**'),nl,
	write('**  ismode --> Select kind of interpretive steps	**'),nl,nl,

	write('		*****  SIMILARITY MENU      *******'),nl,  
	write('**  sim    --> Load a similarities file (.sim.pl)     	**'),nl,
	write('**  tnorm  --> Set t-norm for similarity calculations    **'),nl,
	write('**  tconorm--> Set t-conorm for similarity calculations  **'),nl,
	write('**  lcut   --> Set the lambda-cut for fuzzy unification **'),nl,nl,

	write('		*****  GOAL    MENU    	    *******'),nl,  
	write('**  intro  --> Introduce a new goal (between quotes). 	**'),nl,
	write('**  run    --> Execute a goal completely 		**'),nl,
	write('**  depth  --> Set the maximum level of execution trees **'),nl,
	write('**  leaves --> Interprete a goal                        **'),nl,
	write('**  tree   --> Generate a partial execution tree        **'),nl,nl,

	write('		*****  TRANSFORMATION  MENU *******'),nl, 
	write('%%  pe     -->  Partial evaluation 			%%'),nl,
	write('%%  fu     --> Fold/Unfold Transformations 		%%'),nl,
	write('%%  red    --> Reductants Calculus 			%%'),nl,nl,

	write('---------------------------------------------------------'),nl,nl,

	write('**  stop      --> Stop the execution of the parser. 	**'),nl,
	write('**  quit      --> Exit to desktop.                  	**'),nl,nl,

	write('---------------------------------------------------------'),nl,nl.

shell_synth :- nl,write('>> '), read(Command), (Command=end_of_file;try(call(Command),print_err),!,shell_synth).

print_err :- nl,write('Error...'),nl,!,shell_synth.

%% DYNAMIC PREDICATES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic
	rule/5,
	unfolding/2,
	rule_insert_id/1,
	transformation/6,
	rule_current_id/1,
	transformation_insert_id/1,
	transformation_current_id/1,
	sim:r/3.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PROGRAM MENU OPTIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% PARSE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

parse :- write('File to parse: '),read(File),nl,parser(File,'tmp_fuzzy-prolog.pl'), list.

parse(F) :- parser(F,'tmp_fuzzy-prolog.pl').

parser(Source,Destiny) :- 
	retractall(rule(_,_,_,_,_)),
	retractall(transformation(_,_,_,_,_,_)), 
	retractall(rule_insert_id(_)),
	retractall(rule_current_id(_)),
	retractall(transformation_insert_id(_)), 
	retractall(transformation_current_id(_)),
	assertz(rule_insert_id(0)),
	assertz(transformation_insert_id(0)),
	assertz(transformation_current_id(0)),
	open(Source,read,Stream),stream2list(Stream,Text),close(Stream),
	malp_begin, malp_program(S,Text,[]), malp_end,
	telling(T), tell('tmp_fuzzy-inter.pl'),
	write(':- dynamic rule/5.'),nl,p2inter(S),told,
	tell(Destiny), p2pl(S), told, tell(T),
	fpl:consult(Destiny), consult('tmp_fuzzy-inter.pl'),
	retractall(loaded_file_fpl(_)), assert(loaded_file_fpl(Source)),
	insert_transformation(transformation(load, add([]), remove([])), _).

%% Puts the file in a list %%
stream2list(Stream,Text) :- get_code(Stream,X),
 (X==9,Text=[' '|Text2],!,stream2list(Stream,Text2) % ignore 'tab' and puts a blank 
 ;X\==(-1),name(P,[X]),Text=[P|Text2],!,stream2list(Stream,Text2) 
 ;X==(-1),Text=[]). % EOF

%% Returns a char list from a code list.
to_char_list([A|B],[Ca|Cb]):-name(Ca,[A]),to_char_list(B,Cb).
to_char_list([],[]).

%% clean the list
clean(['%'|Text1],Text3) :- clean_simple_comment(Text1,Text2),clean(Text2,Text3). % ignore simple comment
clean(['/','*'|Text1],Text3) :- clean_complex_comment(Text1,Text2),clean(Text2,Text3). % ignore complex comment
clean([X|Text1],[X|Text2]) :- clean(Text1,Text2).
clean([],[]).

clean_simple_comment(['\r'|Text],['\r'|Text]) :- !. % RC  
clean_simple_comment(['\n'|Text],['\n'|Text]) :- !. % New line
clean_simple_comment([_|Text1],Text2) :- clean_simple_comment(Text1,Text2). % Any other symbol
clean_simple_comment([],[]). % sure terminate

clean_complex_comment(['*','/'|Text],Text) :- !.
clean_complex_comment([_|Text1],Text2) :- clean_complex_comment(Text1,Text2). % Any other symbol
clean_complex_comment([],_) :- error('Complex comment must end with \'*/\'.'). 

%% The final list (with prolog code) is written into a file.
to_file(File,[X|Text]) :- 
  (number(X),name(X,[K|J]),char_code(T,K),put_char(File,T),(empty(J),to_file(File,Text);aux_to_file(File,J),to_file(File,Text)) % If a number is read, it is converted into a char so we can it write in the file. If it has more than one digit, 'aux_to_file' is called so that the number can be written. %    
     ;put_char(File,X),to_file(File,Text)),!.
to_file(_,[]).
empty([]).

%% 'List' contains the remaining digits's ASCII codes   
aux_to_file(File,List) :- nth_(1,List,First,Tail),char_code(T,First),put_char(File,T),aux_to_file(File,Tail). 
aux_to_file(_,[]).

%% SAVE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

save :- write('File to parse: '),read(File), write('Save to: '),read(Save),
	parser(File,Save).

%% LOAD %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

load :- write('File to load: '),read(File),fpl:consult(File),retractall(loaded_file_pl(_)),assert(loaded_file_pl(File)).

%% LIST %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list :- try((loaded_file_pl(PL), list_pl(PL)),(write('No loaded files'),nl)),
	try((loaded_file_fpl(FPL), list_fpl(FPL)),write('No parsed files')).

list_pl(P):- nl, write('LOADED FILES CODE:'), nl,nl, list(P).
list_fpl(P):- nl, write('ORIGINAL FUZZY-PROLOG CODE:'), nl,nl, list(P),
		nl,write('GENERATED PROLOG CODE:'),nl,nl,list('tmp_fuzzy-prolog.pl').

list(F) :- open(F,read,Stream),stream2list(Stream,List),clean(List,Text),print_list(Text),nl,close(Stream).
print_list([]).
print_list([C|T]) :- (C == 'end_of_file'
		     ;write(C),print_list(T)).

%% CLEAN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

clean :- fasiller_default, assert(loaded_file_lat('num.lat')),wipe_module(fpl).

%% STOP %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

stop :- retractall(fasiller_depth(_)), retractall(fasiller_goal(_)), retractall(fasiller_ismode(_)),
	retractall(loaded_file_fpl(_)),retractall(loaded_file_pl(_)),retractall(loaded_file_lat(_)),
	wipe_module(fpl), wipe_module(lat).

%% QUIT %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

quit :- stop, del_file('tmp_fuzzy-prolog.pl'),del_file('tmp_fuzzy-inter.pl'), wipe_module(user).

del_file(F) :- exists_file(F), !, delete_file(F).
del_file(_).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LAT MENU OPTIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                  %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% LAT %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

lat(N) :-
	try(loaded_file_lat(L), (assertz(loaded_file_lat(null)), L=null)),
	wipe_module(lat),
	lat:consult(N),
	lat_test,
	retractall(loaded_file_lat(_)),
	assertz(loaded_file_lat(N)), nl,
	retractall(sim_tnorm(_)),
	retractall(sim_tconorm(_)),
	set_sim_tnorm,
	set_sim_tconorm,
	set_sim_lcut.

lat :-
	write('Current lattice: '),
	write(L), nl,
	write('Introduce new lattice: '),
	read(N), 
	lat(N).

lat_test:- nl, (current_predicate(lat:member/1), write('member/1 OK') ; write('WARNING: member/1 is not defined')),
	nl, (current_predicate(lat:bot/1),    write('bot/1 OK')    ; write('WARNING: bot/1 is not defined')),
	nl, (current_predicate(lat:top/1),    write('top/1 OK')    ; write('WARNING: top/1 is not defined')),
	nl, (current_predicate(lat:leq/2),    write('leq/2 OK')    ; write('WARNING: leq/2 is not defined')),
	nl, (current_predicate(lat:members/1),write('Finite lattice') ; write('Infinite lattice')).

%% SHOW %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

show :- nl, try((loaded_file_lat(LAT), list_lat(LAT)),write('No loaded lattices')).
list_lat(LAT) :- nl, write('MULTI-ADJOINT LATTICE:'), nl, list(LAT).

%% ISMODE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

ismode :- try(fasiller_ismode(O),(assert(fasiller_ismode(m)),O=m)), write('Current mode: '), write(O), nl, write('Introduce new mode (l=large, m=medium, s=small): '),
	read(X), (valid_ismode(X),!, retractall(fasiller_ismode(_)),assert(fasiller_ismode(X)), nl ;
	write(X), write(' is not a valid interpretive mode'), nl).
valid_ismode(s).
valid_ismode(m).
valid_ismode(l).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SIMILARITIES MENU OPTIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                           %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Load similarity file
sim(N) :-
	wipe_module(sim),
	open(N, read, Stream),
	stream2list(Stream, Text),
	close(Stream),
	clean(Text, Input), 
	malp_begin,
	blanks(Input, Inp2),
	sim2(Inp2), 
	malp_end,
	assert(sim:lista([])),
	create_list,
	close.

sim :-
	try((loaded_file_sim(F), write('Current similarity file: '), write(F)), write('Current similarity file: none')),
	nl, write('Similarity File: '),
	read(File),
	sim(File).

sim2(Input):- try((simprog(Input,[]), write('Parsing succeed'),nl),(nl,write('Parsing failed.'),nl)),!.

%% Set lambdacut
lcut :- retract(fasiller_lcut(L_old)),write('Current Lambda Cut: '),write(L_old),nl,
	write('Introduce new Lambda Cut: '), read(L), assert(fasiller_lcut(L)).

set_sim_tnorm :- try(sim_tnorm(_), try((current_predicate(lat:P/_), 
	name(P,Pn),append([97,110,100,95],C,Pn),name(G,C),assert(sim_tnorm(G))), (nl,write('WARNING: Tnorm not found.'),nl))).
set_sim_tnorm(A) :- retractall(sim_tnorm(_)), assert(sim_tnorm(A)).

set_sim_tconorm :- try(sim_tconorm(_), try((current_predicate(lat:P/_), 
	name(P,Pn),append([111,114,95],C,Pn),name(G,C),assert(sim_tconorm(G))), (nl,write('WARNING: Tconorm not found.'),nl))).
set_sim_tconorm(A) :- retractall(sim_tconorm(_)), assert(sim_tconorm(A)).

set_sim_lcut :- try(sim_lcut(_), (lat:bot(B), retractall(sim_lcut(_)), assert(sim_lcut(B)))).
set_sim_lcut(B) :- retractall(sim_lcut(_)), assert(sim_lcut(B)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

simprog --> simrule, simprog.
simprog --> [].

simrule --> ['~'], blanks, simrulek.
simrule --> idSim(A), blanks, need(['~'],'~'), blanks, idSim(B), blanks, tdSim(V), blanks, need(['.'],'.'), blanks, {assertz(sim:r(A,B,V))}.
simrulek --> [t,n,o,r,m], blanks, need(['='],'='), blanks, need(id(TN),'label'), blanks, need(['.'],'.'), blanks, {set_sim_tnorm(TN)}.
simrulek --> [t,c,o,n,o,r,m], blanks, need(['='],'='), blanks, need(id(TN),'label'), blanks, need(['.'],'.'), blanks,{set_sim_tconorm(TN)}.
simrulek --> [l,c,u,t], blanks, need(['='],'='), blanks, need(term(T),'Truth degree after \'=\''), blanks, need(['.'],'.'),blanks,
	{fpl2pl_term(T,PT), (lat:member(PT); loaded_file_lat(L),malp_newWarning([PT,' is not a member of lattice ',L])), set_sim_lcut(PT)}, !.

idSim((A,N)) --> id(A), idSim2(N).
idSim2(N) --> ['/'], int(X),{to_string(X,C,_),append(C,[46],C1),read_from_chars(C1,N),!}.
%% idSim2(all) --> [].
idSim2(0) --> [].

tdSim(PT) --> ['='],blanks,need(term(T),'Truth degree after \'=\''), 
	{fpl2pl_term(T,PT), (lat:member(PT); loaded_file_lat(L),malp_newWarning([PT,' is not a member of lattice ',L]))}, !.
tdSim(T) --> [], {lat:top(T)}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

may_insert(X) :- retract(sim:lista(L)), (exists(X,L), assert(sim:lista(L)) ; assert(sim:lista([X|L]))), !.

exists(X,[X|_]).
exists(X,[_|A]):-exists(X,A).

may_assert(r(A,B,V)) :- sim:r(A,B,W),lat:leq(V,W), !. %%W>V,!.
may_assert(r(A,B,V)) :- retractall(sim:r(A,B,_)),assertz(sim:r(A,B,V)).

%% Primero rellenamos la lista de símbolos

create_list :- sim:r(X,Y,_), may_insert(X), may_insert(Y), fail.
create_list.

%% Luego hacemos los cierres

close_ref :- asserta(sim:r(A,A,1)).

close_sim :- sim:lista(L), close_sim(L).
close_sim([]).
close_sim([A|L]):- (setof(sol(B,X),sim:r(A,B,X),S), close_sim_d(A,S);true),
		   (setof(sol(B,X),sim:r(B,A,X),S), close_sim_r(A,S);true),
		   close_sim(L).

close_sim_d(_,[]).
close_sim_d(A,[sol(B,X)|L]):- may_assert(r(B,A,X)), close_sim_d(A,L).
close_sim_r(_,[]).
close_sim_r(A,[sol(B,X)|L]):- may_assert(r(A,B,X)), close_sim_r(A,L).

close_trans :- setof(rel(A,B,V),sim:r(A,B,V),S), close_trans(S).
close_trans([]).
close_trans([rel(A,B,V)|L]):- (setof(sol(X,W),sim:r(B,X,W),S), close_trans(A,V,S);true),
			      close_trans(L).
close_trans(_,_,[]).
close_trans(A,V,[sol(X,W)|L]) :- sim_tnorm(And), name(And,Land),name(and_,Pre),append(Pre,Land,Cand),name(Und,Cand), Q=..[Und,V,W,Z], lat:Q,
	may_assert(r(A,X,Z)), may_assert(r(X,A,Z)), close_trans(A,V,L).

close :- close_sim, close_trans, close_ref.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GOAL MENU OPTIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                   %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% INTRO %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

intro :- write('Current goal: '), try(fasiller_goal(G_old),G_old='p(X)'), write(G_old),nl,
	write('Introduce new Goal: '), read(Goal), intro(Goal).

intro(Goal):- retractall(fasiller_goal(_)),assert(fasiller_goal(Goal)),
	term2char(Goal,List),malp_begin,body(B,List,[]),malp_end,assert(parsingGoal),
	telling(T),tell('tmp_pl-goal.pl'),p2pl_begin,p2plGoal(B),p2pl_end,told,
	tell('tmp_fuzzy-goal.pl'),write('\''),p2interBody(B),write('\'.'),told,tell(T), retractall(parsingGoal).

%% RUN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

run :- fasiller_goal(Goal),(Goal == 'empty', write('There is no goal introduced yet!');
	open('tmp_pl-goal.pl',read,Stream),stream2list(Stream,G),close(Stream),
	char2list(Code_goal,G), append(Code_goal,[46],Code),
	read_term_from_chars(Code,Fin_goal,[variable_names(V),singletons(_)]), !, run2(Fin_goal,V)).
run2(Fin_goal,V) :- on_exception(_,run3(V,fpl:Fin_goal,Sol),Sol=[]),print_exe(Sol),!.
run2(_) :- write('There is no solution.'),nl.

run3(V,fpl:Fin_goal,Sol) :- setof(V,fpl:Fin_goal,Sol), !.
run3(_,_,[]).

%% Returns a List and a Code_list from an Atom.---> [b,o,d,y] ---> [98,111,100,99] ---> body
to_string(List,Code_list,Atom) :-aux(List,Code_list), name(Atom,Code_list).
aux([],[]).
aux([H|T],[H1|T1]):-name(H,[H1]),aux(T,T1). 

%%%% Prints each solution in a new line, without temporal variables.
print_exe([]):- !, write('There is no solution.'),nl.
print_exe(A) :- print_exe2(A).
print_exe2([]).
print_exe2([H|T]) :- discardAnonymous(H,J), write(J),nl, print_exe2(T).

discardAnonymous([],[]).
discardAnonymous([A=_|L],S):- anonymousVar(A), !, discardAnonymous(L,S).
discardAnonymous([A=B|L],[A=B|S]):- discardAnonymous(L,S).

anonymousVar(A):- name(A,N), append([95],_,N).


%% DEPTH %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

depth :- retract(fasiller_depth(D_old)),write('Current depth: '),write(D_old),nl,
	write('Introduce new depth: '), read(Depth), assert(fasiller_depth(Depth)).

%% TREE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

tree :- retractall(varcont(_)),assert(varcont(0)), fasiller_depth(D), fasiller_ismode(I), fasiller_goal(Goal),
	(Goal == 'empty', write('There is no goal introduced yet!!!!!');
	seeing(S), see('tmp_fuzzy-goal.pl'),read(G),seen,see(S),
	name(G,Code_goal),append(Code_goal,[46],Code),
	read_from_chars(Code,Fin_goal),
	write('R0'),print_state(state(Fin_goal,[])),nl, try(tree2(D,I,state(Fin_goal,[]),1),true)), retract(varcont(_)), retractall(state(_,_)).

tree2(D,I,S,N):- D>N, step(I,S,F,R), tree3(D,I,F,R,N),fail.
tree2(_,_,_,_).

tree3(D,_,_,_,D).
tree3(D,I,F,R,N) :- D>N, indent(N), write(R), print_state(F),nl, M is N+1, tree2(D,I,F,M).

indent(0):- !.
indent(N):- write('    '), M is N-1, indent(M).

%% LEAVES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

leaves :-
	retractall(varcont(_)),
	retractall(state(_,_)),
	assert(varcont(0)),
	fasiller_depth(D),
	fasiller_goal(Goal),
	(Goal == 'empty', write('There is no goal introduced yet!');
	seeing(S), see('tmp_fuzzy-goal.pl'),read(G),seen,see(S),
	name(G,Code_goal),append(Code_goal,[46],Code),
	read_from_chars(Code,Fin_goal),nl,getStateVars(Fin_goal,VarsGoal), leaves2(VarsGoal,D,state(Fin_goal,[]),0)).

leaves2(Vrs,D,S,N):- D>N, step('l',S,F,_), leaves3(Vrs,D,F,N), fail.
leaves2(Vrs,_,S,_):- \+(step('l',S,_,_)),set_subs_leaves(S,Vrs,S2), print_state(S2),nl.
leaves2(_,_,_,_).

leaves3(_,D,_,D).
leaves3(Vrs,D,F,N) :- D>N, M is N+1, leaves2(Vrs,D,F,M).

getStateVars(and(_,_,L),V):- getStateVarsList(L,V).
getStateVars(or(_,_,L),V):- getStateVarsList(L,V).
getStateVars(agr(_,_,L),V):- getStateVarsList(L,V).
getStateVars(atom(_,L),V):- getStateVarsList(L,V).
getStateVars(term(_,L),V):- getStateVarsList(L,V).
getStateVars(var(A),[var(A)]):- !.
getStateVars(_,[]):- !.
getStateVarsList([A|L],V):- getStateVars(A,Va), getStateVarsList(L,Vl), append(Va,Vl,V).
getStateVarsList([],[]).

set_subs_leaves(state(A,S),Vrs, state(A,S2)):- set_subs_leaves2(S,Vrs,S2).
set_subs_leaves2([pair(A,X)|L],Vrs,[pair(A,X)|S]):- member(var(A),Vrs),!, set_subs_leaves2(L,Vrs,S).
set_subs_leaves2([_|L],Vrs,S):- set_subs_leaves2(L,Vrs,S).
set_subs_leaves2([],_,[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                             %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TRANSFORMATION MENU OPTIONS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                             %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Partial evaluation
pe :- write('This option is not implemented yet!'),nl.

%% Fold/unfold transformation
fu :- write('This option is not implemented yet!'),nl.

%% Reductant calculus
red :- write('This option is not implemented yet!'),nl.

unfold(Ri) :-
	rule_current_id(Ri),
	retractall(unfolding(Ri, _)),
	retractall(varcont(_)),
	assert(varcont(0)),
	fasiller_ismode(I),
	rule(Ri, head(Hi), Ir, body(Bi), Tr),
	rename(Hi, Hv),
	rename(Bi, Bv),
	step(I, state(Bv, []), state(Br, S), _),
	subs(Hv, S, Hr),
	assertz(unfolding(Ri, rule(head(Hr), Ir, body(Br), Tr))),
	fail.

unfold(Ri) :-
	retractall(varcont(_)),
	retractall(state(_, _)),
	findall(X, unfolding(Ri, X), Rules),
	Rules \= [],
	retractall(unfolding(Ri, _)),
	insert_rules(Rules, Add),
	insert_transformation(transformation(unfold, add(Add), remove([Ri])), _).

insert_rules([], []).
insert_rules([rule(H, I, B, T)|Xs], [N|Ns]) :-
	rule_insert_id(C),
	N is C + 1,
	retract(rule_insert_id(C)),
	assertz(rule_insert_id(N)),
	assertz(rule(N, H, I, B, T)),
	insert_rules(Xs, Ns).

insert_transformation(transformation(O, add(A), remove(R)), N) :-
	transformation_insert_id(C),
	N is C + 1,
	retract(transformation_insert_id(C)),
	assertz(transformation_insert_id(N)),
	retract(transformation_current_id(F)),
	assertz(transformation_current_id(N)),
	assert_rules(A),
	retract_rules(R),
	findall(X, rule_current_id(X), Rules),
	assertz(transformation(N, O, from(F), add(A), remove(R), rules(Rules))).
	
assert_rules([]).
assert_rules([X|Xs]) :-
	assertz(rule_current_id(X)),
	assert_rules(Xs).
	
retract_rules([]).
retract_rules([X|Xs]) :-
	retract(rule_current_id(X)),
	retract_rules(Xs).

transformation_goto(prev) :- !,
	transformation_current_id(C),
	P is C - 1,
	transformation_goto(P).
	
transformation_goto(next) :- !,
	transformation_current_id(C),
	N is C - 1,
	transformation_goto(N).
	
transformation_goto(first) :- !,
	transformation_unsafe_goto(1).
	
transformation_goto(last) :- !,
	transformation_insert_id(I),
	transformation_unsafe_goto(I).
	
transformation_goto(T) :-
	transformation_insert_id(I),
	number(T),
	T >= 1,
	T =< I,
	transformation_unsafe_goto(T).
	
transformation_unsafe_goto(T) :-
	transformation(T, _, _, _, _, rules(R)),
	retract(transformation_current_id(_)),
	assertz(transformation_current_id(T)),
	retractall(rule_current_id(_)),
	assert_rules(R).
	
rule(X, rule(X, A, B, C, D)) :- rule(X, A, B, C, D).
	
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% PARSER %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%        %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

term2char(T,C) :- write_to_chars(T,N), to_char_list(N,C).

char2list([A|B],[Ca|Cb]):-name(Ca,[A]),char2list(B,Cb).
char2list([],[]).

list2id(L,Id) :- var(Id),!, char2list(C,L), name(Id,C).
list2id(L,Id) :- var(L), !, name(Id,C), char2list(C,L).

malp_end:- malp_errors, statistics(walltime,[E,_]), retract(malp_time(S)), retract(malp_lineCount(L)), T is (E-S)/1000,
	print_list(['Parsed: ',L,' lines. ',T,' seconds']),nl, retract(malp_errorCount(_)), retract(malp_warningCount(_)),
	retract(malp_errorList(_)), retract(malp_ruleCount(_)),retractall(malp_aVarIndex(_)), nl.

malp_errors :- malp_errorList(L), reverse(L,R), malp_errors2(R), malp_numErrors.
malp_errors2([]).
malp_errors2([A|B]) :- print_list(A),nl,malp_errors2(B).
malp_numErrors :- malp_errorCount(E), malp_warningCount(W),
	print_list([E,' errors; ',W,' warnings']),nl.

malp_begin :- retractall(malp_lineCount(_)), retractall(malp_errorList(_)), retractall(malp_ruleCount(_)),
	retractall(malp_errorCount(_)), retractall(malp_warningCount(_)),
	assert(malp_lineCount(1)), assert(malp_errorList([])), assert(malp_ruleCount(1)),
	assert(malp_errorCount(0)), assert(malp_warningCount(0)),
	retractall(malp_time(_)), statistics(walltime,[S,_]), assert(malp_time(S)),
	retractall(parsingState(_)), assert(parsingState(normal)),
	retractall(malp_aVarIndex(_)), assert(malp_aVarIndex(0)).

malp_resetAVar :- retractall(malp_aVarIndex(_)), assert(malp_aVarIndex(0)).

malp_newError(E):- retract(malp_errorCount(Er)), Err is Er+1, assert(malp_errorCount(Err)), retract(malp_errorList(L)), malp_lineCount(N), assert(malp_errorList([['Line: ',N,'. ERROR !: '|E]|L])), !.
malp_newError_foundExpected(E,[X|Y],[X|Y]) :- malp_newError(['\'',X,'\' found. \'',E,'\' expected']).
malp_newError_foundExpected(E,[],[]) :- malp_newError(['\'\\eof\' found. \'',E,'\' expected']).
malp_newWarning(E):- retract(malp_warningCount(Wa)), War is Wa+1, assert(malp_warningCount(War)), retract(malp_errorList(L)), malp_lineCount(N), assert(malp_errorList([['Line: ',N,'. WARNING: '|E]|L])), !.
malp_newLine :- retract(malp_lineCount(N)), M is N+1, assert(malp_lineCount(M)), !.
'malp_newLine?'(X) :- ((name(X,[10]);name(X,[13])), malp_newLine;true).
malp_newRule(N) :- retract(malp_ruleCount(N)), M is N+1, assert(malp_ruleCount(M)),
retract(rule_insert_id(_)), assertz(rule_insert_id(N)), assertz(rule_current_id(N)), !.

setParsingState(M) :- retract(parsingState(_)), assert(parsingState(M)).

%% sync, reads input until symbol '.'.
sync --> {setParsingState(syn)}, sync2.
sync2 --> ['\n'], {malp_newLine}, sync2.
sync2 --> ['\r'], {malp_newLine}, sync2.
sync2 --> ['/','*'], blank_comB, sync2.
sync2 --> ['%'], blank_comL, sync2.
sync2 --> ['.'], !.
sync2 --> [_], sync2.
sync2 --> [], !.

%% allbut(C,S), reads S until symbol C. If no C, then raises error. Actualices malp_lineCount and malp_errorList
allbut(C,['\r'|Id]) --> ['\r'],!,{malp_newLine}, allbut(C,Id).
allbut(C,['\n'|Id]) --> ['\n'],!,{malp_newLine}, allbut(C,Id).
allbut(C,['\\',X|Id]) --> ['\\',X],!, allbut(C,Id).
allbut(C,[X|Id]) --> [X], {\+(X = C)},allbut(C,Id).
allbut(_,[]) --> [].

%% blank, blanks: Read white spaces, omit commentaries, actualizes malp_lineCount and malp_errorList
blank --> [' '].
blank --> ['\n'], {malp_newLine}.
blank --> ['\r'], {malp_newLine}.
blank --> ['\t'].
blank --> ['/','*'], blank_comB.
blank --> ['%'], blank_comL.
blank_comB --> ['*','/'].
blank_comB --> [X], {((X='\n';X='\r'),!,malp_newLine;true)}, blank_comB.
blank_comB --> [], malp_newError_foundExpected('*/').
blank_comL --> ['\n'], {malp_newLine}.
blank_comL --> ['\r'], {malp_newLine}.
blank_comL --> [_], blank_comL.
blank_comL --> [].
blanks --> blank, blanks, !.
blanks --> [].

%% need(X,E): El NT X es obligatorio. El input esperado es E.
need(_,_) --> {parsingState(syn)},!.
need(X,_) --> X, !.
need(_,E) --> malp_newError_foundExpected(E), sync.

%% program:
malp_program(L) --> blanks, malp_program_(L), !.
malp_program_([A|B]) --> declaration(A), !, blanks, malp_program_(B), !.
malp_program_(C) --> {malp_resetAVar}, rule(A), !,{parsingState(normal),C=[A|B];parsingState(syn),C=B, setParsingState(normal)},
	blanks, malp_program_(B),!.
malp_program_([]) --> [], !.

declaration(decl(A)) --> ['$'],!,allbut('$', A),need(['$'],'$'),!.

rule(_,[],[]) :- !,fail.
rule(rule(N,head(H),impl(I),body(B),td(T))) --> head(H), blanks, rule2(I,B,T), blanks,need(['.'],'.'),!,
	{parsingState(normal),malp_newRule(N); parsingState(syn)}.
rule2(I,B,T) --> implication(I),!, blanks, pcode(P), rule3(P,B,T).
rule2(empty,empty,T) --> truth_degree(T),!.

rule3(P,'b#'(P,empty,''),PT) --> [w,i,t,h],blank,!,need(term(T),'Truth degree after \'with\''),!,{fpl2pl_term(T,PT), (lat:member(PT); loaded_file_lat(L),malp_newWarning([PT,' is not a member of lattice ',L]))}, !.
rule3(P,B,T) --> bodyX(Y), !, blanks, pcode(P2), blanks, body2('b#'(P,Y,P2),B0),blanks, body4(B0,B), blanks, !, truth_degree(T),blanks,!.
rule3(P,'b#'(P,empty,''),empty) --> [].

truth_degree(PT) --> [w,i,t,h],!,blanks,need(term(T),'Truth degree after \'with\''), 
	{fpl2pl_term(T,PT), (lat:member(PT); loaded_file_lat(L),malp_newWarning([PT,' is not a member of lattice ',L]))}, !.
truth_degree(empty) --> [].

implication(I) --> ['<'],!, implication2(I), !.
implication2(C) --> ['-'], !, {arbitrary_connective(and,C,2)}.
implication2(I) --> [X], {minus(X)}, id_(D), {list2id([X|D],I)},!.
implication2('-') --> malp_newError_foundExpected('Label implication or \'-\'').
arbitrary_connective(T,C,A) :- M is A+1,current_predicate(lat:P/M), name(P,Pn),char2list(Pn,Pr),
	name(T,T_),char2list(T_,T__),append(T__,['_'|C_],Pr), list2id(C_,C),!.
arbitrary_connective(T,'empty',N) :- loaded_file_lat(L), malp_newWarning(['There is no ',N,'-ary ',T,' connectives in ', L]).

con('c#'(and,I)) --> ['&'],!, con2(I), blanks, !.
con('c#'(or,I)) --> ['|'],!, con2(I), blanks, !.
con('c#'(agr,I)) --> ['@'],!, con2(I), blanks, !.
con2(I) --> [X], {minus(X)},!, id_(D), {list2id([X|D],I)},!.
con2(_) --> [], !.
test_arity('c#'(T,I),N):- var(I),!,arbitrary_connective(T,I,N),!.
test_arity('c#'(T,I),N):- !,atom_concat(T,'_',A1),atom_concat(A1,I,A2),!,test_arity2(A2,N),!.
test_arity2(P,N) :-  M is N+1, current_predicate(lat:P/M),!.
test_arity2(P,N) :- M is N+1, loaded_file_lat(L), malp_newWarning(['There is no ',P,'/',M,' connective in ', L]).

pcode(R) --> pcode2(S), {list2id(S,R)}.
pcode2(R) --> ['{'],!, allbut('}',P), need(['}'],'}') ,!, blanks, pcode2(Q), {append(P,Q,R)}.
pcode2([]) --> [].

body(X) --> pcode(P1),need(bodyX(Y),'Body'), blanks, pcode(P2), blanks, body2('b#'(P1,Y,P2),Z), blanks, body4(Z,X), blanks.
bodyX(B) --> ['('],!,blanks, need(body(B),'body'),blanks, need([')'],')').
bodyX('#'(I,N,L)) --> con(I),!, body3(N,L), {test_arity(I,N)}.
bodyX(B) --> id(I),!, blanks, termX2(N,L), bodyX2(I,N,L,B).
%% bodyX(td(T)) --> term(B), {fpl2pl_term(B,T), (lat:member(T),!; loaded_file_lat(L),malp_newWarning([T,' is not a member of lattice ',L]))}.
bodyX(T) --> termX(B), blanks, bodyX_exp(B,T), blanks.
bodyX_exp(B,T) --> expr2_(B,T).
bodyX_exp(B,'#'(is,2,[B,T])) --> [i,s],blank, !, {((B=var(_);B=num(_)),!;fpl2pl_term(B,BPL),malp_newWarning([BPL,' is neither a variable nor a number']))}, blanks, need('S'(T),'Expression after \'is\''),blanks.
bodyX_exp(B,td(T)) --> [], {fpl2pl_term(B,T), (lat:member(T),!; loaded_file_lat(L),malp_newWarning([T,' is not a member of lattice ',L]))}.

bodyX2(I,N,L,td(T)) --> {fpl2pl_term('#'(I,N,L),T), lat:member(T),!}.
bodyX2(I,N,L,'#'(I,N,L)) --> [].

body2(Y,'#'(I,2,[Y,B])) --> con(I), need(body(B),'body'),{test_arity(I,2)}.
body2(Y,Y) --> [].
body3(N,[A|B]) --> ['('],!,blanks,need(body(A),'body'),blanks,bodies(M,B),need([')'],')'), {N is M+1}.
body3(0,[]) --> [].
bodies(N,[A|B]) --> [','],!,blanks,need(body(A),'body'),blanks,bodies(M,B), {N is M+1}.
bodies(0,[]) --> [].
body4(Z,'#'(';',2,[Z,T])) --> [';'], !, blanks, need(body(T),'Body after \';\'').
body4(Z,Z) --> [].

head('#'(I,N,L)) --> need(id(I),'Identifier in the head of the rule'),!, blanks, termX2(N,L),!.

%% En "(8+1)/2", "(8+1)" es considerado una tupla de un elemento. Luego se corrige.
term(T) --> expr(T),!.
termX(T) --> string(T),!.
termX(T) --> list(T),!.
termX(T) --> var(T),!.
termX(T) --> number(T),!.
termX('#'(I,N,L)) --> id(I),!, blanks, termX2(N,L),blanks,!.
termX('#'(',',N,[T|L])) --> ['('],!, blanks, need(term(T),'Term after \'(\''), terms(M,L), need([')'],')'), {N is M+1}.
termX2(N,[T|L]) --> ['('],!, blanks, need(term(T),'Term after \'(\''), terms(M,L), need([')'],')'), {N is M+1}.
termX2(0,[]) --> [].
terms(N,[A|B]) --> [','],!, blanks, need(term(A),'Term after \',\''), blanks, terms(M,B), {N is M+1}.
terms(0,[]) --> [].

expr(T) --> 'S'(A), blanks, expr2(A,T).
expr2_(A,'#'('=<',2,[A,B]))--> ['=','<'], !,blanks, need(expr(B),'Expression after \'=<\''),!.
expr2_(A,'#'('>=',2,[A,B]))--> ['>','='], !,blanks, need(expr(B),'Expression after \'>=\''),!.
expr2_(A,'#'('=',2,[A,B]))--> ['='], !,blanks, need(expr(B),'Expression after \'=\''),!.
expr2_(A,'#'('~',2,[A,B]))--> ['~'], !,blanks, need(expr(B),'Expression after \'~\''),!.
expr2_(A,'#'('<',2,[A,B]))--> ['<'], !,blanks, need(expr(B),'Expression after \'<\''),!.
expr2_(A,'#'('>',2,[A,B]))--> ['>'], !,blanks, need(expr(B),'Expression after \'>\''),!.
expr2(A,B) --> expr2_(A,B).
expr2(A,A) --> [].
'S'(T) --> 'F'(A), blanks, 'S2'(A,T).
'S2'(A,'#'('+',2,[A,B])) --> ['+'], !,blanks, need('S'(B),'Expression after \'+\''),!.
'S2'(A,'#'('-',2,[A,B])) --> ['-'], !,blanks, need('S'(B),'Expression after \'-\''),!.
'S2'(A,A) --> [].
'F'(T) --> termX(A),blanks,'F2'(A,T).
'F2'(A,'#'('*',2,[A,B])) --> ['*'], !,blanks, need('F'(B),'Expression after \'*\''),!.
'F2'(A,'#'('/',2,[A,B])) --> ['/'], !,blanks, need('F'(B),'Expression after \'/\''),!.
'F2'(A,A) --> [].

id(I) --> ['\''],!, allbut('\'', D), need(['\''],'\''), blanks, {list2id(D,I)}, !.
id(I) --> id2(I).
id2(I) --> [X], {minus(X)}, id_(D), {list2id([X|D],I)},!.
id_([X|D]) --> [X], {(letter(X);number(X);X='_')}, id_(D).
id_([]) --> [].

var(var(V)) --> [X], {(mayus(X);X='_')}, !, id_(D), {(X='_', malp_aVarConvert(['_'|D],V);list2id([X|D],V))}, blanks.

malp_aVarConvert(['_'],X) :- !, retract(malp_aVarIndex(N)), M is N+1, assert(malp_aVarIndex(M)), list2id(V,N),list2id(['_'|V],X).
malp_aVarConvert(['_'|D],X):- list2id(['_','_'|D],X).

list(L) --> ['['],!, blanks, list2(L), blanks, need([']'],']').
list2('#'('.',2,[T,R])) --> term(T),!,blanks, terms(_,L), blanks, list3(S), {terms2PlList(L,S,R)}.
list2('#'([],0,[])) --> [].
list3(T) --> ['|'], !, blanks, need(term(T),'term after \'|\'').
list3('#'([],0,[])) --> [].
terms2PlList([],S,S).
terms2PlList([T|L],S,'#'('.',2,[T,R])):-terms2PlList(L,S,R).

string(C) --> ['"'],!, allbut('"',S), need(['"'],'\"'), blanks, {char2list(C_,S),listize(C_,C)}.
listize([],'#'([],0,[])).
listize([A|B],'#'('.',2,[A,S])) :- listize(B,S).

letter(X) :- name(X,[C]), (C>=97, C=<122; C>=65, C=< 90).
minus(X) :- name(X,[C]), C>=97, C=<122.
mayus(X) :- name(X,[C]), C>=65, C=<90.

number(num(X)) --> ['-'], need(int(A),'Integer after \'-\''), number_(B), {append(['-'|A],B,C),list2id(C,X)}.
number(num(X)) --> int(A), number_(B), {append(A,B,C),list2id(C,X)}.
number_(['.'|A]) --> ['.'], int(A).
number_([])--> [].
int([X|Y]) --> [X], {number(X)},!, int_(Y).
int_([X|Y])--> [X], {number(X)},!, int_(Y).
int_([])--> [].


fpl2pl_term('#'(Id,_,L),S):- !,fpl2pl_terms(L,R),S=..[Id|R],!.
fpl2pl_term(var(X),X):- !.
fpl2pl_term(num(X),X):- !.
fpl2pl_term(S,S):- !.
fpl2pl_terms([],[]).
fpl2pl_terms([A|B],[C|D]):-fpl2pl_term(A,C),!,fpl2pl_terms(B,D).


/**************************************************************************
*
*	p2inter
*
***************************************************************************/

p2inter([]).
p2inter([A|B]):-p2interRule(A),!,p2inter(B).

p2interRule(decl(_)).
p2interRule(rule(N,head(H),impl(I),body(B),td(T))):- write('rule('),write(N),write(',head('),
	p2interHead(H),write('),impl('),write(I),write('),body('),p2interBody(B),write('),td('),
	p2interTd(T),write(')).'),nl.

p2interTd(empty):- \+(lat:member(empty)),!,lat:top(T), writeq(T).
p2interTd(T) :- writeq(T). %% p2plTd_(T).

p2interHead('#'(Id,A,L)):- !, write('atom(pred('),writeq(Id),write(','),write(A),write('),['),
	p2interTermLIST(L), write('])').

p2interBody(empty):- !, write(empty).
p2interBody('b#'(_,empty,_)):- !, write(empty).
p2interBody('b#'(_,B,_)):- !, p2interBody2(B).
p2interBody(B):- p2interBody2(B).
p2interBody2('#'('c#'(T,Lbl),A,L)) :- !, write(T),write('('),write(Lbl),write(','),write(A),write(',['),
	p2interBodyLIST(L), write('])').
p2interBody2('#'(';',2,[A,B])) :- !, arbitrary_connective(or,Lbl,2), p2interBody2('#'('c#'(or,Lbl),2,[A,B])).
p2interBody2('#'(Id,A,L)):- !, write('atom(pred('),writeq(Id),write(','),write(A),write('),['),
	p2interTermLIST(L), write('])').
p2interBody2(td(T)) :- write(td(T)).

p2interTerm('#'(',',1,[T])):- !,p2interTerm(T). %% CARLOS
p2interTerm('#'(Id,A,L)):- !, write('term(fun('),writeq(Id),write(','),write(A),write('),['),
	p2interTermLIST(L), write('])').
p2interTerm(var(X)):- parsingGoal, !, write('var(\\\''),write(X),write('\\\')').
p2interTerm(var(X)):- !, write('var(\''),write(X),write('\')').
p2interTerm(num(X)):- !, write('num('),write(X),write(')').

p2interBodyLIST([]).
p2interBodyLIST([A|B]):- p2interBody(A),p2interBodyLIST2(B).
p2interBodyLIST2([]).
p2interBodyLIST2([A|B]):- write(','),p2interBody(A),p2interBodyLIST2(B).

p2interTermLIST([]).
p2interTermLIST([A|B]):- p2interTerm(A),p2interTermLIST2(B).
p2interTermLIST2([]).
p2interTermLIST2([A|B]):- write(','),p2interTerm(A),p2interTermLIST2(B).

/**************************************************************************
*
*	p2pl
*
***************************************************************************/

p2pl(P) :- p2pl_begin, p2pl2(P), p2pl_end.

p2pl_begin :- assert(p2pl_tvVarIndex(1)).
p2pl_end  :- retractall(p2pl_tvVarIndex(_)).

p2pl_newTvVar(V) :- retract(p2pl_tvVarIndex(V)), W is V+1, assert(p2pl_tvVarIndex(W)).
p2pl_lastTvVar(W):- p2pl_tvVarIndex(V), W is V-1.
p2pl_resetTvVar  :- retract(p2pl_tvVarIndex(_)), assert(p2pl_tvVarIndex(1)).

p2pl2([]).
p2pl2([A|B]):-p2pl_resetTvVar, p2plRule(A),!,p2pl2(B).
p2plRule(decl(D)):- print_list(D),nl.
p2plRule(rule(_,head(H),impl(empty),body(empty),td(empty))) :- !,
	lat:top(S),p2plAtom(H,S),write('.'),nl.
p2plRule(rule(_,head(H),impl(empty),body(empty),td(T))) :- !,
	p2plAtom(H,T),write('.'),nl.
p2plRule(rule(_,head(H),impl(_),body('b#'('',empty,'')),td(empty))) :- !,
	lat:top(S),p2plAtom(H,S),write('.'),nl.
p2plRule(rule(_,head(H),impl(_),body('b#'('',empty,'')),td(T))) :- !,
	p2plAtom(H,T),write('.'),nl.
p2plRule(rule(_,head(H),impl(_),body('b#'(P,empty,'')),td(empty))) :- !,
	lat:top(S),p2plAtom(H,S),write(' :- '),write(P),write('.'),nl.
p2plRule(rule(_,head(H),impl(_),body('b#'(P,empty,'')),td(T))) :- !,
	p2plAtom(H,T),write(' :- '),write(P),write('.'),nl.

p2plRule(rule(_,head(H),impl(_),body(B),td(empty))) :- !,
	p2plAtom(H,var('TV0')), write(' :- '), p2plBody(B), write('.'),nl.
p2plRule(rule(_,head(H),impl(I),body(B),td(T))) :- !,
	%% p2plAtom(H,var('TV0')), write(' :- '), p2plBody('#'('c#'(and,I),2,[B,td(T)])), write('.'),nl. CARLOS
	p2plAtom(H,var('TV0')), write(' :- '), p2plBody('#'('c#'(and,I),2,[td(T),B])), write('.'),nl.

p2plTv(0,var('TV0')).
p2plTv(N,var(X)):- name(N,Nl), name('_TV',TV),append(TV,Nl,Xl),name(X,Xl).

p2plGoal('b#'(P1,B,P2)):- p2plPCODEpre(P1), p2plBody2(B,var('Truth_degree'),Q), p2plPCODEpos(P2,Q).
p2plGoal(B):- p2plBody2(B,var('Truth_degree'),_).

p2plBody('b#'(P1,B,P2)):- p2plPCODEpre(P1), p2plBody2(B,var('TV0'),Q), p2plPCODEpos(P2,Q).
p2plBody(B):- p2plBody2(B,var('TV0'),_).

p2plPCODEpre(''):- !.
p2plPCODEpre(P):- write(P),write(', ').
p2plPCODEpos('',_):- !.
p2plPCODEpos(P,colon):- write(', '),write(P).
p2plPCODEpos(P,nocolon):- write(P).

p2plBody2('#'(';',_,[A,B]),T,colon):- (var(T),!,p2pl_newTvVar(T_),p2plTv(T_,T);true), write('('),p2plBody2(A,T,_),write('; '),p2plBody2(B,T,_),write(')').
p2plBody2('#'(OP,2,[A,B]),T,colon):- member(OP,['=','>','<','=<','>=','~',is]),!, 
	(var(T), lat:top(K), T=td(K);true), p2plTerm(A), write(' '), write(OP), write(' '), p2plTerm(B).
%% p2plBody2('#'(OP,2,[A,B]),T,colon):- member(OP,['=','>','<','=<','>=','~',is]),!, 
%% 	(var(T),!,p2pl_newTvVar(T_),p2plTv(T_,T);true),
%% 	lat:top(K), p2plTerm(A), write(' '), write(OP), write(' '), p2plTerm(B), write(', '), p2plTd(T), write(' = '), writeq(K).
p2plBody2('#'('c#'(K,Lbl),_,L),T,colon):- p2plBodyLIST(L,Tl,Q),(Q=colon,!,write(', ');true),p2plCon('c#'(K,Lbl)),p2plTdLIST(Tl,T).
p2plBody2('b#'(P1,B,P2),T,Q2):- p2plPCODEpre(P1), p2plBody2(B,T,Q), p2plPCODEpos(P2,Q),(\+(P2=''),Q2=colon,!;Q2=Q).
p2plBody2(td(B),T,Q):- (\+(var(T)),!, p2plTd(T), write(' = '), writeq(B),Q=colon; T=td(B),Q=nocolon).
p2plBody2(B,T,colon):- (var(T),!,p2pl_newTvVar(T_),p2plTv(T_,T);true), p2plAtom(B,T).

p2plCon('c#'(K,L)):- write('lat:'),write(K),write('_'),write(L).

p2plBodyLIST([],[],nocolon).
p2plBodyLIST([A|B],[Ta|Tb],Q2):- p2plBody2(A,Ta,Q), p2plBodyLIST2(B,Tb,Q,Q2).
p2plBodyLIST2([],[],Q,Q).
p2plBodyLIST2([A|B],[Ta|Tb],colon,Q2):- write(', '), p2plBody2(A,Ta,Q), p2plBodyLIST2(B,Tb,Q,Q2).
p2plBodyLIST2([A|B],[Ta|Tb],nocolon,Q2):- p2plBody2(A,Ta,Q), p2plBodyLIST2(B,Tb,Q,Q2).

p2plTdLIST([],T):- write('('), p2plTd(T), write(')').
p2plTdLIST([A|B],T):- write('('), p2plTd(A), p2plTdLIST2(B), write(', '), p2plTd(T), write(')').
p2plTdLIST2([]).
p2plTdLIST2([A|B]):- write(', '), p2plTd(A), p2plTdLIST2(B).

p2plTd(X) :- var(X), !, p2pl_newTvVar(T), p2plTv(T,X), p2plTd(X).
p2plTd(empty):- !, write('TV0').
p2plTd(var(X)) :- !, write(X).
p2plTd(td(T)) :- writeq(T).

p2plAtom('#'(Id,_,L),T):- (var(T),!, p2pl_newTvVar(T_), p2plTv(T_,T);true),
	writeq(Id), write('('), (T=var(X), append(L,[var(X)],LT);append(L,[td(T)],LT)),p2plTermLIST(LT),write(')').

p2plTerm('#'(',',1,[T])):- !,p2plTerm(T). %% CARLOS
p2plTerm('#'(Id,A,L)):- !,writeq(Id),(A=0;A>0,write('('),p2plTermLIST(L),write(')')).
p2plTerm(var(X)):- !,write(X).
p2plTerm(num(N)):- !,write(N).
p2plTerm(td(T)):- !,writeq(T).
p2plTerm(X) :- p2plTd_(X).

p2plTd_(T) :- T=..[F|L], !, length(L,N), p2plTerm('#'(F,N,L)).
p2plTd_(T) :- write(T).

p2plTermLIST([]).
p2plTermLIST([A|B]):- p2plTerm(A),p2plTermLIST2(B).
p2plTermLIST2([]).
p2plTermLIST2([A|B]):- write(','),p2plTerm(A),p2plTermLIST2(B).

/**************************************************************************
*
*	rule_to_fuzzy
*
***************************************************************************/

show_rules(N) :-
	(N == current, transformation_current_id(T) ; T = N),
	transformation(T, _, _, _, _, rules(R)),
	findall(_, (member(X,R), rule(X,Y), rule_to_fuzzy(Y,Z), write("R"), write(X), write("\t"), writeln(Z)), _) ; writeln("").

rule_to_fuzzy([], '').
rule_to_fuzzy(empty, '').

rule_to_fuzzy(num(X), X).

rule_to_fuzzy([H], X) :-
	rule_to_fuzzy(H, X).
	
rule_to_fuzzy([H,S|T], X) :-
	rule_to_fuzzy(H, Y),
	rule_to_fuzzy([S|T], W),
	name(Y, S1),
	name(', ', S2),
	name(W, S3),
	append(S1, S2, S4),
	append(S4, S3, S5),
	name(X, S5).
	
rule_to_fuzzy(rule(_, head(H), impl(empty), _, _), X) :-
	rule_to_fuzzy(H, Y),
	name(Y, S1),
	name('.', S2),
	append(S1, S2, S3),
	name(X, S3), !.

rule_to_fuzzy(rule(_, head(H), impl(I), body(B), _), X) :-
	rule_to_fuzzy(H, Y),
	rule_to_fuzzy(B, Z),
	name(Y, S1),
	name(' <- ', S2),
	name(Z, S3),
	name('.', S4),
	append(S1, S2, S7),
	append(S7, S3, S8),
	append(S8, S4, S9),
	name(X, S9).
	
rule_to_fuzzy(agr(A, _, L), X) :-
	name('@', S1),
	name(A, S2),
	name('(', S3),
	rule_to_fuzzy(L, Y),
	name(Y, S4),
	name(')', S5),
	append(S1, S2, S6),
	append(S6, S3, S7),
	append(S7, S4, S8),
	append(S8, S5, S9),
	name(X, S9).
	
rule_to_fuzzy(var(V), V).
rule_to_fuzzy(td(T), T).

rule_to_fuzzy(and(_, _, [H]), X) :-
	rule_to_fuzzy(H, X).

rule_to_fuzzy(and(A, _, [H,S|T]), X) :-
	rule_to_fuzzy(H, Y),
	rule_to_fuzzy([S|T], Z),
	name('(', S1),
	name(Y, S2),
	name(' &', S3),
	name(A, S4),
	name(' ', S5),
	name(Z, S6),
	name(')', S7),
	append(S1, S2, S8),
	append(S8, S3, S9),
	append(S9, S4, S10),
	append(S10, S5, S11),
	append(S11, S6, S12),
	append(S12, S7, S13),
	name(X, S13).
	
rule_to_fuzzy(or(_, _, [H]), X) :-
	rule_to_fuzzy(H, X).

rule_to_fuzzy(or(O, _, [H,S|T]), X) :-
	rule_to_fuzzy(H, Y),
	rule_to_fuzzy([S|T], Z),
	name('(', S1),
	name(Y, S2),
	name(' |', S3),
	name(O, S4),
	name(' ', S5),
	name(Z, S6),
	name(')', S7),
	append(S1, S2, S8),
	append(S8, S3, S9),
	append(S9, S4, S10),
	append(S10, S5, S11),
	append(S11, S6, S12),
	append(S12, S7, S13),
	name(X, S13).

rule_to_fuzzy(atom(pred(P, _), []), P) :- !.

rule_to_fuzzy('=', '=').
rule_to_fuzzy('~', '~').
rule_to_fuzzy('<', '<').
rule_to_fuzzy('>', '>').
rule_to_fuzzy('=<', '=<').
rule_to_fuzzy('>=', '>=').
rule_to_fuzzy('is', ' is ').
rule_to_fuzzy('+', '+').
rule_to_fuzzy('-', '-').
rule_to_fuzzy('/', '/').
rule_to_fuzzy('*', '*').

rule_to_fuzzy(atom(pred(P,2),[A,B]), X) :-
	member(P, ['=','~','<','>','=<','>=', 'is']), !,
	rule_to_fuzzy(A, A2),
	rule_to_fuzzy(B, B2),
	name(A2, S1),
	rule_to_fuzzy(P, P2),
	name(P2, S2),
	name(B2, S3),
	append(S1, S2, S4),
	append(S4, S3, S5),
	name(X, S5).

rule_to_fuzzy(atom(pred(P, _), L), X) :-
	name(P, S1),
	name('(', S2),
	rule_to_fuzzy(L, Y),
	name(Y, S3),
	name(')', S4),
	append(S1, S2, S5),
	append(S5, S3, S6),
	append(S6, S4, S7),
	name(X, S7).

rule_to_fuzzy(term(fun(P, _), []), P) :- !.

rule_to_fuzzy(term(fun(P,2),[A,B]), X) :-
	member(P, ['+','-','*','/']), !,
	rule_to_fuzzy(A, A2),
	rule_to_fuzzy(B, B2),
	name(A2, S1),
	rule_to_fuzzy(P, P2),
	name(P2, S2),
	name(B2, S3),
	append(S1, S2, S4),
	append(S4, S3, S5),
	name(X, S5).

rule_to_fuzzy(term(fun(P, _), L), X) :-
	name(P, S1),
	name('(', S2),
	rule_to_fuzzy(L, Y),
	name(Y, S3),
	name(')', S4),
	append(S1, S2, S5),
	append(S5, S3, S6),
	append(S6, S4, S7),
	name(X, S7).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% EXECUTION TREE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% step(estado inicial, estado final, info)
step(_,state(Q,S),state(Q2,S2),Info)  :- select_atom(Q,A,Q_,Q_v),!,step_AS(state(Q,S),A,Q_,Q_v,state(Q2,S2),Info).
step(l,state(td(_),_),_,_):- !,fail.
step(l,state(Q,S),state(Q2,S2),result):- is_derivation(state(Q,S),state(Q2,S2)),!.
step(m,state(Q,S),state(Q2,S2),Info)  :- select_expression(Q,A,Q_,Q_v),step_IS(state(Q,S),A,Q_,Q_v,state(Q2,S2),Info),!.
step(s,state(Q,S),state(Q2,S2),Info)  :- select_expression(Q,A,Q_,Q_v),step_SIS(state(Q,S),A,Q_,Q_v,state(Q2,S2),Info),!.

%% step_?(Estado inicial S, átomo A seleccionado de S, S con una variable V en lugar de A, V, Estado final F, información)
step_AS(state(GOFA,S),atom(pred(OP,2),V1),Q_,td(Q_v),state(Q2,SZ),R):- 
	member(OP,['>','<','~','=<','>=']), !, V1=[As,Bs],operate_AS_param(As,KA),operate_AS_param(Bs,KB),
	operate_AS(OP,KA,KB,Q_v), Q2=Q_,SZ=S,R='S', assert(state(GOFA,S)).
step_AS(state(GOFA,S),atom(pred(is,2),[A,B]),Q_,td(Q_v),state(Q2,SZ),R):- 
	operate_AS_param(A,KA), operate_AS_param(B,KB),
	(KA=var(KAV), Z=[pair(KAV,KB)],lat:top(Q_v);\+(KA=var(KAV)),KB=KA,Z=[],lat:top(Q_v)),
	subs(Q_,Z,Q2), subs(S,Z,S0),append(Z,S0,SZ),R='S', assert(state(GOFA,S)).
step_AS(state(GOFA,S),atom(pred('=',2),[A,B]),Q_,td(Q_v),state(Q2,SZ),R):- 
	(A=var(KAV), Z=[pair(KAV,B)],lat:top(Q_v);\+(KA=var(KAV)),B=var(KBV), Z=[pair(KBV,KA)],lat:top(Q_v);
	try((B=A,Z=[],lat:top(Q_v)),(\+(B=A),lat:bot(Q_v)))),
	subs(Q_,Z,Q2), subs(S,Z,S0),append(Z,S0,SZ),R='S', assert(state(GOFA,S)).

step_AS(state(GOFA,S),atom(pred(P,A),V1),Q_,Q_v,state(Q2,SZ),R):- 
	\+(member(P,[is,'=','>','<','~','=<','>='])), rule_current_id(Nr),
	rule(Nr,head(atom(pred(P,A),V2)),impl(I),body(B),td(Nu)), retract(varcont(Vc)),Vc1 is Vc+1,assert(varcont(Vc1)),
	rename(V2,V2_),rename(B,B_), mgu(atom(pred(P,A),V1),atom(pred(P,A),V2_),Z,D),\+(lat:bot(D)),
	(B=empty,(lat:top(D),Q_v=td(Nu);\+(lat:top(D)),sim_tnorm(G),
	(\+(lat:top(Nu)), Q_v=and(G,2,[td(Nu),td(D)]);lat:top(Nu), Q_v=td(D))
	);\+(B=empty),(lat:top(D),
	(\+(lat:top(Nu)),Q_v=and(I,2,[td(Nu),B_]);lat:top(Nu),Q_v=B_)
	;\+(lat:top(D)),sim_tnorm(G),
	(\+(lat:top(Nu)), Q_v=and(G,2,[and(I,2,[td(Nu),B_]),td(D)]);lat:top(Nu), Q_v=and(G,2,[B_,td(D)]))
	)),subs(Q_,Z,Q2), subs(S,Z,S0),append(Z,S0,SZ), name(Nr,NrN), append([82],NrN,Rn), name(R,Rn), assert(state(GOFA,S)).
step_AS(state(GOFA,S),atom(pred(P,A),V1),Q_,Q_v,state(Q2,SZ),R):- 
	\+((A=2,member(P,[is,'=','>','<','~','=<','>=']))), rule_current_id(Nr),
	rule(Nr,head(atom(pred(Q,A),V2)),impl(I),body(B),td(Nu)), \+(Q=P), sim:r((P,A),(Q,A),Rfg), (\+(lat:bot(Rfg));lat:bot(Rfg), sim:r((P,all),(Q,all),Rfg2), \+(lat:bot(Rfg2))),
	retract(varcont(Vc)),Vc1 is Vc+1,assert(varcont(Vc1)),
	rename(V2,V2_),rename(B,B_), mgu(atom(pred(P,A),V1),atom(pred(Q,A),V2_),Z,D),\+(lat:bot(D)),
	(B=empty,(lat:top(D),Q_v=td(Nu);\+(lat:top(D)),sim_tnorm(G),
	(\+(lat:top(Nu)), Q_v=and(G,2,[td(Nu),td(D)]);lat:top(Nu), Q_v=td(D))
	);\+(B=empty), (lat:top(D),
	(\+(lat:top(Nu)), Q_v=and(I,2,[td(Nu),B_]);lat:top(Nu), Q_v=B_)
	;\+(lat:top(D)),sim_tnorm(G),
	(\+(lat:top(Nu)),Q_v=and(G,2,[and(I,2,[td(Nu),B_]),td(D)]);lat:top(Nu),Q_v=and(G,2,[B_,td(D)]))
	)),subs(Q_,Z,Q2), subs(S,Z,S0),append(Z,S0,SZ), name(Nr,NrN), append([82],NrN,Rn), name(R,Rn), assert(state(GOFA,S)).
step_AS(state(GOFA,S),_,Q_,Q_v,state(Q2,SZ),'R0'):- 
	\+(state(GOFA,S)),
	lat:bot(B), Q_v=td(B),
	Q2=Q_,SZ=S.


step_IS(state(_,S),E,Q_,td(Q_v),state(Q_,S),is) :- E=..[T,L,_,V], applow(T,L,Fn),
	str2td(V,V2),append(V2,[Q_v],V3),A=..[Fn|V3],lat:A.

operate_AS_param(term(fun(OP,2),[A,B]),num(D)):- !, operate_AS_param(A,num(KA)), operate_AS_param(B,num(KB)), Q=..[OP,KA,KB], D is Q.
operate_AS_param(A,A).
operate_AS(OP,num(A),num(B),T):- Q=..[OP,A,B], try((Q,lat:top(T)),lat:bot(T)).

%% is_derivation(Estado inicial S, Estado final)
is_derivation(state(Q,S),F):- select_expression(Q,A,Q_,Q_v),!,
	step_IS(state(Q,S),A,Q_,Q_v,State2,_),is_derivation(State2,F).
is_derivation(F,F).

step_SIS(state(_,S),E,Q_,Q_v,state(Q_,S),Info) :- E=..[T,L,_,V], applow(T,L,Fn),str2td(V,V2), append(V2,[X],V3),A=..[Fn|V3],
	try(clause(lat:A,Body),(nl,write('ERROR: '),write(A),write(' is not a dynamic predicate.'),nl,!,fail) ),
	( validForm(Body),assert(tsnum(nv(0))), assert(ts([])),tsInsert(V2),tsExtract(Body,X,Q_v),
	  retractall(ts(_)),retractall(tsnum(_)), (Q_v=td(_),!,Info=sis2; Info=sis1)
	; append(V2,[Rt],Po), Y=..[Fn|Po],lat:Y, Q_v=td(Rt), Info=sis2).

%% validForm(Prolog Body): 'true' if the parameter is vaid for sis1
validForm((A,B)):- !,A=..[P|_], name(P,Pn), to_string(Ps,Pn,_), validForm2(Ps), validForm(B).
validForm(A):- A=..[P|_], name(P,Pn), to_string(Ps,Pn,_), validForm2(Ps).
validForm2(X):-append([a,n,d,'_'],_,X).
validForm2(X):-append([a,g,r,'_'],_,X).
validForm2(X):-append([p,r,i,'_'],_,X).
validForm2(X):-append([o,r,'_'],_,X).

%% tsInsert(list) : insert the list in the table of symbols ts
tsInsert([]).
tsInsert([A|C]):- retract(ts(X)), assert(ts([var(A,td(A))|X])), tsInsert(C).	%% Parameters

%% tsExtract(Body,Variable,Result): extracts in R the Bariable from the Body and the table of symbols.
tsExtract((A,B),U,R):- !, tsExtract2(A), tsExtract(B,U,R).
tsExtract(A,U,R):- tsExtract2(A), ts_search(U,R).
tsExtract2(A):- !, A=..[P|L], rev(L,[U|Param]),retract(tsnum(U)), U=nv(NUM), NUM1 is NUM+1, assert(tsnum(nv(NUM1))),
	rev(Param,L2), length(Param,Num), applow(C,N,P), ts_searchmap(L2,TdParam), retract(ts(Ts)),
	Term=..[C,N,Num,TdParam], assert(ts([var(U,Term)|Ts])).

%% applow(A,B,A_B)
applow(C,X,Z):-var(Z),!,name(C,Cc), to_string(Cl,Cc,_), name(X,Xc), to_string(Xl,Xc,_), append(Cl,['_'|Xl],F), to_string(F,_,Z).
applow(C,X,Z):-name(Z,Zn),to_string(Zs,Zn,_), append(Cs,['_'|Xs],Zs), to_string(Cs,Cn,_),name(C,Cn), to_string(Xs,Xn,_),name(X,Xn).

ts_searchmap([A|B],[As|Bs]):- ts_search(A,As), ts_searchmap(B,Bs).
ts_searchmap([],[]).
ts_search(A,B):- ts(Ts), ts_search2(A,B,Ts).
ts_search2(A,B,[var(A,B)|_]):- !.
ts_search2(A,B,[_|L]):-ts_search2(A,B,L).
ts_search2(A,td(A),[]):- lat:member(A),!.
ts_search2(A,td(X),[]):- lat:bot(X), nl, write(A), write(' is not a member of the loaded lattice'),nl.

%% str2td: [td(0.3),td(1)] --> [0.3,1]
str2td([],[]).
str2td([td(X)|Y],[X|Y0]):-str2td(Y,Y0).

%% select_atom(objetivo S,átomo A de S,S con una variable S_v en lugar de A,S_v)
select_atom(atom(P,V),atom(P,V),W,W).
select_atom(and(C,A,L),X,and(C,A,L_),V):- select_atom_2(L,X,L_,V).
select_atom(agr(C,A,L),X,agr(C,A,L_),V):- select_atom_2(L,X,L_,V).
select_atom(or(C,A,L) ,X,or(C,A,L_) ,V):- select_atom_2(L,X,L_,V).
select_atom(pri(C,A,L),X,pri(C,A,L_),V):- select_atom_2(L,X,L_,V).
select_atom_2([A|B],X,[A_|B],A_v):-select_atom(A,X,A_,A_v),!.
select_atom_2([A|B],X,[A|B_],A_v):-select_atom_2(B,X,B_,A_v).

%% select_expression(objetivo S,expresión E de S,S con una variable S_v en lugar de E,S_v)
select_expression(and(C,A,L),and(C,A,L),V, V):- all_td(L),!.
select_expression(and(C,A,L),X,and(C,A,L_),V):- select_expression_2(L,X,L_,V).
select_expression(agr(C,A,L),agr(C,A,L),V, V):- all_td(L),!.
select_expression(agr(C,A,L),X,agr(C,A,L_),V):- select_expression_2(L,X,L_,V).
select_expression(or(C,A,L), or(C,A,L), V, V):- all_td(L),!.
select_expression(or(C,A,L), X,or(C,A,L_), V):- select_expression_2(L,X,L_,V).
select_expression(pri(C,A,L),pri(C,A,L),V, V):- all_td(L),!.
select_expression(pri(C,A,L),X,pri(C,A,L_),V):- select_expression_2(L,X,L_,V).
select_expression_2([A|B],X,[A_|B],A_v):-select_expression(A,X,A_,A_v),!.
select_expression_2([A|B],X,[A|B_],A_v):-select_expression_2(B,X,B_,A_v).

%% all_td(list of expressions): true if all parameters are truth degrees
all_td([]).
all_td([td(_)|S]):-all_td(S).

%% mgu(Expression 1, Expression 2, substitution)
mgu(atom(pred(P,A),L),atom(pred(Q,A),L_),S,T):- lat:top(TOP), unif(state([eq(term(fun(P,A),L),term(fun(Q,A),L_))], [],TOP),state([],S,T)).

unif(state([],S,D),state([],S,D)).
unif(state([eq(term(fun(F,N),L1), term(fun(G,N),L2))|R],S,D), state(Final,Sf,Df)) :-
	comp(L1,L2,Lr),append(Lr,R,R2), 
	(F=G, D2=D ;
	\+(F=G), try(sim:r((F,N),(G,N),Rfg),sim:r((F,all),(G,all),Rfg)),
	sim_tnorm(And), name(And,Land),name(and_,Pre),append(Pre,Land,Cand),name(Und,Cand), QQ=..[Und,D,Rfg,D2], lat:QQ),
	unif(state(R2,S,D2), state(Final,Sf,Df)),!.
unif(state([eq(X,X)|R],S,D),state(F,Sf,Df)):-
	unif(state(R,S,D),state(F,Sf,Df)),!.
unif(state([eq(X,var(V))|R],S,D),state(F,Sf,Df)):-
	subs(R,[pair(V,X)],R2),subs(S,[pair(V,X)],S2),
	unif(state(R2,[pair(V,X)|S2],D),state(F,Sf,Df)),!.
unif(state([eq(var(V),X)|R],S,D),state(F,Sf,Df)):-
	subs(R,[pair(V,X)],R2),subs(S,[pair(V,X)],S2),
	unif(state(R2,[pair(V,X)|S2],D),state(F,Sf,Df)),!.
unif(state([eq(X1,X2)|R],S,D),state(F,Sf,Df)):-
	X1=..[_,A],X2=..[_,B],
	(A=B, D2=D; 
	\+(A=B), try(sim:r((A,0),(B,0),Rfg),sim:r((A,all),(B,all),Rfg)),
	sim_tnorm(And), name(And,Land),name(and_,Pre),append(Pre,Land,Cand),name(Und,Cand), QQ=..[Und,D,Rfg,D2], lat:QQ),
	unif(state(R,S,D2),state(F,Sf,Df)).

%% comp([a],[b],[eq(a,b)])
comp([],[],[]).
comp([A|La],[B|Lb],[eq(A,B)|Lc]):-comp(La,Lb,Lc).


%% subs(Initial, Substitution, Final)
subs(X,[],X):- !.
subs([],_,[]):- !.
subs([pair(V,Vs)|L],S,[pair(V,Vs_)|L_]) :- subs(Vs,S,Vs_), subs(L,S,L_),!.
subs([A|As],S,[B|Bs]):-subs(A,S,B),subs(As,S,Bs),!.
subs(atom(P,L),S,atom(P,L_)):- subs(L,S,L_),!.
subs(and(A,N,L),S,and(A,N,L_)):- subs(L,S,L_),!.
subs(agr(A,N,L),S,agr(A,N,L_)):- subs(L,S,L_),!.
subs(or(A,N,L), S,or(A,N,L_)) :- subs(L,S,L_),!.
subs(pri(A,N,L),S,pri(A,N,L_)):- subs(L,S,L_),!.
subs(empty, _, empty):- !.
subs(con(C), _, con(C)):- !.
subs(num(C), _, num(C)):- !.
subs(td(C), _, td(C)):- !.
subs(term(F,L),S,term(F,L_)):- subs(L,S,L_),!.
subs(var(V), [pair(V,E)|_], E):- !.
subs(var(V), [_|S], E):- !, subs(var(V),S,E),!.
subs(eq(A,B),S,eq(A_,B_)):- subs(A,S,A_),subs(B,S,B_),!.

%% rename(parameters, renamed parameters)
rename([],[]).
rename([A|As],[B|Bs]):- rename(A,B), rename(As,Bs).
rename(var(A),var(B)):- !,name(A,N),varcont(I),name(I,Ni),append(N,Ni,R),name(B,R).
rename(empty,empty).
rename(con(A),con(A)).
rename(num(A),num(A)).
rename(td(A),td(A)).
rename(atom(P,L),atom(P,L2)):- rename(L,L2).
rename(term(F,L),term(F,L2)):- rename(L,L2).
rename(and(A,B,L),and(A,B,L2)):- rename(L,L2).
rename(or(A,B,L), or(A,B,L2)) :- rename(L,L2).
rename(agr(A,B,L),agr(A,B,L2)):- rename(L,L2).
rename(pri(A,B,L),pri(A,B,L2)):- rename(L,L2).

%% print_state(state(Q,S))
print_state(state(Q,S)):- write(' < '), prints(Q), write(', {'), prints_subs(S), write('} >'), !.
prints(and(Label,A,List)):- write('&'),write(Label),prints2(A,List).
prints(or(Label,A,List)) :- write('|'),write(Label),prints2(A,List).
prints(agr(Label,A,List)):- write('@'),write(Label),prints2(A,List).
prints(pri(Label,A,List)):- write('#'),write(Label),prints2(A,List).
prints(atom(pred(P,A),List)):- member(P,['=','~','<','>','=<','>=']), !, write('\''), write(P), write('\''), prints2(A,List).
prints(atom(pred(P,A),List)):- writeq(P), prints2(A,List).
prints(con(C)):- writeq(C).
prints(var(C)):- write(C).
prints(num(C)):- write(C).
prints(td(C)):- writeq(C).
prints(term(fun('.',2),[H,B])):- write('['),prints(H), prints_list(B), write(']').
prints(term(fun(F,A),List)):- member(F,['=','~','<','>','=<','>=']), !, write('\''), write(F), write('\''), prints2(A,List).
prints(term(fun(F,A),List)):- \+(F='.'), writeq(F), prints2(A,List).
prints([]).
prints(pair(A,B)):- write(A),write('/'),prints(B).

prints_subs([]).
prints_subs([A|B]):-prints(A),prints3(B).

prints2(0,_):- !.
prints2(_,[A|B]):-write('('),prints(A),prints3(B),write(')').

prints3([]).
prints3([A|B]):- write(','),prints(A),prints3(B).

prints_list(term(fun('.',2),[H,B])):- write(','), prints(H), prints_list(B).
prints_list(con([])).
prints_list(X):- write('|'),prints(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% AUXILIARY PREDICATES %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                      %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% try(dangerous block, exception): obtain a fasiller value with no errors
try(X,F):-(catch(X,_,F),!;F).

%% nth element
nth_(1,[E|L],E,L).
nth_(N,[E|L],X,[E|R]) :- N>0, M is N-1, nth_(M,L,X,R).

%% wipe_module(M): erase a module M
wipe_module(M) :- 
        (   current_predicate(M:P/A), 
            (\+(current_predicate(license:P/A)) %Evitamos que coja '=', '<', etc..., que aparecen como predicados de 'license'
            ; fail
            ),
            abolish(M:P,A), 
            fail 
        ;   true 
        ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% SETUP %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%       %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% reverse a list.
rev(L1,L2):- rev(L1,L2,[]).
rev([],L,L).
rev([H|T],L,S):- rev(T,L,[H|S]).

changedir(D):- getdir(D,Dir),catch(chdir(Dir),_,write('SICStus')).
getdir(D,Dir):- name(D,L),rev(L,R),eraseLastPart(R,Rdir),rev(Rdir,Ldir),name(Dir,Ldir).
eraseLastPart([47|L],[47|L]):- !.
eraseLastPart([_|L],R):- eraseLastPart(L,R).

fasiller_default :-
	retractall(fasiller_depth(_)),
	retractall(fasiller_goal(_)),
	retractall(fasiller_ismode(_)),
	retractall(loaded_file_fpl(_)),
	retractall(loaded_file_pl(_)),
	retractall(loaded_file_lat(_)),
	retractall(sim_tnorm(_)),
	retractall(sim_tconorm(_)),
	retractall(rule(_,_,_,_,_)),
	retractall(rule_insert_id(_)),
	retractall(rule_current_id(_)),
	retractall(transformation(_,_,_,_,_,_)),
	retractall(transformation_insert_id(_)), 
	retractall(transformation_current_id(_)),
	retractall(sim:r(_,_,_)),
	retractall(parsingGoal),
	retractall(state(_,_)),
	retractall(fasiller_lcut(_)),
	assertz(fasiller_lcut(0)),
	assertz(fasiller_depth(12)),
	assertz(fasiller_ismode('m')),
	assertz(rule_insert_id(0)),
	assertz(transformation_insert_id(0)),
	assertz(transformation_current_id(0)).

?-prolog_load_context(source,Name),write('Name: '),write(Name),nl,nl,changedir(Name),
	use_module(library(lists)), %% This package defines operations on lists.
	use_module(library(system)), %% This package contains utilities for invoking services from the operating system.
	use_module(library(charsio)), %% This package defines I/O predicates that read from, or write to, a code-list.
	fasiller_default, 		%% Default setting	
	title.
