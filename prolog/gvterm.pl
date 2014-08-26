:- module(graphviz_term,
	  [ term_to_dot/1,		% +Term
	    term_to_dot/2,		% +Out, +Term
	    dotty_term/1		% +Term
	  ]).
:- use_module(library(dcg/basics)).
:- use_module(library(process)).
:- use_module(library(settings)).
:- use_module(library(gensym)).

/** <module> View complex terms using Graphviz

This library translates complex Prolog terms  into Graphviz (dot) output
for graphical rendering.

@see	Default renderer is xdot from
	https://github.com/jrfonseca/xdot.py
*/

:- setting(graphviz:dot_viewer, atom, xdot,
	   'Program to show dot graphs').

%%	dotty_term(+Term) is det.
%
%	Write dot representation to temporary file   and  open this file
%	using the dotty program.

dotty_term(Term) :-
	setup_call_cleanup(tmp_file_stream(utf8, File, Out),
			   term_to_dot(Out, Term),
			   close(Out)),
%	process_create(path(cat), ['test.dot'], []),
	setting(graphviz:dot_viewer, Program),
	thread_create(run_dotty(Program, File),
		      _,
		      [detached(true)]).

:- dynamic
	dotty_process/1.

run_dotty(Program, File) :-
	process_create(path(Program), [File], [process(PID)]),
	assert(dotty_process(PID)),
	process_wait(PID, _),
	retractall(dotty_process(PID)).

kill_dotties :-
	forall(dotty_process(PID),
	       process_kill(PID)).

:- at_halt(kill_dotties).


%%	term_to_dot(+Term) is det.
%
%	Emit a dot representation for Term to the curent output.

term_to_dot(Term) :-
	term_to_dot(current_output, Term).


%%	term_to_dot(+Out:stream, Term) is det.
%
%	Emit a dot representation for Term to the stream Out.

term_to_dot(Out, Term) :-
	\+ \+ ( numbervars(Term, 0, _, [singletons(true)]),
		'$factorize_term'(Term, Skel, Subst),
		label_factors(Subst),
		phrase(struct0(Skel), Codes),
		format(Out, 'digraph structs {\n  node [shape=record];\n~s}\n', [Codes])
	      ).


label_factors([]).
label_factors([V='$VAR'(X)|T]) :- !,
	V = '$VAR'(X),
	label_factors(T).
label_factors(['$SKEL'(_,C)=C|T]) :-
	label_factors(T).

%%	struct0(+Term)//
%
%	Deal with the outer term.  Note that labels inside terms are
%	embedded in the term label.

struct0(Prim) -->
	{ number(Prim), !,
	  format(codes(Codes), '~q', [Prim])
	},
	cstring(Codes).
struct0(Prim) -->
	{ primitive(Prim), !,
	  format(codes(Codes), '~q', [Prim])
	},
	"\"", cstring(Codes), "\"".
struct0(Term) -->
	struct(Term, -(_), Links, []),
	links(Links).

%%	struct(+Term, Link, Links, RestLinks)//
%
%	Deal with compound and inner terms.

struct('$SKEL'(Done, C), -(Id), Links, LinksT) -->
	{ var(Done), !,
	  Done = top(Id)
	},
	struct(C, -(Id), Links, LinksT).
struct('$SKEL'(Done, C), Id-Arg, [link_c(Id-Arg, Id2, C)|LinkT], LinkT) -->
	{ var(Done), !,
	  Done = id(Id2)
	},
	".".
struct('$SKEL'(top(Id), _), Id-Arg,
       [link(Id-Arg, Id)|LinksT], LinksT) --> !,
	".".
struct('$SKEL'(id(Id2), _), Id-Arg, [link(Id-Arg, Id2)|LinkT], LinkT) --> !,
	".".
struct(Prim, _, Links, Links) -->
	{ primitive(Prim), !,
	  format(codes(Codes), '~q', [Prim])
	},
	cstring(Codes).
struct(Compound, -(Id), Links, LinkT) --> !,
	{ compound_name_arguments(Compound, F, Args),
	  gensym(struct, Id),
	  format(codes(FCodes), '~q', [F])
	},
	"  ", atom(Id),
	" [", "label=\"<f> ", cstring(FCodes), " ",
	gv_args(Args, 0, Id, Links, LinkT), "\"];\n".
struct(Compound, Id-Arg, [link_c(Id-Arg, _, Compound)|LinkT], LinkT) -->
	".".

gv_args([], _, _, Links, Links) --> [].
gv_args([H|T], N, Id, Links, LinksT) -->
	"|", gv_arg_id(N), " ",
	struct(H, Id-N, Links, LT0),
	{N2 is N + 1},
	gv_args(T, N2, Id, LT0, LinksT).

gv_arg_id(N) -->
	"<a", integer(N), ">".

links(Links) -->
	{ \+ memberchk(link_c(_,_,_), Links)
	}, !,
	"\n",
	link_f(Links).
links(Links) -->
	link_c(Links, RestLinks, []),
	links(RestLinks).

link_c([], Links, Links) --> [].
link_c([link_c(Id-Arg, Id2, Compound)|T0],
       [link(Id-Arg, Id2)|LinksT0], LinkT) --> !,
	struct(Compound, -(Id2), LinksT0, LinkT1),
	link_c(T0, LinkT1, LinkT).
link_c([H|T0], [H|T], Links) -->
	link_c(T0, T, Links).

link_f([]) --> [].
link_f([link(Id-Arg, Id2)|T]) -->
	"  ", atom(Id), ":a", integer(Arg), " -> ", atom(Id2), ":f;\n",
	link_f(T).


primitive('$VAR'(_)) :- !.
primitive(X) :-
	\+ compound(X).

%%	cstring(+Codes)//
%
%	Create a C-string. Normally =dot=  appears   to  be  using UTF-8
%	encoding. Would there be a  safer   way  to  transport non-ascii
%	characters, such as \uXXXX?

cstring([]) -->
	[].
cstring([H|T]) -->
	(   cchar(H)
	->  []
	;   [H]
	),
	cstring(T).

cchar(0'") --> "\\\"".
cchar(0'\n) --> "\\n".
cchar(0'\t) --> "\\t".
cchar(0'\b) --> "\\b".
cchar(0'|) --> "\\|".
cchar(0'[) --> "\\[".
cchar(0']) --> "\\]".

:- if(\+current_predicate(compound_name_arguments/3)).
compound_name_arguments(Term, Name, Args) :-
	Term =.. [Name|Args].
:- endif.
