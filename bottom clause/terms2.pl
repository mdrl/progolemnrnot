/*  Part of SWI-Prolog

    Author:        Jan Wielemaker
    E-mail:        J.Wielemaker@cs.vu.nl
    WWW:           http://www.swi-prolog.org
    Copyright (C): 2010, University of Amsterdam, VU University Amsterdam

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public
    License along with this library; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA

    As a special exception, if you link this library with other files,
    compiled with a Free Software compiler, to produce an executable, this
    library does not by itself cause the resulting executable to be covered
    by the GNU General Public License. This exception does not however
    invalidate any other reasons why the executable file might be covered by
    the GNU General Public License.
*/

:- module(terms2,
	  [
	    term_subsumer/5		% +Special1, +Special2, -General
	  ]).

:- use_module(library(rbtrees)).
:- use_module(library(terms)).

/** <module> Term manipulation

Compatibility library for term manipulation  predicates. Most predicates
in this library are provided as SWI-Prolog built-ins.

@compat	YAP, SICStus, Quintus.  Not all versions of this library define
	exactly the same set of predicates, but defined predicates are
	compatible.
*/

%%	term_subsumer(+Special1, +Special2, -General) is det.
%
%	General is the most specific term   that  is a generalisation of
%	Special1 and Special2. The  implementation   can  handle  cyclic
%	terms.
%
%	@compat SICStus
%	@author Inspired by LOGIC.PRO by Stephen Muggleton

%	It has been rewritten by  Jan   Wielemaker  to use the YAP-based
%	red-black-trees as mapping rather than flat  lists and use arg/3
%	to map compound terms rather than univ and lists.

term_subsumer(S1, S2, G, Map, NewMap) :-
	cyclic_term(S1),
	cyclic_term(S2), !,
	lgg_safe(S1, S2, G, Map, NewMap).

term_subsumer(S1, S2, G, Map, NewMap) :-
	lgg(S1, S2, G, Map, NewMap).

lgg(S1, S2, G, Map0, Map) :-
	(   S1 == S2
	->  G = S1,
	    Map = Map0
	;   compound(S1),
	    compound(S2),
	    functor(S1, Name, Arity),
	    functor(S2, Name, Arity)
	->  functor(G, Name, Arity),
	    lgg(0, Arity, S1, S2, G, Map0, Map)
	;   rb_lookup(S1+S2, G0, Map0)
	->  G = G0,
	    Map	= Map0
	;   rb_insert(Map0, S1+S2, G, Map)
	).

lgg(Arity, Arity, _, _, _, Map, Map) :- !.
lgg(I0, Arity, S1, S2, G, Map0, Map) :-
	I is I0 + 1,
	arg(I, S1, Sa1),
	arg(I, S2, Sa2),
	arg(I, G, Ga),
	lgg(Sa1, Sa2, Ga, Map0, Map1),
	lgg(I, Arity, S1, S2, G, Map1, Map).


%%	lgg_safe(+S1, +S2, -G, +Map0, -Map) is det.
%
%	Cycle-safe version of the  above.  The   difference  is  that we
%	insert compounds into the mapping table   and  check the mapping
%	table before going into a compound.

lgg_safe(S1, S2, G, Map0, Map) :-
	(   S1 == S2
	->  G = S1,
	    Map = Map0
	;   rb_lookup(S1+S2, G0, Map0)
	->  G = G0,
	    Map	= Map0
	;   compound(S1),
	    compound(S2),
	    functor(S1, Name, Arity),
	    functor(S2, Name, Arity)
	->  functor(G, Name, Arity),
	    rb_insert(Map0, S1+S2, G, Map1),
	    lgg_safe(0, Arity, S1, S2, G, Map1, Map)
	;   rb_insert(Map0, S1+S2, G, Map)
	).

lgg_safe(Arity, Arity, _, _, _, Map, Map) :- !.
lgg_safe(I0, Arity, S1, S2, G, Map0, Map) :-
	I is I0 + 1,
	arg(I, S1, Sa1),
	arg(I, S2, Sa2),
	arg(I, G, Ga),
	lgg_safe(Sa1, Sa2, Ga, Map0, Map1),
	lgg_safe(I, Arity, S1, S2, G, Map1, Map).


%%	term_factorized(+Term, -Skeleton, -Substiution)
%
%	Is true when Skeleton is  Term   where  all subterms that appear
%	multiple times are replaced by a  variable and Substitution is a
%	list of Var=Value that provides the subterm at the location Var.
%	I.e., After unifying all substitutions  in Substiutions, Term ==
%	Skeleton. Term may be cyclic. For example:
%
%	  ==
%	  ?- X = a(X), term_factorized(b(X,X), Y, S).
%	  Y = b(_G255, _G255),
%	  S = [_G255=a(_G255)].
%	  ==

term_factorized(Term, Skeleton, Substitutions) :-
	rb_new(Map0),
	add_map(Term, Map0, Map),
	rb_visit(Map, Counts),
	common_terms(Counts, Common),
	(   Common == []
	->  Skeleton = Term,
	    Substitutions = []
	;   ord_list_to_rbtree(Common, SubstAssoc),
	    insert_vars(Term, Skeleton, SubstAssoc),
	    mk_subst(Common, Substitutions, SubstAssoc)
	).

add_map(Term, Map0, Map) :-
	(   primitive(Term)
	->  Map = Map0
	;   rb_update(Map0, Term, Old, New, Map)
	->  New is Old+1
	;   rb_insert(Map0, Term, 1, Map1),
	    assoc_arg_map(1, Term, Map1, Map)
	).

assoc_arg_map(I, Term, Map0, Map) :-
	arg(I, Term, Arg), !,
	add_map(Arg, Map0, Map1),
	I2 is I + 1,
	assoc_arg_map(I2, Term, Map1, Map).
assoc_arg_map(_, _, Map, Map).

common_terms([], []).
common_terms([H-Count|T], List) :- !,
	(   Count == 1
	->  common_terms(T, List)
	;   List = [H-_NewVar|Tail],
	    common_terms(T, Tail)
	).

insert_vars(T0, T, _) :-
	primitive(T0), !,
	T = T0.
insert_vars(T0, T, Subst) :-
	rb_lookup(T0, S, Subst), !,
	T = S.
insert_vars(T0, T, Subst) :-
	functor(T0, Name, Arity),
	functor(T,  Name, Arity),
	insert_arg_vars(1, T0, T, Subst).

insert_arg_vars(I, T0, T, Subst) :-
	arg(I, T0, A0), !,
	arg(I, T,  A),
	insert_vars(A0, A, Subst),
	I2 is I + 1,
	insert_arg_vars(I2, T0, T, Subst).
insert_arg_vars(_, _, _, _).

mk_subst([], [], _).
mk_subst([Val0-Var|T0], [Var=Val|T], Subst) :-
	functor(Val0, Name, Arity),
	functor(Val,  Name, Arity),
	insert_arg_vars(1, Val0, Val, Subst),
	mk_subst(T0, T, Subst).
