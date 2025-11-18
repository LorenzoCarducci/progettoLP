:- module(tc, [tc/1, tc_debug_on/0, tc_debug_off/0]).

:- dynamic next_type_var_id/1.
next_type_var_id(0).

:- dynamic tc_debug/1.
tc_debug(off).

tc_debug_on :-
    retractall(tc_debug(_)),
    asserta(tc_debug(on)).

tc_debug_off :-
    retractall(tc_debug(_)),
    asserta(tc_debug(off)).

/* ============================ ENTRY POINT ============================ */
/* Punto di ingresso del type checker: legge il file, genera e risolve i vincoli. */

tc_core(File) :-
    retractall(next_type_var_id(_)),
    asserta(next_type_var_id(0)),
    format("%%% Type checking '~w'.~n", [File]),
    read_program(File, Clauses0),
    reorder_clauses(Clauses0, Clauses),
    build_initial_env(Clauses, Env0),
    generate_constraints(Clauses, Env0, Constraints),
    solve_constraints(Constraints, Subst, Errors),
    apply_subst_env(Subst, Env0, EnvTyped),
    print_env_types(EnvTyped),
    print_errors(Errors).

tc(File) :-
    (   tc_core(File)
    ->  true
    ;   true
    ).

/* =========================== LETTURA FILE ============================ */
/* Lettura dei termini Prolog dal file sorgente. */

read_program(File, Clauses) :-
    open(File, read, In),
    read_terms(In, Clauses),
    close(In).

read_terms(Stream, []) :-
    at_end_of_stream(Stream),
    !.
read_terms(Stream, [T|Ts]) :-
    read(Stream, Term),
    ( Term == end_of_file ->
        Ts = []
    ; T = Term,
      read_terms(Stream, Ts)
    ).

/* ====================== RIORDINO CLAUSOLE ============================ */
/* Porta alla fine le direttive (:- ...) lasciando prima le clausole normali. */

is_directive_clause((:- _)).

split_directives([], [], []).
split_directives([Cl|Cls], [Cl|Dirs], Others) :-
    is_directive_clause(Cl),
    !,
    split_directives(Cls, Dirs, Others).
split_directives([Cl|Cls], Dirs, [Cl|Others]) :-
    split_directives(Cls, Dirs, Others).

reorder_clauses(Clauses, Reordered) :-
    split_directives(Clauses, Directives, Others),
    append(Others, Directives, Reordered).

/* ========================= TYPE VAR & TIPI =========================== */
/* Gestione delle variabili di tipo e definizione dei costruttori di tipo. */

fresh_type_var(t_var(Id)) :-
    retract(next_type_var_id(Id0)),
    Id is Id0 + 1,
    asserta(next_type_var_id(Id)).

/* ===================== BUILT-IN PREDICATES =========================== */
/* Ambiente dei tipi dei predicati built-in che vogliamo riconoscere. */

builtin_env(EnvBuiltin) :-
    fresh_type_var(T1),
    fresh_type_var(T2),
    fresh_type_var(T3),
    fresh_type_var(T4),
    EnvBuiltin =
      [ pred(member, 2) - t_pred(member, 2, [T1, t_list(T1)])
      , pred(length, 2) - t_pred(length, 2, [t_list(T2), t_int])
      , pred(append, 3) - t_pred(append, 3,
                                 [t_list(T3), t_list(T3), t_list(T3)])
      , pred(is_list, 1) - t_pred(is_list, 1, [t_list(T4)])
      ].

/* ===================== AMBIENTE DEI PREDICATI ======================== */
/* Costruzione/lookup dell’ambiente dei predicati utente + built-in. */

build_initial_env(Clauses, Env) :-
    findall(Name/Arity,
            ( member(Cl, Clauses),
              is_clause(Cl, Head, _Body),
              Head \= dummy_head,
              functor(Head, Name, Arity)
            ),
            Pairs0),
    sort(Pairs0, Pairs),
    build_pred_entries(Pairs, EnvUser),
    builtin_env(EnvBuiltin),
    append(EnvBuiltin, EnvUser, Env).

is_clause((:- Goal), dummy_head, Goal) :- !.
is_clause((Head :- Body), Head, Body) :- !,
    callable(Head).
is_clause(Head, Head, true) :-
    callable(Head),
    Head \= (:-).

build_pred_entries([], []).
build_pred_entries([Name/Arity | Rest],
                   [pred(Name,Arity) - t_pred(Name,Arity,ArgTypes) | EnvRest]) :-
    fresh_arg_types(Arity, ArgTypes),
    build_pred_entries(Rest, EnvRest).

fresh_arg_types(0, []).
fresh_arg_types(N, [T|Ts]) :-
    N > 0,
    fresh_type_var(T),
    N1 is N - 1,
    fresh_arg_types(N1, Ts).

lookup_pred([pred(Name,Arity)-Type|_], Name, Arity, Type) :- !.
lookup_pred([_|Rest], Name, Arity, Type) :-
    lookup_pred(Rest, Name, Arity, Type).

/* ===================== GENERAZIONE VINCOLI =========================== */
/* Genera i vincoli di tipo a partire dalle clausole del programma. */

generate_constraints(Clauses, Env, Constraints) :-
    generate_constraints_clauses(Clauses, Env, [], Constraints).

generate_constraints_clauses([], _Env, C, C).
generate_constraints_clauses([Cl|Rest], Env, CIn, COut) :-
    ( is_clause(Cl, Head, Body) ->
        ( Head == dummy_head ->
            term_variables(Body, Vars),
            make_var_env(Vars, VarEnv),
            gen_body_constraints(Body, Env, VarEnv, CIn, CMid)
        ;   gen_head_and_body_constraints(Head, Body, Env, CIn, CMid)
        )
    ;   CMid = CIn
    ),
    generate_constraints_clauses(Rest, Env, CMid, COut).

gen_head_and_body_constraints(Head, Body, EnvPred, CIn, COut) :-
    term_variables((Head :- Body), Vars),
    make_var_env(Vars, VarEnv),
    functor(Head, Name, Arity),
    lookup_pred(EnvPred, Name, Arity, t_pred(_,_,PredArgTypes)),
    Head =.. [_|HeadArgs],
    gen_args_constraints(HeadArgs, PredArgTypes, VarEnv, CIn, CHead, Head),
    gen_body_constraints(Body, EnvPred, VarEnv, CHead, COut).

/* ===================== AMBIENTE VARIABILI LOGICHE ==================== */
/* Associa a ogni variabile logica una variabile di tipo. */

make_var_env([], []).
make_var_env([V|Vs], [V-T | Rest]) :-
    fresh_type_var(T),
    make_var_env(Vs, Rest).

lookup_var_type([V-T|_], V, T) :- !.
lookup_var_type([_|Rest], V, T) :-
    lookup_var_type(Rest, V, T).

/* ========= gen_args_constraints CON CONTESTO DEL GOAL ================ */
/* Collega i tipi degli argomenti con quelli dichiarati per il predicato. */

gen_args_constraints([], [], _VarEnv, C, C, _Goal).
gen_args_constraints([Arg|Args], [Ty|Tys], VarEnv, CIn, COut, Goal) :-
    infer_term_type(Arg, VarEnv, TyTerm, CIn, C1),
    add_constraint(eq_in_context(TyTerm, Ty, Goal), C1, C2),
    gen_args_constraints(Args, Tys, VarEnv, C2, COut, Goal).

/* ================== INFERENZA TIPO TERMINI SEMPLICI ================== */
/* Assegna o deduce il tipo dei singoli termini. */

infer_term_type(Term, _VarEnv, t_int, C, C) :-
    integer(Term),
    !.

infer_term_type(Term, VarEnv, Ty, C, C) :-
    var(Term),
    !,
    lookup_var_type(VarEnv, Term, Ty).

infer_term_type(true, _VarEnv, t_bool, C, C) :- !.
infer_term_type(false, _VarEnv, t_bool, C, C) :- !.

infer_term_type(Term, _VarEnv, t_list(TElem), C, C) :-
    Term == [],
    !,
    fresh_type_var(TElem).

infer_term_type([H|_T], VarEnv, t_list(TElem), CIn, COut) :-
    !,
    fresh_type_var(TElem),
    infer_term_type(H, VarEnv, TH, CIn, C1),
    add_constraint(eq(TH, TElem), C1, COut).

infer_term_type(Term, _VarEnv, t_atom, C, C) :-
    atom(Term),
    !.

infer_term_type(_Term, _VarEnv, Ty, C, C) :-
    fresh_type_var(Ty).

/* =========== VINCOLI PER IL CORPO DELLA CLAUSOLA ===================== */
/* Genera vincoli di tipo dalle chiamate presenti nel corpo delle clausole. */

gen_body_constraints(true, _EnvPred, _VarEnv, C, C) :- !.
gen_body_constraints((G1, Gs), EnvPred, VarEnv, CIn, COut) :-
    !,
    gen_goal_constraints(G1, EnvPred, VarEnv, CIn, C1),
    gen_body_constraints(Gs, EnvPred, VarEnv, C1, COut).
gen_body_constraints(Goal, EnvPred, VarEnv, CIn, COut) :-
    gen_goal_constraints(Goal, EnvPred, VarEnv, CIn, COut).

/* ================= GOAL CONTESTUALIZZATO ============================= */
/* Generazione dei vincoli per uguaglianze, confronti e predicati. */

gen_goal_constraints((A = B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, TB, (A = B)), C2, COut).

gen_goal_constraints((A \= B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, TB, (A \= B)), C2, COut).

gen_goal_constraints((A == B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, TB, (A == B)), C2, COut).

gen_goal_constraints((A \== B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, TB, (A \== B)), C2, COut).

gen_goal_constraints((A > B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, t_int, (A > B)), C2, C3),
    add_constraint(eq_in_context(TB, t_int, (A > B)), C3, COut).

gen_goal_constraints((A < B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, t_int, (A < B)), C2, C3),
    add_constraint(eq_in_context(TB, t_int, (A < B)), C3, COut).

gen_goal_constraints((A >= B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, t_int, (A >= B)), C2, C3),
    add_constraint(eq_in_context(TB, t_int, (A >= B)), C3, COut).

gen_goal_constraints((A =< B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, t_int, (A =< B)), C2, C3),
    add_constraint(eq_in_context(TB, t_int, (A =< B)), C3, COut).

gen_goal_constraints((A =:= B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, t_int, (A =:= B)), C2, C3),
    add_constraint(eq_in_context(TB, t_int, (A =:= B)), C3, COut).

gen_goal_constraints((A =\= B), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq_in_context(TA, t_int, (A =\= B)), C2, C3),
    add_constraint(eq_in_context(TB, t_int, (A =\= B)), C3, COut).

gen_goal_constraints((X is Expr), _Env, VarEnv, CIn, COut) :-
    !,
    infer_term_type(X, VarEnv, TX, CIn, C1),
    infer_arith_expr_type(Expr, VarEnv, TE, C1, C2),
    add_constraint(eq_in_context(TX, TE, (X is Expr)), C2, COut).

gen_goal_constraints(Goal, EnvPred, VarEnv, CIn, COut) :-
    functor(Goal, Name, Arity),
    (   lookup_pred(EnvPred, Name, Arity, t_pred(_,_,ArgTypes))
    ->  Goal =.. [_|Args],
        gen_args_constraints(Args, ArgTypes, VarEnv, CIn, COut, Goal)
    ;   COut = CIn
    ).

/* ================= TIPO ESPRESSIONI ARITMETICHE ====================== */
/* Deduce il tipo delle espressioni aritmetiche. */

infer_arith_expr_type(Expr, _VarEnv, t_int, C, C) :-
    integer(Expr),
    !.

infer_arith_expr_type(Expr, VarEnv, Ty, C, C) :-
    var(Expr),
    !,
    lookup_var_type(VarEnv, Expr, Ty).

infer_arith_expr_type(Expr, VarEnv, t_int, CIn, COut) :-
    Expr =.. [Op, A, B],
    member(Op, [+, -, *, /]),
    !,
    infer_arith_expr_type(A, VarEnv, TA, CIn, C1),
    infer_arith_expr_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq(TA, t_int), C2, C3),
    add_constraint(eq(TB, t_int), C3, COut).

infer_arith_expr_type(_Expr, _VarEnv, Ty, C, C) :-
    fresh_type_var(Ty).

/* =================== RISOLUZIONE VINCOLI (UNIFY) ===================== */
/* Risoluzione dei vincoli di uguaglianza tra tipi con unificazione. */

goal_primitive(Goal) :-
    functor(Goal, F, A),
    (   ( F = (=),   A = 2 )
    ;   ( F = (\=),  A = 2 )
    ;   ( F = (==),  A = 2 )
    ;   ( F = (\==), A = 2 )
    ;   ( F = (>),   A = 2 )
    ;   ( F = (<),   A = 2 )
    ;   ( F = (>=),  A = 2 )
    ;   ( F = (=<),  A = 2 )
    ;   ( F = (=:=), A = 2 )
    ;   ( F = (=\=), A = 2 )
    ;   ( F = is,    A = 2 )
    ;   ( F = is_list, A = 1 )
    ).

solve_constraints(Constraints, Subst, Errors) :-
    solve_constraints_list(Constraints, [], Subst, [], Errors).

solve_constraints_list([], Sub, Sub, Err, Err).

solve_constraints_list([eq_in_context(T1,T2,Goal)|Cs],
                       SubIn, SubOut, ErrIn, ErrOut) :-
    apply_subst_type(SubIn, T1, S1),
    apply_subst_type(SubIn, T2, S2),
    (   unify_type(S1, S2, SubIn, SubMid)
    ->  ErrMid = ErrIn
    ;   (   goal_primitive(Goal)
        ->  build_context_error(S1, S2, Goal, Msg),
            SubMid = SubIn,
            append(ErrIn, [Msg], ErrMid)
        ;   format(string(Msg),
                   "Type mismatch: ~w vs ~w in call '~w'",
                   [S1, S2, Goal]),
            SubMid = SubIn,
            append(ErrIn, [Msg], ErrMid)
        )
    ),
    solve_constraints_list(Cs, SubMid, SubOut, ErrMid, ErrOut).

solve_constraints_list([eq(T1,T2)|Cs],
                       SubIn, SubOut, ErrIn, ErrOut) :-
    apply_subst_type(SubIn, T1, S1),
    apply_subst_type(SubIn, T2, S2),
    (   unify_type(S1, S2, SubIn, SubMid)
    ->  ErrMid = ErrIn
    ;   format(string(Msg), "Type mismatch: ~w vs ~w", [S1, S2]),
        SubMid = SubIn,
        append(ErrIn, [Msg], ErrMid)
    ),
    solve_constraints_list(Cs, SubMid, SubOut, ErrMid, ErrOut).

solve_constraints_list([_C|Cs], SubIn, SubOut, ErrIn, ErrOut) :-
    solve_constraints_list(Cs, SubIn, SubOut, ErrIn, ErrOut).

unify_type(t_int,  t_int,  Sub, Sub) :- !.
unify_type(t_atom, t_atom, Sub, Sub) :- !.
unify_type(t_bool, t_bool, Sub, Sub) :- !.

unify_type(t_list(T1), t_list(T2), SubIn, SubOut) :-
    !,
    unify_type(T1, T2, SubIn, SubOut).

unify_type(t_pred(N,A,Args1), t_pred(N,A,Args2), SubIn, SubOut) :-
    !,
    unify_arg_lists(Args1, Args2, SubIn, SubOut).

unify_type(t_var(Id), T, SubIn, SubOut) :-
    !,
    bind_var(Id, T, SubIn, SubOut).

unify_type(T, t_var(Id), SubIn, SubOut) :-
    !,
    bind_var(Id, T, SubIn, SubOut).

unify_type(T1, T2, _SubIn, _SubOut) :-
    debug_print_mismatch(T1, T2),
    fail.

unify_arg_lists([], [], Sub, Sub).
unify_arg_lists([T1|Ts1], [T2|Ts2], SubIn, SubOut) :-
    unify_type(T1, T2, SubIn, SubMid),
    unify_arg_lists(Ts1, Ts2, SubMid, SubOut).

bind_var(Id, T, SubIn, SubOut) :-
    (   T = t_var(Id)
    ->  SubOut = SubIn
    ;   occurs_in(Id, T, SubIn)
    ->  fail
    ;   SubOut = [Id-T | SubIn]
    ).

occurs_in(Id, t_var(Id), _Sub) :- !.
occurs_in(_Id, t_int,  _Sub) :- !, fail.
occurs_in(_Id, t_atom, _Sub) :- !, fail.
occurs_in(_Id, t_bool, _Sub) :- !, fail.
occurs_in(Id, t_list(T), Sub) :-
    !,
    occurs_in(Id, T, Sub).
occurs_in(Id, t_pred(_,_,Args), Sub) :-
    member(T, Args),
    occurs_in(Id, T, Sub).

/* ========== MESSAGGI DI ERRORE CONTESTUALIZZATI ====================== */
/* Generazione di messaggi di errore “legibili” a partire dai tipi. */

build_context_error(T1, T2, Goal, Msg) :-
    expected_from_type(T1, Exp1),
    expected_from_type(T2, Exp2),
    pick_wrong_type(T1, T2, WrongType),
    (   extract_wrong_argument(Goal, WrongType, WrongArg)
    ->  true
    ;   WrongArg = Goal
    ),
    (   WrongType == T1
    ->  Expected = Exp2
    ;   Expected = Exp1
    ),
    format(string(Msg),
       "'~w' is not of type '~w' in call '~w'",
       [WrongArg, Expected, Goal]).

expected_from_type(t_int,  'integer') :- !.
expected_from_type(t_atom, 'atom')    :- !.
expected_from_type(t_bool, 'bool')    :- !.
expected_from_type(t_list(_), 'list') :- !.
expected_from_type(_, 'unknown').

pick_wrong_type(t_int, T, T) :- !.
pick_wrong_type(T, t_int, T) :- !.
pick_wrong_type(T1, T2, T1)  :- T1 \= T2,
                                !.
pick_wrong_type(T1, _T2, T1).

extract_wrong_argument(Goal, WrongType, Arg) :-
    Goal =.. [_|Args],
    member(Arg, Args),
    matches_type(Arg, WrongType),
    !.

matches_type(X, t_int)  :- integer(X).
matches_type(X, t_atom) :- atom(X).
matches_type(X, t_bool) :- X == true ; X == false.
matches_type(_, t_list(_)) :- fail.
matches_type(_, t_var(_))  :- fail.

/* ================== APPLICARE SOSTITUZIONE ========================== */
/* Applica una sostituzione di tipo a tipi e ambiente. */

apply_subst_type(Subst, t_var(Id), TOut) :-
    ( member(Id-T, Subst) ->
        apply_subst_type(Subst, T, TOut)
    ; TOut = t_var(Id)
    ),
    !.
apply_subst_type(_Subst, t_int, t_int) :- !.
apply_subst_type(_Subst, t_atom, t_atom) :- !.
apply_subst_type(_Subst, t_bool, t_bool) :- !.
apply_subst_type(Subst, t_list(T), t_list(TOut)) :-
    !,
    apply_subst_type(Subst, T, TOut).
apply_subst_type(Subst, t_pred(N,A,Args), t_pred(N,A,ArgsOut)) :-
    !,
    apply_subst_type_list(Subst, Args, ArgsOut).
apply_subst_type(_, T, T).

apply_subst_type_list(_Subst, [], []).
apply_subst_type_list(Subst, [T|Ts], [T1|Ts1]) :-
    apply_subst_type(Subst, T, T1),
    apply_subst_type_list(Subst, Ts, Ts1).

apply_subst_env(Subst, EnvIn, EnvOut) :-
    maplist(apply_subst_env_entry(Subst), EnvIn, EnvOut).

apply_subst_env_entry(Subst, pred(N,A)-TypeIn, pred(N,A)-TypeOut) :-
    apply_subst_type(Subst, TypeIn, TypeOut).

/* ================= STAMPA TIPI ED ERRORI ============================= */
/* Stampa i tipi inferiti dei predicati e la lista di errori. */

is_builtin(member/2).
is_builtin(length/2).
is_builtin(append/3).
is_builtin(is_list/1).

print_env_types([]).
print_env_types([pred(Name,Arity)-Type | Rest]) :-
    (   is_builtin(Name/Arity)
    ->  true
    ;   format_pred_type(Name, Arity, Type, String),
        format("~w~n", [String])
    ),
    print_env_types(Rest).

format_pred_type(Name, _Arity,
                 t_pred(_,_,ArgTypes), String) :-
    maplist(type_to_atom, ArgTypes, ArgAtoms),
    atomic_list_concat(ArgAtoms, ', ', ArgsStr),
    format(string(String), "predicate ~w(~w).", [Name, ArgsStr]).

type_to_atom(t_int, 'integer').
type_to_atom(t_atom, 'atom').
type_to_atom(t_bool, 'bool').
type_to_atom(t_var(Id), Atom) :-
    format(atom(Atom), 'T~w', [Id]).
type_to_atom(t_list(T), Atom) :-
    type_to_atom(T, ElemAtom),
    format(atom(Atom), 'list(~w)', [ElemAtom]).
type_to_atom(t_pred(N,A,_), Atom) :-
    format(atom(Atom), 'pred(~w/~w)', [N,A]).

print_errors([]).
print_errors([Err | Rest]) :-
    format("Error: ~w~n", [Err]),
    print_errors(Rest).

/* ========================= DEBUG HELPERS ============================= */
/* Funzioni di supporto per stampare vincoli e mismatch in modalità debug. */

add_constraint(C, CIn, COut) :-
    append(CIn, [C], COut),
    debug_print_constraint(C).

debug_print_constraint(C) :-
    ( tc_debug(on) ->
        format("DEBUG constraint: ~w~n", [C])
    ; true ).

debug_print_mismatch(T1, T2) :-
    ( tc_debug(on) ->
        format("DEBUG mismatch trying to unify ~w and ~w~n", [T1, T2])
    ; true ).
