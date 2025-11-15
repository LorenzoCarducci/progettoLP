%%%% <917356> <Carducci> <Lorenzo>
%%%% Type checker minimale per Prolog (interi + variabili + liste + built-in + struct)
%%%% Versione con filtro predicati che generano errori (opzione B)

:- module(tc, [tc/1, tc_debug_on/0, tc_debug_off/0]).

:- dynamic next_type_var_id/1.
:- dynamic tc_debug/1.
:- dynamic last_errors/1.

next_type_var_id(0).
tc_debug(off).
last_errors([]).

tc_debug_on :-
    retractall(tc_debug(_)),
    asserta(tc_debug(on)).

tc_debug_off :-
    retractall(tc_debug(_)),
    asserta(tc_debug(off)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% ENTRY POINT
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

tc(File) :-
    retractall(next_type_var_id(_)),
    asserta(next_type_var_id(0)),
    retractall(last_errors(_)),
    asserta(last_errors([])),
    format("%%% Type checking '~w'.~n", [File]),
    read_program(File, Clauses),
    build_initial_env(Clauses, Env0),
    generate_constraints(Clauses, Env0, Constraints),
    solve_constraints(Constraints, Subst, Errors),
    retractall(last_errors(_)),
    asserta(last_errors(Errors)),
    apply_subst_env(Subst, Env0, EnvTyped),
    print_env_types(EnvTyped),
    print_errors(Errors).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% LETTURA PROGRAMMA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

read_program(File, Clauses) :-
    open(File, read, In),
    read_terms(In, Clauses),
    close(In).

read_terms(Stream, []) :-
    at_end_of_stream(Stream), !.
read_terms(Stream, [T|Ts]) :-
    read(Stream, Term),
    ( Term == end_of_file ->
        Ts = []
    ; T = Term,
      read_terms(Stream, Ts)
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% TYPE VAR
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

fresh_type_var(t_var(Id)) :-
    retract(next_type_var_id(Id0)),
    Id is Id0 + 1,
    asserta(next_type_var_id(Id)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% BUILT-IN
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

builtin_env(EnvBuiltin) :-
    fresh_type_var(T1),
    fresh_type_var(T2),
    fresh_type_var(T3),
    fresh_type_var(T4),
    EnvBuiltin =
      [ pred(member, 2) - t_pred(member, 2, [T1, t_list(T1)])
      , pred(length, 2) - t_pred(length, 2, [t_list(T2), t_int])
      , pred(append, 3) - t_pred(append, 3, [t_list(T3), t_list(T3), t_list(T3)])
      , pred(is_list, 1) - t_pred(is_list, 1, [t_list(T4)])
      ].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% ENV PREDICATI
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

build_initial_env(Clauses, Env) :-
    findall(Name/Arity,
            (member(Cl, Clauses),
             is_clause(Cl, Head, _),
             functor(Head, Name, Arity)),
            Pairs0),
    sort(Pairs0, Pairs),
    build_pred_entries(Pairs, EnvUser),
    builtin_env(EnvBuiltin),
    append(EnvBuiltin, EnvUser, Env).

is_clause((:- _), _, _) :- !, fail.
is_clause((Head :- Body), Head, Body) :- !, callable(Head).
is_clause(Head, Head, true) :- callable(Head).

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GENERAZIONE VINCOLI
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

generate_constraints(Clauses, Env, Constraints) :-
    generate_constraints_clauses(Clauses, Env, [], Constraints).

generate_constraints_clauses([], _, C, C).
generate_constraints_clauses([Cl|Rest], Env, CIn, COut) :-
    ( is_clause(Cl, Head, Body) ->
        gen_head_and_body_constraints(Head, Body, Env, CIn, CMid)
    ;   CMid = CIn ),
    generate_constraints_clauses(Rest, Env, CMid, COut).

gen_head_and_body_constraints(Head, Body, EnvPred, CIn, COut) :-
    term_variables((Head :- Body), Vars),
    make_var_env(Vars, VarEnv),
    functor(Head, Name, Arity),
    lookup_pred(EnvPred, Name, Arity, t_pred(_,_,PredArgTypes)),
    Head =.. [_|HeadArgs],
    gen_args_constraints(HeadArgs, PredArgTypes, VarEnv, CIn, CHead),
    gen_body_constraints(Body, EnvPred, VarEnv, CHead, COut).

make_var_env([], []).
make_var_env([V|Vs], [V-T | Rest]) :-
    fresh_type_var(T),
    make_var_env(Vs, Rest).

lookup_var_type([V-T|_], V, T) :- !.
lookup_var_type([_|Rest], V, T) :- lookup_var_type(Rest, V, T).
gen_args_constraints([], [], _, C, C).
gen_args_constraints([T|Ts], [Ty|Tys], VarEnv, CIn, COut) :-
    infer_term_type(T, VarEnv, TyTerm, CIn, C1),
    % vincolo normale di uguaglianza tra tipo del termine e tipo atteso
    add_constraint(eq(TyTerm, Ty), C1, C2),
    gen_args_constraints(Ts, Tys, VarEnv, C2, COut).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INFERENZA TIPI TERMINI  (VERSIONE CORRETTA – PATCH 1)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Interi
infer_term_type(Term, _, t_int, C, C) :- 
    integer(Term), !.

% Variabili
infer_term_type(Term, VarEnv, Ty, C, C) :-
    var(Term), !,
    lookup_var_type(VarEnv, Term, Ty).

% Booleani
infer_term_type(true, _, t_bool, C, C) :- !.
infer_term_type(false, _, t_bool, C, C) :- !.

% Lista vuota []
infer_term_type(Term, _, t_list(T), C, C) :-
    Term == [], !,
    fresh_type_var(T).

% Lista [H|T] – versione corretta che non produce mai t_list(T) = T
infer_term_type([H|T], VarEnv, t_list(TElem), CIn, COut) :- !,
    fresh_type_var(TElem),
    infer_term_type(H, VarEnv, TH, CIn, C1),
    infer_term_type(T, VarEnv, TT, C1, C2),
    add_constraint(eq(TH, TElem), C2, C3),
    add_constraint(eq(TT, t_list(TElem)), C3, COut).

% Structs / compound terms
infer_term_type(Term, VarEnv, t_struct(Name, ArgTypes), CIn, COut) :-
    compound(Term),
    Term \= [],
    Term \= [_|_],
    Term \= true,
    Term \= false,
    Term =.. [Name | Args],
    infer_term_list_types(Args, VarEnv, ArgTypes, CIn, COut), !.

% Atomi
infer_term_type(Term, _, t_atom, C, C) :- 
    atom(Term), !.

% Caso generico: nuovo tipo variabile
infer_term_type(_, _, Ty, C, C) :- 
    fresh_type_var(Ty).

% Lista di tipi (per struct)
infer_term_list_types([], _, [], C, C).
infer_term_list_types([A|As], VarEnv, [TA|TAs], CIn, COut) :-
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_list_types(As, VarEnv, TAs, C1, COut).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% CORPO CLAUSOLA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gen_body_constraints(true, _, _, C, C) :- !.

gen_body_constraints((G1 ; G2), EnvPred, VarEnv, CIn, COut) :- !,
    gen_body_constraints(G1, EnvPred, VarEnv, CIn, C1),
    gen_body_constraints(G2, EnvPred, VarEnv, CIn, C2),
    append(C1, C2, COut).

gen_body_constraints((G1, Gs), EnvPred, VarEnv, CIn, COut) :- !,
    gen_goal_constraints(G1, EnvPred, VarEnv, CIn, C1),
    gen_body_constraints(Gs, EnvPred, VarEnv, C1, COut).

gen_body_constraints(Goal, EnvPred, VarEnv, CIn, COut) :-
    gen_goal_constraints(Goal, EnvPred, VarEnv, CIn, COut).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% GOAL
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gen_goal_constraints((A = B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq(TA, TB), C2, COut).

gen_goal_constraints((A \= B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq(TA, TB), C2, COut).

gen_goal_constraints((A == B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq(TA, TB), C2, COut).

gen_goal_constraints((A \== B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    add_constraint(eq(TA, TB), C2, COut).

% confronti numerici (PATCH 3)
gen_goal_constraints((A > B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    eq_force_int(TA, C2, C3),
    eq_force_int(TB, C3, COut).

gen_goal_constraints((A < B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    eq_force_int(TA, C2, C3),
    eq_force_int(TB, C3, COut).

gen_goal_constraints((A >= B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    eq_force_int(TA, C2, C3),
    eq_force_int(TB, C3, COut).

gen_goal_constraints((A =< B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    eq_force_int(TA, C2, C3),
    eq_force_int(TB, C3, COut).

gen_goal_constraints((A =:= B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    eq_force_int(TA, C2, C3),
    eq_force_int(TB, C3, COut).

gen_goal_constraints((A =\= B), _, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    eq_force_int(TA, C2, C3),
    eq_force_int(TB, C3, COut).

% X is Expr
gen_goal_constraints((X is Expr), _, VarEnv, CIn, COut) :- !,
    infer_term_type(X, VarEnv, TX, CIn, C1),
    infer_arith_expr_type(Expr, VarEnv, TExpr, C1, C2),
    eq_force_int(TX, C2, C3),
    eq_force_int(TExpr, C3, COut).

gen_goal_constraints(!, _, _, C, C) :- !.
gen_goal_constraints(fail, _, _, C, C) :- !.

gen_goal_constraints(\+ G, Env, VarEnv, CIn, COut) :- !,
    gen_body_constraints(G, Env, VarEnv, CIn, COut).

gen_goal_constraints(Goal, EnvPred, VarEnv, CIn, COut) :-
    functor(Goal, Name, Arity),
    lookup_pred(EnvPred, Name, Arity, t_pred(_,_,ArgTypes)),
    Goal =.. [_|Args],
    gen_args_constraints(Args, ArgTypes, VarEnv, CIn, COut).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% ESPRESSIONI ARITMETICHE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

infer_arith_expr_type(Expr, _, t_int, C, C) :- integer(Expr), !.

infer_arith_expr_type(Expr, VarEnv, Ty, C, C) :-
    var(Expr), !,
    lookup_var_type(VarEnv, Expr, Ty).

infer_arith_expr_type(Expr, VarEnv, t_int, CIn, COut) :-
    Expr =.. [Op, A, B],
    member(Op, [+, -, *, /]), !,
    infer_arith_expr_type(A, VarEnv, TA, CIn, C1),
    infer_arith_expr_type(B, VarEnv, TB, C1, C2),
    eq_force_int(TA, C2, C3),
    eq_force_int(TB, C3, COut).

infer_arith_expr_type(_, _, Ty, C, C) :-
    fresh_type_var(Ty).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% RISOLUZIONE VINCOLI
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve_constraints(Constraints, Subst, Errors) :-
    solve_constraints_list(Constraints, [], Subst, [], Errors).

solve_constraints_list([], Sub, Sub, Err, Err).
solve_constraints_list([eq(T1,T2)|Cs], SubIn, SubOut, ErrIn, ErrOut) :-
    apply_subst_type(SubIn, T1, S1),
    apply_subst_type(SubIn, T2, S2),
    ( unify_type(S1, S2, SubIn, SubMid, NewErrs) ->
        append(ErrIn, NewErrs, ErrMid),
        solve_constraints_list(Cs, SubMid, SubOut, ErrMid, ErrOut)
    ;   format(string(Msg), "Type mismatch in ???: ~w vs ~w", [S1, S2]),
        append(ErrIn, [Msg], ErrMid),
        solve_constraints_list(Cs, SubIn, SubOut, ErrMid, ErrOut)
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% EQ_FORCE_INT – forza un tipo a intero in modo sicuro (PATCH 3)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Non si possono fare confronti numerici su una lista
eq_force_int(t_list(_), C, C) :- !, fail.

% Né su struct
eq_force_int(t_struct(_, _), C, C) :- !, fail.

% Né su predicati
eq_force_int(t_pred(_,_,_), C, C) :- !, fail.

% Caso valido: forza il tipo ad essere integer
eq_force_int(T, CIn, COut) :-
    add_constraint(eq(T, t_int), CIn, COut).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% UNIFICAZIONE TIPI (VERSIONE ROBUSTA – PATCH 4)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Base types
unify_type(t_int, t_int, Sub, Sub, []) :- !.
unify_type(t_atom, t_atom, Sub, Sub, []) :- !.
unify_type(t_bool, t_bool, Sub, Sub, []) :- !.

% Liste: devono essere liste da entrambe le parti
unify_type(t_list(T1), t_list(T2), SubIn, SubOut, Errs) :- !,
    unify_type(T1, T2, SubIn, SubOut, Errs).

% Structs: nome e numero argomenti devono combaciare
unify_type(t_struct(N, Args1), t_struct(N, Args2), SubIn, SubOut, Errs) :- !,
    unify_arg_lists(Args1, Args2, SubIn, SubOut, Errs).

% Predicati: nome/arity devono combaciare
unify_type(t_pred(N,A,Args1), t_pred(N,A,Args2), SubIn, SubOut, Errs) :- !,
    unify_arg_lists(Args1, Args2, SubIn, SubOut, Errs).

% Variabile di tipo a sinistra
unify_type(t_var(Id), T, SubIn, SubOut, []) :- !,
    bind_var(Id, T, SubIn, SubOut).

% Variabile di tipo a destra
unify_type(T, t_var(Id), SubIn, SubOut, []) :- !,
    bind_var(Id, T, SubIn, SubOut).

% Casi vietati espliciti (per evitare errori a cascata)
unify_type(t_list(_), t_int, Sub, Sub, ["Type mismatch: list vs integer"]) :- !.
unify_type(t_int, t_list(_), Sub, Sub, ["Type mismatch: integer vs list"]) :- !.

unify_type(t_list(_), t_atom, Sub, Sub, ["Type mismatch: list vs atom"]) :- !.
unify_type(t_atom, t_list(_), Sub, Sub, ["Type mismatch: atom vs list"]) :- !.

unify_type(t_list(_), t_struct(N,_), Sub, Sub, [Msg]) :- !,
    format(string(Msg), "Type mismatch: list vs struct(~w)", [N]).
unify_type(t_struct(N,_), t_list(_), Sub, Sub, [Msg]) :- !,
    format(string(Msg), "Type mismatch: struct(~w) vs list", [N]).

unify_type(t_pred(N,A,_), t_list(_), Sub, Sub, [Msg]) :- !,
    format(string(Msg), "Type mismatch: pred(~w/~w) vs list", [N,A]).
unify_type(t_list(_), t_pred(N,A,_), Sub, Sub, [Msg]) :- !,
    format(string(Msg), "Type mismatch: list vs pred(~w/~w)", [N,A]).

% Caso finale: mismatch generale
unify_type(T1, T2, Sub, Sub, [Msg]) :-
    format(string(Msg), "Type mismatch: ~w vs ~w", [T1, T2]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% BIND VAR + OCCURS CHECK (PATCH 4 ROBUSTA)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

bind_var(Id, T, SubIn, SubOut) :-
    % Caso banale: t_var(Id) = t_var(Id)
    ( T = t_var(Id) ->
        SubOut = SubIn

    % Occurs check: impedisce ricorsioni come T = list(T)
    ; occurs_in(Id, T, SubIn) ->
        fail

    % Binding illegale: non puoi assegnare predicati/struct come tipo
    ; invalid_binding(Id, T) ->
        fail

    % Caso normale: aggiungi il binding Id -> T
    ; SubOut = [Id-T | SubIn]
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% INVALID BINDING – tipi che NON possono essere assegnati a variabili
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Non puoi unificare una variabile di tipo con un tipo predicativo
invalid_binding(_, t_pred(_,_,_)) :- !.

% Non puoi unificare una variabile con una struct: non è un tipo di dato primitivo
invalid_binding(_, t_struct(_, _)) :- !.

% Puoi unificare con le liste → quindi FAIL (perché questa definizione significa “NON invalid”)
invalid_binding(_, t_list(_)) :- fail.

% Tutto il resto è valido → FAIL
invalid_binding(_, _) :- fail.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% OCCURS-IN – controlla se una variabile compare ricorsivamente in un tipo
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

occurs_in(Id, t_var(Id), _) :- !.   % stesso id → ricorsione vietata

occurs_in(_, t_int, _) :- !, fail.
occurs_in(_, t_atom, _) :- !, fail.
occurs_in(_, t_bool, _) :- !, fail.

% Lista → controlla l’elemento interno
occurs_in(Id, t_list(T), Sub) :- !,
    occurs_in(Id, T, Sub).

% Struct → controlla ogni argomento
occurs_in(Id, t_struct(_, Args), Sub) :- !,
    member(T, Args),
    occurs_in(Id, T, Sub).

% Predicato → controlla ogni argomento
occurs_in(Id, t_pred(_,_,Args), Sub) :-
    member(T, Args),
    occurs_in(Id, T, Sub).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% STAMPA TIPI ED ERRORI
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

is_builtin(member/2).
is_builtin(length/2).
is_builtin(append/3).
is_builtin(is_list/1).

print_env_types([]).
print_env_types([pred(Name,Arity)-Type | Rest]) :-
    (   is_builtin(Name/Arity)
    ->  true
    ;   pred_has_error(Name,Arity)
    ->  true       % NON stampare predicati con errori
    ;   format_pred_type(Name, Arity, Type, String),
        format("~w~n", [String])
    ),
    print_env_types(Rest).

pred_has_error(Name,Arity) :-
    last_errors(Errors),
    atom_concat(Name, '/', N0),
    number_string(Arity, As),
    atom_concat(N0, As, PredId),
    member(M, Errors),
    sub_atom(M, _, _, _, PredId), !.

format_pred_type(Name, _, t_pred(_,_,ArgTypes), String) :-
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
type_to_atom(t_struct(N,Args), Atom) :-
    maplist(type_to_atom, Args, ArgAtoms),
    atomic_list_concat(ArgAtoms, ', ', ArgsStr),
    format(atom(Atom), '~w(~w)', [N, ArgsStr]).
type_to_atom(t_pred(N,A,_), Atom) :-
    format(atom(Atom), 'pred(~w/~w)', [N,A]).

print_errors([]).
print_errors([Err|Rest]) :-
    format("Error: ~w~n", [Err]),
    print_errors(Rest).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% APPLICAZIONE DI UNA SOSTITUZIONE A TIPI ED AMBIENTE
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% apply_subst_type(+Subst, +TypeIn, -TypeOut)
% Subst è una lista di coppie Id-Tipo (es. [3-t_int, 5-t_list(t_int), ...])

apply_subst_type(_, t_int, t_int).
apply_subst_type(_, t_atom, t_atom).
apply_subst_type(_, t_bool, t_bool).

% Variabile di tipo: se c'è un binding Id-T in Subst, applicalo ricorsivamente
apply_subst_type(Sub, t_var(Id), TypeOut) :-
    (   member(Id-T, Sub)
    ->  apply_subst_type(Sub, T, TypeOut)
    ;   TypeOut = t_var(Id)
    ).

% Liste
apply_subst_type(Sub, t_list(T), t_list(TS)) :-
    apply_subst_type(Sub, T, TS).

% Struct
apply_subst_type(Sub, t_struct(Name, Args), t_struct(Name, ArgsS)) :-
    apply_subst_type_list(Sub, Args, ArgsS).

% Predicati
apply_subst_type(Sub, t_pred(Name,Arity,Args), t_pred(Name,Arity,ArgsS)) :-
    apply_subst_type_list(Sub, Args, ArgsS).

% Helper per liste di tipi
apply_subst_type_list(_, [], []).
apply_subst_type_list(Sub, [T|Ts], [TS|TSs]) :-
    apply_subst_type(Sub, T, TS),
    apply_subst_type_list(Sub, Ts, TSs).

% apply_subst_env(+Subst, +EnvIn, -EnvOut)
% Applica la sostituzione all'ambiente dei predicati

apply_subst_env(_, [], []).
apply_subst_env(Sub, [pred(Name,Arity)-TypeIn | Rest],
                     [pred(Name,Arity)-TypeOut | RestS]) :-
    apply_subst_type(Sub, TypeIn, TypeOut),
    apply_subst_env(Sub, Rest, RestS).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% DEBUG
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

add_constraint(C, CIn, [C|CIn]) :-
    debug_print_constraint(C).

debug_print_constraint(C) :-
    ( tc_debug(on) ->
        format("DEBUG constraint: ~w~n", [C])
    ; true ).

debug_print_mismatch(T1, T2) :-
    ( tc_debug(on) ->
        format("DEBUG mismatch trying to unify ~w and ~w~n", [T1, T2])
    ; true ).
