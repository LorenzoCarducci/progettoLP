%%%% <Matricola> <Cognome> <Nome>
%%%% Type checker minimale per Prolog (solo interi + variabili)

:- module(tc, [tc/1]).

:- dynamic next_type_var_id/1.
next_type_var_id(0).

/* ============================ ENTRY POINT ============================ */
% Tipi:
%   t_int                intero
%   t_atom               atomo
%   t_var(Id)            variabile di tipo
%   t_pred(Name,Arity,ArgsTypes)   tipo di predicato

% tc(+File).
% Esempio:
%   ?- tc('fact.pl').

tc(File) :-
    % reset contatore variabili di tipo
    retractall(next_type_var_id(_)),
    asserta(next_type_var_id(0)),
    format("%%% Type checking '~w'.~n", [File]),
    read_program(File, Clauses),
    build_initial_env(Clauses, Env0),
    generate_constraints(Clauses, Env0, Constraints),
    solve_constraints(Constraints, Subst, Errors),
    apply_subst_env(Subst, Env0, EnvTyped),
    print_env_types(EnvTyped),
    print_errors(Errors).

/* =========================== LETTURA FILE ============================ */

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

/* ========================= TYPE VAR & TIPI =========================== */

% Tipi:
%   t_int                intero
%   t_var(Id)            variabile di tipo
%   t_pred(Name,Arity,ArgsTypes)   tipo di predicato

fresh_type_var(t_var(Id)) :-
    retract(next_type_var_id(Id0)),
    Id is Id0 + 1,
    asserta(next_type_var_id(Id)).

/* ===================== AMBIENTE DEI PREDICATI ======================= */

% Env = [ pred(Name,Arity) - t_pred(Name,Arity,ArgTypes), ... ]

build_initial_env(Clauses, Env) :-
    findall(Name/Arity,
            ( member(Cl, Clauses),
              is_clause(Cl, Head, _Body),
              functor(Head, Name, Arity)
            ),
            Pairs0),
    sort(Pairs0, Pairs),
    build_pred_entries(Pairs, Env).

% is_clause(+Term, -Head, -Body)
% Normalizza:
%   p(...) :- B     -> Head=p(...), Body=B
%   p(...).        -> Head=p(...), Body=true
%   direttive :- ... vengono ignorate (fail)

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

/* ===================== GENERAZIONE VINCOLI ========================== */

% Vincoli: eq(T1, T2)

generate_constraints(Clauses, Env, Constraints) :-
    generate_constraints_clauses(Clauses, Env, [], Constraints).

generate_constraints_clauses([], _Env, C, C).
generate_constraints_clauses([Cl|Rest], Env, CIn, COut) :-
    ( is_clause(Cl, Head, Body) ->
        gen_head_and_body_constraints(Head, Body, Env, CIn, CMid)
    ;   % direttive o roba che non ci interessa
        CMid = CIn
    ),
    generate_constraints_clauses(Rest, Env, CMid, COut).

% Una clausola: Head :- Body

gen_head_and_body_constraints(Head, Body, EnvPred, CIn, COut) :-
    % variabili logiche della clausola
    term_variables((Head :- Body), Vars),
    make_var_env(Vars, VarEnv),
    % testa
    functor(Head, Name, Arity),
    lookup_pred(EnvPred, Name, Arity, t_pred(_,_,PredArgTypes)),
    Head =.. [_|HeadArgs],
    gen_args_constraints(HeadArgs, PredArgTypes, VarEnv, CIn, CHead),
    % corpo
    gen_body_constraints(Body, EnvPred, VarEnv, CHead, COut).

% ambiente delle variabili logiche: VarEnv = [Var - TypeVar, ...]

make_var_env([], []).
make_var_env([V|Vs], [V-T | Rest]) :-
    fresh_type_var(T),
    make_var_env(Vs, Rest).

lookup_var_type([V-T|_], V, T) :- !.
lookup_var_type([_|Rest], V, T) :-
    lookup_var_type(Rest, V, T).

% vincoli sugli argomenti (testa o chiamata a predicato)

gen_args_constraints([], [], _VarEnv, C, C).
gen_args_constraints([T|Ts], [Ty|Tys], VarEnv, CIn, COut) :-
    infer_term_type(T, VarEnv, TyTerm, CIn, C1),
    C2 = [eq(TyTerm, Ty) | C1],
    gen_args_constraints(Ts, Tys, VarEnv, C2, COut).

/* ================== INFERENZA TIPO TERMINI SEMPLICI ================== */
% infer_term_type(+Term, +VarEnv, -Type, +CIn, -COut)

% intero
infer_term_type(Term, _VarEnv, t_int, C, C) :-
    integer(Term), !.

% variabile logica
infer_term_type(Term, VarEnv, Ty, C, C) :-
    var(Term), !,
    lookup_var_type(VarEnv, Term, Ty).

% atomo
infer_term_type(Term, _VarEnv, t_atom, C, C) :-
    atom(Term), !.

% qualsiasi altra cosa (per ora): nuova variabile di tipo
infer_term_type(_Term, _VarEnv, Ty, C, C) :-
    fresh_type_var(Ty).


/* ================== VINCOLI PER IL CORPO DELLA CLAUSOLA ============== */

% gen_body_constraints(+Body, +EnvPred, +VarEnv, +CIn, -COut)

gen_body_constraints(true, _EnvPred, _VarEnv, C, C) :- !.
gen_body_constraints((G1, Gs), EnvPred, VarEnv, CIn, COut) :- !,
    gen_goal_constraints(G1, EnvPred, VarEnv, CIn, C1),
    gen_body_constraints(Gs, EnvPred, VarEnv, C1, COut).
gen_body_constraints(Goal, EnvPred, VarEnv, CIn, COut) :-
    gen_goal_constraints(Goal, EnvPred, VarEnv, CIn, COut).

% gen_goal_constraints(+Goal, +EnvPred, +VarEnv, +CIn, -COut)

% confronti numerici: >, <, >=, =<, =:=, =\=

gen_goal_constraints((A > B), _EnvPred, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    COut = [eq(TA, t_int), eq(TB, t_int) | C2].

gen_goal_constraints((A < B), _EnvPred, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    COut = [eq(TA, t_int), eq(TB, t_int) | C2].

gen_goal_constraints((A >= B), _EnvPred, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    COut = [eq(TA, t_int), eq(TB, t_int) | C2].

gen_goal_constraints((A =< B), _EnvPred, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    COut = [eq(TA, t_int), eq(TB, t_int) | C2].

gen_goal_constraints((A =:= B), _EnvPred, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    COut = [eq(TA, t_int), eq(TB, t_int) | C2].

gen_goal_constraints((A =\= B), _EnvPred, VarEnv, CIn, COut) :- !,
    infer_term_type(A, VarEnv, TA, CIn, C1),
    infer_term_type(B, VarEnv, TB, C1, C2),
    COut = [eq(TA, t_int), eq(TB, t_int) | C2].

% X is Expr

gen_goal_constraints((X is Expr), _EnvPred, VarEnv, CIn, COut) :- !,
    infer_term_type(X, VarEnv, TX, CIn, C1),
    infer_arith_expr_type(Expr, VarEnv, TExpr, C1, C2),
    COut = [eq(TX, t_int), eq(TExpr, t_int) | C2].

% chiamata a predicato utente: p(...)

gen_goal_constraints(Goal, EnvPred, VarEnv, CIn, COut) :-
    functor(Goal, Name, Arity),
    lookup_pred(EnvPred, Name, Arity, t_pred(_,_,ArgTypes)),
    Goal =.. [_|Args],
    gen_args_constraints(Args, ArgTypes, VarEnv, CIn, COut).

/* ================= TIPO ESPRESSIONI ARITMETICHE ====================== */

% infer_arith_expr_type(+Expr, +VarEnv, -Type, +CIn, -COut)

infer_arith_expr_type(Expr, _VarEnv, t_int, C, C) :-
    integer(Expr), !.

infer_arith_expr_type(Expr, VarEnv, Ty, C, C) :-
    var(Expr), !,
    lookup_var_type(VarEnv, Expr, Ty).

infer_arith_expr_type(Expr, VarEnv, t_int, CIn, COut) :-
    Expr =.. [Op, A, B],
    member(Op, [+, -, *, /]), !,
    infer_arith_expr_type(A, VarEnv, TA, CIn, C1),
    infer_arith_expr_type(B, VarEnv, TB, C1, C2),
    COut = [eq(TA, t_int), eq(TB, t_int) | C2].

% qualunque altra espressione: assegnamo un nuovo tipo variabile
infer_arith_expr_type(_Expr, _VarEnv, Ty, C, C) :-
    fresh_type_var(Ty).

/* =================== RISOLUZIONE VINCOLI (UNIFY) ===================== */

% solve_constraints(+Constraints, -Subst, -Errors)

solve_constraints(Constraints, Subst, Errors) :-
    solve_constraints_list(Constraints, [], Subst, [], Errors).

solve_constraints_list([], Sub, Sub, Err, Err).
solve_constraints_list([eq(T1,T2)|Cs], SubIn, SubOut, ErrIn, ErrOut) :-
    apply_subst_type(SubIn, T1, S1),
    apply_subst_type(SubIn, T2, S2),
    ( unify_type(S1, S2, SubIn, SubMid, NewErrs) ->
        append(ErrIn, NewErrs, ErrMid),
        solve_constraints_list(Cs, SubMid, SubOut, ErrMid, ErrOut)
    ;   % occurs-check fallito
        format(string(Msg), "Cannot unify types ~w and ~w", [S1, S2]),
        append(ErrIn, [Msg], ErrMid),
        solve_constraints_list(Cs, SubIn, SubOut, ErrMid, ErrOut)
    ).

% unify_type(+T1, +T2, +SubIn, -SubOut, -Errors)
unify_type(t_int, t_int, Sub, Sub, []) :- !.
unify_type(t_atom, t_atom, Sub, Sub, []) :- !.

unify_type(t_var(Id), T, SubIn, SubOut, []) :- !,
    bind_var(Id, T, SubIn, SubOut).
unify_type(T, t_var(Id), SubIn, SubOut, []) :- !,
    bind_var(Id, T, SubIn, SubOut).

unify_type(t_pred(N,A,Args1), t_pred(N,A,Args2), SubIn, SubOut, Errs) :- !,
    unify_arg_lists(Args1, Args2, SubIn, SubOut, Errs).

% tipi incompatibili: registriamo errore, ma non falliamo
unify_type(T1, T2, Sub, Sub, [Msg]) :-
    format(string(Msg), "Type mismatch: ~w vs ~w", [T1, T2]).


bind_var(Id, T, SubIn, SubOut) :-
    ( T = t_var(Id) ->
        SubOut = SubIn
    ; occurs_in(Id, T, SubIn) ->
        fail
    ; SubOut = [Id-T | SubIn]
    ).

occurs_in(Id, t_var(Id), _Sub) :- !.
occurs_in(_Id, t_int, _Sub) :- !, fail.
occurs_in(Id, t_pred(_,_,Args), Sub) :-
    member(T, Args),
    occurs_in(Id, T, Sub).

unify_arg_lists([], [], Sub, Sub, []).
unify_arg_lists([T1|Ts1], [T2|Ts2], SubIn, SubOut, Errs) :-
    unify_type(T1, T2, SubIn, SubMid, Err1),
    unify_arg_lists(Ts1, Ts2, SubMid, SubOut, Err2),
    append(Err1, Err2, Errs).

/* ================== APPLICARE SOSTITUZIONE ========================== */

apply_subst_type(Subst, t_var(Id), TOut) :-
    ( member(Id-T, Subst) ->
        apply_subst_type(Subst, T, TOut)
    ; TOut = t_var(Id)
    ), !.
apply_subst_type(_Subst, t_int, t_int) :- !.
apply_subst_type(Subst, t_pred(N,A,Args), t_pred(N,A,ArgsOut)) :- !,
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

/* ================= STAMPA TIPI ED ERRORI ============================ */

print_env_types([]).
print_env_types([pred(Name,Arity)-Type | Rest]) :-
    format_pred_type(Name, Arity, Type, String),
    format("~w~n", [String]),
    print_env_types(Rest).

format_pred_type(Name, _Arity,
                 t_pred(_,_,ArgTypes), String) :-
    maplist(type_to_atom, ArgTypes, ArgAtoms),
    atomic_list_concat(ArgAtoms, ', ', ArgsStr),
    format(string(String), "predicate ~w(~w).", [Name, ArgsStr]).

type_to_atom(t_int, 'integer').
type_to_atom(t_atom, 'atom').
type_to_atom(t_var(Id), Atom) :-
    format(atom(Atom), 'T~w', [Id]).
type_to_atom(t_pred(N,A,_), Atom) :-
    format(atom(Atom), 'pred(~w/~w)', [N,A]).

print_errors([]).
print_errors([Err | Rest]) :-
    format("Error: ~w~n", [Err]),
    print_errors(Rest).
