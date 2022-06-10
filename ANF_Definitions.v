(** Definition of Fsub (System F with subtyping).

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    Table of contents:
      - #<a href="##syntax">Syntax (pre-terms)</a>#
      - #<a href="##open">Opening</a>#
      - #<a href="##lc">Local closure</a>#
      - #<a href="##env">Environments</a>#
      - #<a href="##wf">Well-formedness</a>#
      - #<a href="##sub">Subtyping</a>#
      - #<a href="##typing_doc">Typing</a>#
      - #<a href="##values">Values</a>#
      - #<a href="##reduction">Reduction</a>#
      - #<a href="##auto">Automation</a>#
*)

Require Export Metatheory.

Require Import Coq.Init.Specif.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

(** We use a locally nameless representation for Fsub, where bound
    variables are represented as natural numbers (de Bruijn indices)
    and free variables are represented as [atom]s.  The type [atom],
    defined in the [Atom] library, represents names: there are
    infinitely many atoms, equality is decidable on atoms, and it is
    possible to generate an atom fresh for any given finite set of
    atoms.

    We say that the definitions below define pre-types ([typ]) and
    pre-expressions ([exp]), collectively pre-terms, since the
    datatypes admit terms, such as [(typ_all typ_top (typ_bvar 3))],
    where indices are unbound.  A term is locally closed when it
    contains no unbound indices.

    Note that indices for bound type variables are distinct from
    indices for bound expression variables.  We make this explicit in
    the definitions below of the opening operations. *)

Inductive typ : Set :=
  | typ_top : typ
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_prod : typ -> typ -> typ.

Inductive var : Set :=
  | var_b : nat -> var
  | var_f : atom -> var.

Inductive exp : Set :=
  | exp_var : var -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : var -> var -> exp
  | exp_tabs : typ -> exp -> exp
  | exp_tapp : var -> typ -> exp
  | exp_let : exp -> exp -> exp
  | exp_pair : var -> var -> exp
  | exp_fst : var -> exp
  | exp_snd : var -> exp.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion var_b : nat >-> var.
Coercion var_f : atom >-> var.
Coercion exp_var : var >-> exp.

(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.

    The notation used below for decidable equality on atoms and
    natural numbers (e.g., [K === J]) is defined in the [Metatheory]
    library.  The order of arguments to each "open" function is the
    same.  For example, [(open_tt_rec K U T)] can be read as
    "substitute [U] for index [K] in [T]."

    Note that we assume that [U] is locally closed (and similarly for
    the other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => if K === J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 T2 => typ_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | typ_prod T1 T2 => typ_prod (open_tt_rec K U T1) (open_tt_rec K U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_var v => v
  | exp_abs V e1 => exp_abs  (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app f x => exp_app f x
  | exp_tabs V e1 => exp_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | exp_tapp x V => exp_tapp x (open_tt_rec K U V)
  | exp_let e c => exp_let (open_te_rec K U e) (open_te_rec K U c)
  | exp_pair x1 x2 => exp_pair x1 x2
  | exp_fst x => exp_fst x
  | exp_snd x => exp_snd x
  end.

Definition open_vv_rec (k : nat) (y : atom) (v : var) : var :=
  match v with
  | var_b i => if k === i then var_f y else var_b i
  | var_f x => var_f x
  end.

Fixpoint open_ve_rec (k : nat) (y : atom) (e : exp) {struct e} : exp :=
  match e with
  | exp_var v => open_vv_rec k y v
  | exp_abs V e1 => exp_abs V (open_ve_rec (S k) y e1)
  | exp_app f x => exp_app (open_vv_rec k y f) (open_vv_rec k y x)
  | exp_tabs V e1 => exp_tabs V (open_ve_rec k y e1)
  | exp_tapp x V => exp_tapp (open_vv_rec k y x) V
  | exp_let e c => exp_let (open_ve_rec k y e) (open_ve_rec (S k) y c)
  | exp_pair x1 x2 => exp_pair (open_vv_rec k y x1) (open_vv_rec k y x2)
  | exp_fst x => exp_fst (open_vv_rec k y x)
  | exp_snd x => exp_snd (open_vv_rec k y x)
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ve e y := open_ve_rec 0 y e.
Definition open_vv v y := open_vv_rec 0 y v.

(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed we much
    check that [T1] is locally closed, and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2)
>>  or we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2)
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite
    quantification": we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)

Inductive type : typ -> Prop :=
  | type_top :
      type typ_top
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all T1 T2)
  | type_prod : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_prod T1 T2).

Inductive expr : exp -> Prop :=
  | expr_var : forall (x : atom),
      expr x
  | expr_abs : forall L T e,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ve e x)) ->
      expr (exp_abs T e)
  | expr_app : forall (x y : atom),
      expr (exp_app (var_f x) (var_f y))
  | expr_tabs : forall L T e,
      type T ->
      (forall X : atom, X `notin` L -> expr (open_te e X)) ->
      expr (exp_tabs T e)
  | expr_tapp : forall (x : atom) V,
      type V ->
      expr (exp_tapp x V)
  | expr_let : forall L e c,
      expr e ->
      (forall x : atom, x `notin` L -> expr (open_ve c x)) ->
      expr (exp_let e c)
  | expr_pair : forall (x y : atom),
      expr (exp_pair x y)
  | expr_fst : forall (x : atom),
      expr (exp_fst x)
  | expr_snd : forall (x : atom),
      expr (exp_snd x).

Definition scope (e : exp) :=
    { L : atoms & forall x, x `notin` L -> expr (open_ve e x) }.

(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The [Metatheory] and [Environment] libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  The [Environment] library treats environments
    as lists of type [list (atom * A)].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive binding : Set :=
  | bind_sub : typ -> binding
  | bind_typ : typ -> binding.

(** A binding [(X, bind_sub T)] records that a type variable [X] is a
    subtype of [T], and a binding [(x, bind_typ U)] records that an
    expression variable [x] has type [U].

    We define an abbreviation [env] for the type of environments, and
    an abbreviation [empty] for the empty environment.

    Note: Each instance of [Notation] below defines an abbreviation
    since the left-hand side consists of a single identifier that is
    not in quotes.  These abbreviations are used for both parsing (the
    left-hand side is equivalent to the right-hand side in all
    contexts) and printing (the right-hand side is pretty-printed as
    the left-hand side).  Since [nil] is normally a polymorphic
    constructor whose type argument is implicit, we prefix the name
    with "[@]" to signal to Coq that we are going to supply arguments
    to [nil] explicitly. *)

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(** We also define a notation that makes it convenient to write one
    element lists.  This notation is useful because of our convention
    for building environments; see the examples below. *)

Notation "[ x ]" := (x :: nil).

(** #<b>#Examples:#</b># We use a convention where environments are
    never built using a cons operation [((x, a) :: E)] where [E] is
    non-[nil].  This makes the shape of environments more uniform and
    saves us from excessive fiddling with the shapes of environments.
    For example, Coq's tactics sometimes distinguish between consing
    on a new binding and prepending a one element list, even though
    the two operations are convertible with each other.

    Consider the following environments written in informal notation.
<<
  1. (empty environment)
  2. x : T
  3. x : T, Y <: S
  4. E, x : T, F
>>  In the third example, we have an environment that binds an
    expression variable [x] to [T] and a type variable [Y] to [S].
    In Coq, we would write these environments as follows.
<<
  1. empty
  2. [(x, bind_typ T)]
  3. [(Y, bind_sub S)] ++ [(x, bind_typ T)]
  4. F ++ [(x, bind_typ T)] ++ E
>> The symbol "[++]" denotes list concatenation and associates to the
    right.  (That notation is defined in Coq's [List] library.)  Note
    that in Coq, environments grow on the left, since that is where
    the head of a list is. *)


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(** A type [T] is well-formed with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    Note: It is tempting to define the premise of [wf_typ_var] as [(X
    `in` dom E)], since that makes the rule easier to apply (no need
    to guess an instantiation for [U]).  Unfortunately, this is
    incorrect.  We need to check that [X] is bound as a type-variable,
    not an expression-variable; [(dom E)] does not distinguish between
    the two kinds of bindings. *)

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_top : forall E,
      wf_typ E typ_top
  | wf_typ_var : forall U E (X : atom),
      binds X (bind_sub U) E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_prod : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_prod T1 T2)
  | wf_typ_all : forall L E T1 T2,
      wf_typ E T1 ->
      (forall X : atom, X `notin` L ->
        wf_typ ([(X, bind_sub T1)] ++ E) (open_tt T2 X)) ->
      wf_typ E (typ_all T1 T2).

(** An environment E is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [ok]
    relation defined in the [Environment] library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_sub : forall (E : env) (X : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      X `notin` dom E ->
      wf_env ([(X, bind_sub T)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
      x `notin` dom E ->
      wf_env ([(x, bind_typ T)] ++ E).

(* ********************************************************************** *)
(** * #<a name="sub"></a># Subtyping *)

(** The definition of subtyping is straightforward.  It uses the
    [binds] relation from the [Environment] library (in the
    [sub_trans_tvar] case) and cofinite quantification (in the
    [sub_all] case). *)

Inductive sub : env -> typ -> typ -> Prop :=
  | sub_top : forall E S,
      wf_env E ->
      wf_typ E S ->
      sub E S typ_top
  | sub_refl_tvar : forall E X,
      wf_env E ->
      wf_typ E (typ_fvar X) ->
      sub E (typ_fvar X) (typ_fvar X)
  | sub_trans_tvar : forall U E T X,
      binds X (bind_sub U) E ->
      sub E U T ->
      sub E (typ_fvar X) T
  | sub_arrow : forall E S1 S2 T1 T2,
      sub E T1 S1 ->
      sub E S2 T2 ->
      sub E (typ_arrow S1 S2) (typ_arrow T1 T2)
  | sub_all : forall L E S1 S2 T1 T2,
      sub E T1 S1 ->
      (forall X : atom, X `notin` L ->
          sub ([(X, bind_sub T1)] ++ E) (open_tt S2 X) (open_tt T2 X)) ->
      sub E (typ_all S1 S2) (typ_all T1 T2)
  | sub_prod : forall E S1 S2 T1 T2,
      sub E S1 T1 ->
      sub E S2 T2 ->
      sub E (typ_prod S1 S2) (typ_prod T1 T2).

(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

(** The definition of typing is straightforward.  It uses the [binds]
    relation from the [Environment] library (in the [typing_var] case)
    and cofinite quantification in the cases involving binders (e.g.,
    [typing_abs] and [typing_tabs]). *)

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E (x : atom) T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E x T
  | typing_abs : forall L E V e T1,
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ V)] ++ E) (open_ve e x) T1) ->
      typing E (exp_abs V e) (typ_arrow V T1)
  | typing_app : forall T1 E (f x : atom) T2,
      typing E f (typ_arrow T1 T2) ->
      typing E x T1 ->
      typing E (exp_app f x) T2
  | typing_tabs : forall L E V e T1,
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_sub V)] ++ E) (open_te e X) (open_tt T1 X)) ->
      typing E (exp_tabs V e) (typ_all V T1)
  | typing_tapp : forall T1 E (x : atom) T T2,
      typing E x (typ_all T1 T2) ->
      sub E T T1 ->
      typing E (exp_tapp x T) (open_tt T2 T)
  | typing_let : forall L T1 T2 E e c,
      typing E e T1 ->
      (forall x : atom, x `notin` L -> typing ([(x, bind_typ T1)] ++ E) (open_ve c x) T2) ->
      typing E (exp_let e c) T2
  | typing_pair : forall T1 T2 E (x1 x2 : atom),
      typing E x1 T1 ->
      typing E x2 T2 ->
      typing E (exp_pair x1 x2) (typ_prod T1 T2)
  | typing_fst : forall T1 T2 E (x : atom),
      typing E x (typ_prod T1 T2) ->
      typing E (exp_fst x) T1
  | typing_snd : forall T1 T2 E (x : atom),
      typing E x (typ_prod T1 T2) ->
      typing E (exp_snd x) T2
  | typing_sub : forall S E e T,
      typing E e S ->
      sub E S T ->
      typing E e T.

(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T L e1,
      type T ->
      (forall x, x `notin` L -> expr (open_ve e1 x)) ->
      value (exp_abs T e1)
  | value_tabs : forall T L e1,
      type T ->
      (forall X, X `notin` L -> expr (open_te e1 X)) ->
      value (exp_tabs T e1)
  | value_pair : forall (x y : atom),
      value (exp_pair x y).

Inductive answer : exp -> Prop :=
  | answer_val : forall v,
      value v -> answer v
  | answer_var : forall (x : atom),
      answer x
  | answer_pair : forall (x y : atom),
      answer (exp_pair x y).

Definition store_frame : Set := (atom * { v | value v }).
Definition let' x v v_value : store_frame := (x, exist value v v_value).
Definition store_ctx : Set := list store_frame.
Definition stores (S : store_ctx) (x : atom) (v : exp) (v_value : value v) : Prop :=
    binds x (exist value v v_value) S.

Inductive eval_frame : Type :=
  | cont c : scope c -> eval_frame.
Definition eval_ctx : Type := (list eval_frame).

(*
Inductive store_ctx : env -> Set :=
  | store_ctx_nil : store_ctx nil
  | store_ctx_cons : forall E x v T,
      value v ->
      typing E v T ->
      store_ctx ([(x, bind_typ T)] ++ E).

Inductive eval_ctx (E : env) : typ -> typ -> Set :=
  | eval_ctx_nil : forall T, eval_ctx E T T
  | eval_ctx_cons : forall c T U V L,
      (forall x, x `notin` L -> typing ([(x, bind_typ T)] ++ E) (open_ve c x) U) ->
      eval_ctx E U V ->
      eval_ctx E T V.
*)

Record state : Type := mk_state {
  store_context : store_ctx;
  eval_context : eval_ctx;
  current_exp : exp
}.

Notation "⟨ S | E | e ⟩" := (mk_state S E e).

Definition init_state (e : exp) : state :=
  ⟨ nil | nil | e ⟩.

Definition final_state (s : state) : Prop :=
  s.(eval_context) = nil /\ answer s.(current_exp).

Inductive store_typing : store_ctx -> env -> Prop :=
  | typing_store_nil : store_typing nil nil
  | typing_store_cons : forall x T v v_value S Γ,
      store_typing S Γ ->
      typing Γ v T ->
      x `notin` dom Γ ->
      store_typing (let' x v v_value :: S) ([(x, bind_typ T)] ++ Γ).

Inductive eval_typing (Γ : env) : eval_ctx -> typ -> typ -> Prop :=
  | typing_eval_nil : forall T U, wf_env Γ -> sub Γ T U -> eval_typing Γ nil T U
  | typing_eval_cons : forall L T U V c (c_scope : scope c) E,
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ T)] ++ Γ) (open_ve c x) U) ->
      eval_typing Γ E U V ->
      eval_typing Γ (cont c c_scope :: E) T V.

Inductive state_typing (st : state) (U : typ) : Prop :=
  | typing_state : forall T Γ,
      store_typing st.(store_context) Γ ->
      eval_typing Γ st.(eval_context) T U ->
      typing Γ st.(current_exp) T ->
      state_typing st U.

Fixpoint dom_store (S : store_ctx) : atoms :=
    match S with
    | nil => {}
    | (x, _) :: S' => singleton x `union` dom_store S'
    end.

(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
    [fv_tt] and [fv_te] calculate the set of atoms used as free type
    variables in a type or expression, respectively.  The function
    [fv_ee] calculates the set of atoms used as free expression
    variables in an expression.  Cases involving binders are
    straightforward since bound variables are indices, not names, in
    locally nameless representation. *)

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_top => {}
  | typ_bvar J => {}
  | typ_fvar X => singleton X
  | typ_arrow T1 T2 => fv_tt T1 `union` fv_tt T2
  | typ_all T1 T2 => fv_tt T1 `union` fv_tt T2
  | typ_prod T1 T2 => fv_tt T1 `union` fv_tt T2
  end.
      
Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_var v => {}
  | exp_abs V e1  => fv_tt V `union` fv_te e1
  | exp_app f x => {}
  | exp_tabs V e1 => fv_tt V `union` fv_te e1
  | exp_tapp x V => fv_tt V
  | exp_let e c => fv_te e `union` fv_te c
  | exp_pair x1 x2 => {}
  | exp_fst x => {}
  | exp_snd x => {}
  end.
      
Definition fv_vv (v : var) : atoms :=
  match v with
  | var_b i => {}
  | var_f x => singleton x
  end.
      
Fixpoint fv_ve (e : exp) {struct e} : atoms :=
  match e with
  | exp_var v => fv_vv v
  | exp_abs V e1 => fv_ve e1
  | exp_app f x => fv_vv f `union` fv_vv x
  | exp_tabs V e1 => fv_ve e1
  | exp_tapp x V => fv_vv x
  | exp_let e c => fv_ve e `union` fv_ve c
  | exp_pair x1 x2 => fv_vv x1 `union` fv_vv x2
  | exp_fst x => fv_vv x
  | exp_snd x => fv_vv x
  end.

Fixpoint fv_tc (Γ : env) : atoms :=
  match Γ with
  | nil => {}
  | (x, bind_typ T) :: Δ => fv_tt T `union` fv_tc Δ
  | (x, bind_sub T) :: Δ => fv_tt T `union` fv_tc Δ
  end.

(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)
(*
Inductive red : state -> state -> Prop :=
  | red_lift : forall v S E x (c : exp) (c_scope : scope c) (v_value : value v),
      x `notin` (dom_store S `union` projT1 c_scope) ->
      red ⟨ S | cont c c_scope :: E | v ⟩
          ⟨ let' x v v_value :: S | E | open_ve c x ⟩
  | red_let_var : forall (x y : atom) c v v_value S E,
      stores S y v v_value ->
      x `notin` dom_store S ->
      red ⟨ S | E | exp_let y c ⟩
          ⟨ let' x v v_value :: S | E | open_ve c x ⟩
  | red_let_val : forall x v c S E (v_value : value v),
      x `notin` dom_store S ->
      red ⟨ S | E | exp_let v c ⟩
          ⟨ let' x v v_value :: S | E | open_ve c x ⟩
  | red_let_exp : forall e c S E (c_scope : scope c),
      red ⟨ S | E | exp_let e c ⟩
          ⟨ S | cont c c_scope :: E | e ⟩
  | red_app : forall (f x : atom) U e S E v (v_value : value v) (abs_value : value (exp_abs U e)),
      stores S f (exp_abs U e) abs_value ->
      stores S x v v_value ->
      red ⟨ S | E | exp_app f x ⟩
          ⟨ S | E | open_ve e x ⟩
  | red_tapp : forall x T U e S E (tabs_value : value (exp_tabs U e)),
      stores S x (exp_tabs U e) tabs_value ->
      type T ->
      red ⟨ S | E | exp_tapp x T ⟩
          ⟨ S | E | open_te e T ⟩
  | red_fst : forall x v1 v2 S E (pair_value : value (exp_pair v1 v2)),
      stores S x (exp_pair v1 v2) pair_value ->
      red ⟨ S | E | exp_fst x ⟩
          ⟨ S | E | v1 ⟩
  | red_snd : forall x v1 v2 S E (pair_value : value (exp_pair v1 v2)),
      stores S x (exp_pair v1 v2) pair_value ->
      red ⟨ S | E | exp_snd x ⟩
          ⟨ S | E | v2 ⟩.*)

Inductive red' (L : atoms) : state -> state -> Prop :=
  | red_lift' : forall v S E x (c : exp) (c_scope : scope c) (v_value : value v),
      x `notin` L ->
      red' L ⟨ S | cont c c_scope :: E | v ⟩
             ⟨ let' x v v_value :: S | E | open_ve c x ⟩
(* Cannot use this definition because we would need complicated lemmas about exchange rule.
  | red_let_var' : forall (x : atom) c (c_scope : scope c) v (v_value : value v) S E,
      stores S x v v_value ->
      red' L ⟨ S | cont c c_scope :: E | x ⟩
             ⟨ S | E | open_ve c x ⟩ *)
  | red_let_var' : forall (x y : atom) c (c_scope : scope c) v (v_value : value v) S E,
      stores S x v v_value ->
      y `notin` L ->
      red' L ⟨ S | cont c c_scope :: E | x ⟩
             ⟨ let' y v v_value :: S | E | open_ve c y ⟩
  | red_let_val' : forall x v c S E (v_value : value v),
      x `notin` L ->
      red' L ⟨ S | E | exp_let v c ⟩
             ⟨ let' x v v_value :: S | E | open_ve c x ⟩
  | red_let_exp' : forall e c S E (c_scope : scope c),
      red' L ⟨ S | E | exp_let e c ⟩
             ⟨ S | cont c c_scope :: E | e ⟩
  | red_app' : forall (f x : atom) U e S E v (v_value : value v) (abs_value : value (exp_abs U e)),
      stores S f (exp_abs U e) abs_value ->
      stores S x v v_value ->
      x `notin` L ->
      red' L ⟨ S | E | exp_app f x ⟩
             ⟨ S | E | open_ve e x ⟩
  | red_tapp' : forall x T U e S E (tabs_value : value (exp_tabs U e)),
      stores S x (exp_tabs U e) tabs_value ->
      type T ->
      x `notin` L ->
      red' L ⟨ S | E | exp_tapp x T ⟩
             ⟨ S | E | open_te e T ⟩
  | red_fst' : forall x x1 x2 S E (pair_value : value (exp_pair x1 x2)),
      stores S x (exp_pair x1 x2) pair_value ->
      red' L ⟨ S | E | exp_fst x ⟩
             ⟨ S | E | x1 ⟩
  | red_snd' : forall x x1 x2 S E (pair_value : value (exp_pair x1 x2)),
      stores S x (exp_pair x1 x2) pair_value ->
      red' L ⟨ S | E | exp_snd x ⟩
             ⟨ S | E | x2 ⟩.

(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

#[global]
Hint Constructors type expr wf_typ wf_env value answer red' : core.
#[global]
Hint Resolve sub_top sub_refl_tvar sub_arrow : core.
#[global]
Hint Resolve typing_var typing_app typing_tapp typing_sub : core.
