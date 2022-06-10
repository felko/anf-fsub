(** Infrastructure lemmas and tactic definitions for Fsub.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of definitions, tactics, and lemmas
    that are based only on the syntax of the language at hand.  While
    the exact statements of everything here would change for a
    different language, the general structure of this file (i.e., the
    sequence of definitions, tactics, and lemmas) would remain the
    same.

    Table of contents:
      - #<a href="##fv">Free variables</a>#
      - #<a href="##subst">Substitution</a>#
      - #<a href="##pick_fresh">The "pick fresh" tactic</a>#
      - #<a href="##apply_fresh">The "pick fresh and apply" tactic</a>#
      - #<a href="##properties">Properties of opening and substitution</a>#
      - #<a href="##lc">Local closure is preserved under substitution</a>#
      - #<a href="##auto">Automation</a># *)

Require Export ANF_Definitions.

Require Import Coq.Arith.Peano_dec.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

(** In this section, we define substitution for expression and type
    variables appearing in types, expressions, and environments.
    Substitution differs from opening because opening replaces indices
    whereas substitution replaces free variables.  The definitions
    below are relatively simple for two reasons.
      - We are using locally nameless representation, where bound
        variables are represented using indices.  Thus, there is no
        need to rename variables to avoid capture.
      - The definitions below assume that the term being substituted
        in, i.e., the second argument to each function, is locally
        closed.  Thus, there is no need to shift indices when passing
        under a binder. *)

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_arrow T1 T2 => typ_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all T1 T2 => typ_all (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_prod T1 T2 => typ_prod (subst_tt Z U T1) (subst_tt Z U T2)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_var v => exp_var v
  | exp_abs V e1 => exp_abs (subst_tt Z U V)  (subst_te Z U e1)
  | exp_app f x => exp_app f x
  | exp_tabs V e1 => exp_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | exp_tapp x V => exp_tapp x (subst_tt Z U V)
  | exp_let e c => exp_let (subst_te Z U e) (subst_te Z U c)
  | exp_pair x1 x2 => exp_pair x1 x2
  | exp_fst x => exp_fst x
  | exp_snd x => exp_snd x
  end.

Definition subst_vv (z : atom) (y : atom) (v : var) : var :=
  match v with
  | var_b i => var_b i
  | var_f x => if x == z then y else x
  end.

Fixpoint subst_ve (z : atom) (y : atom) (e : exp) {struct e} : exp :=
  match e with
  | exp_var v => subst_vv z y v
  | exp_abs V e1 => exp_abs V (subst_ve z y e1)
  | exp_app f x => exp_app (subst_vv z y f) (subst_vv z y x)
  | exp_tabs V e1 => exp_tabs V (subst_ve z y e1)
  | exp_tapp x V => exp_tapp (subst_vv z y x) V
  | exp_let e c => exp_let (subst_ve z y e) (subst_ve z y c)
  | exp_pair x1 x2 => exp_pair (subst_vv z y x1) (subst_vv z y x2)
  | exp_fst x => exp_fst (subst_vv z y x)
  | exp_snd x => exp_snd (subst_vv z y x)
  end.

Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

(* ********************************************************************** *)
(** * #<a name="pick_fresh"></a># The "[pick fresh]" tactic *)

(** The "[pick fresh]" tactic introduces a fresh atom into the context.
    We define it in two steps.

    The first step is to define an auxiliary tactic [gather_atoms],
    meant to be used in the definition of other tactics, which returns
    a set of atoms in the current context.  The definition of
    [gather_atoms] follows a pattern based on repeated calls to
    [gather_atoms_with].  The one argument to this tactic is a
    function that takes an object of some particular type and returns
    a set of atoms that appear in that argument.  It is not necessary
    to understand exactly how [gather_atoms_with] works.  If we add a
    new inductive datatype, say for kinds, to our language, then we
    would need to modify [gather_atoms].  On the other hand, if we
    merely add a new type, say products, then there is no need to
    modify [gather_atoms]; the required changes would be made in
    [fv_tt]. *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_te x) in
  let D := gather_atoms_with (fun x : var => fv_vv x) in
  let E := gather_atoms_with (fun x : exp => fv_ve x) in
  let F := gather_atoms_with (fun x : typ => fv_tt x) in
  let G := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).

(** The second step in defining "[pick fresh]" is to define the tactic
    itself.  It is based on the [(pick fresh ... for ...)] tactic
    defined in the [Atom] library.  Here, we use [gather_atoms] to
    construct the set [L] rather than leaving it to the user to
    provide.  Thus, invoking [(pick fresh x)] introduces a new atom
    [x] into the current context that is fresh for "everything" in the
    context. *)

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

(* *********************************************************************** *)
(** * #<a name="apply_fresh"></a># The "[pick fresh and apply]" tactic *)

(** This tactic is implementation specific only because of its
    reliance on [gather_atoms], which is itself implementation
    specific.  The definition below may be copied between developments
    without any changes, assuming that the other other developments
    define an appropriate [gather_atoms] tactic.  For documentation on
    the tactic on which the one below is based, see the
    [Metatheory] library. *)

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.

(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)

(** The following lemmas provide useful structural properties of
    substitution and opening.  While the exact statements are language
    specific, we have found that similar properties are needed in a
    wide range of languages.

    Below, we indicate which lemmas depend on which other lemmas.
    Since [te] functions depend on their [tt] counterparts, a similar
    dependency can be found in the lemmas.

    The lemmas are split into three sections, one each for the [tt],
    [te], and [ee] functions.  The most important lemmas are the
    following:
      - Substitution and opening commute with each other, e.g.,
        [subst_tt_open_tt_var].
      - Opening a term is equivalent to opening the term with a fresh
        name and then substituting for that name, e.g.,
        [subst_tt_intro].

    We keep the sections as uniform in structure as possible.  In
    particular, we state explicitly strengthened induction hypotheses
    even when there are more concise ways of proving the lemmas of
    interest. *)


(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with eauto*.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j === n)... destruct (i === n)...
Qed.

(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto*.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  Case "typ_all".
    unfold open_tt in *.
    pick fresh X.
    apply (open_tt_rec_type_aux T2 0 (typ_fvar X))...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with auto*.
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    contradict H; fsetdec.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto*.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  Case "typ_bvar".
    destruct (k === n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto*.
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with auto*.
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with auto*.
  induction T2; intros U k Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (k === n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... contradict Fr; fsetdec.
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with auto*.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.

(* ********************************************************************** *)
(** ** Properties of type substitution in expressions *)

(** This section follows the structure of the previous section.  The
    one notable difference is that we require two auxiliary lemmas to
    show that substituting a type in a locally-closed expression is
    the identity. *)

Lemma open_te_rec_expr_aux : forall e j v i P ,
  open_ve_rec j v e = open_te_rec i P (open_ve_rec j v e) ->
  e = open_te_rec i P e.
Proof with eauto*.
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof with auto*.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type;
  try solve [
    unfold open_ve in *;
    pick fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (v := x);
    auto*
  | unfold open_te in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := typ_fvar X);
    auto*
    ].
Qed.

Lemma subst_te_fresh : forall X U e,
  X `notin` fv_te e ->
  e = subst_te X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_tt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

Lemma subst_te_open_te : forall e T X U,
  type U ->
  subst_te X U (open_te e T) = open_te (subst_te X U e) (subst_tt X U T).
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_te_open_te_rec...
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  type U ->
  open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with auto*.
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X `notin` fv_te e ->
  open_te_rec k U e = subst_te X U (open_te_rec k (typ_fvar X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec.
Qed.

Lemma subst_te_intro : forall X e U,
  X `notin` fv_te e ->
  open_te e U = subst_te X U (open_te e X).
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.

(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_vv_rec_expand : forall v x i,
  v = open_vv_rec i x v ->
  open_vv_rec i x v = open_vv_rec i x (open_vv_rec i x v).
Proof with auto*.
  intros v x i H.
  unfold open_vv_rec in *.
  destruct v...
  destruct (i === n)...
  destruct (i === n)...
Qed.

Lemma open_vv_rec_collapse : forall v j x y i,
  i <> j ->
  open_vv_rec j x v = open_vv_rec i y (open_vv_rec j x v) ->
  v = open_vv_rec i y v.
Proof with auto*.
  intros v j x y i Neq H.
  unfold open_vv_rec in *.
  destruct v...
  destruct (j === n).
  destruct (i === n)...
  assumption.
Qed.

Lemma open_ve_rec_expr_aux : forall e j x y i,
  i <> j ->
  open_ve_rec j y e = open_ve_rec i x (open_ve_rec j y e) ->
  e = open_ve_rec i x e.
Proof with eauto using open_vv_rec_collapse.
  intros e; induction e; intros j x y i Neq H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_ve_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ve_rec i u (open_te_rec j V e) ->
  e = open_ve_rec i u e.
Proof with eauto using open_vv_rec_expand.
  induction e; intros j V u i H; simpl; inversion H; f_equal...
Qed.

Lemma open_ve_rec_expr : forall x e k,
  expr e ->
  e = open_ve_rec k x e.
Proof with auto*.
  intros x e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; auto*;
    try solve [
      unfold open_ve in *;
      pick fresh y;
      eapply open_ve_rec_expr_aux with (j := 0) (y := y);
      auto*
    | unfold open_te in *;
      pick fresh Y;
      eapply open_ve_rec_type_aux with (j := 0) (V := typ_fvar Y);
      auto*
    ].
Qed.

Lemma subst_vv_fresh : forall (z : atom) (y : atom) (v : var),
  v <> z ->
  v = subst_vv z y v.
Proof with auto*.
  intros z y v H.
  unfold subst_vv.
  destruct v...
  destruct (a == z)...
Qed.

Lemma subst_ve_fresh : forall (x : atom) (y : atom) e,
  x `notin` fv_ve e ->
  e = subst_ve x y e.
Proof with eauto using subst_vv_fresh.
  intros x u e; induction e; simpl; intro H; f_equal; unfold subst_vv; auto*;
    match goal with
    | [|- ?v = _] =>
      destruct v as [| a];
      auto*;
      destruct (a == x);
      auto*;
      subst;
      simpl in H;
      fsetdec
    end.
Qed.

(*
Lemma subst_ve_open_ve_rec : forall e1 e2 x (u : atom) k,
  subst_ve x u (open_ve_rec k e2 e1) =
    open_ve_rec k (subst_vv x u e2) (subst_ve x u e1).
Proof with auto*.
  intros e1 e2 x u k WP. revert k.
  induction e1; intros k; simpl; f_equal...
  Case "exp_bvar".
    destruct (k === n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto*.
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.
*)

Lemma subst_ve_open_ve_var : forall (x y : atom) u e k,
  y <> x ->
  open_ve_rec k y (subst_ve x u e) = subst_ve x u (open_ve_rec k y e).
Proof with auto*.
  intros x y u e k Neq. revert k.
  induction e; intros k; simpl; f_equal; unfold subst_vv; auto*;
    match goal with
    | [|- open_vv_rec k y (match ?v with var_b _ => _ | var_f _ => _ end) = _] =>
      unfold open_vv_rec;
      destruct v as [n | a];
      [ destruct (k === n);
        [ destruct (y == x);
          [ contradict e0; assumption
          | auto
          ]
        | auto
        ]
      | destruct (a == x); auto
      ]
    end.
Qed.

Lemma subst_te_open_ve_rec : forall e x Z P k,
  subst_te Z P (open_ve_rec k x e) =
    open_ve_rec k x (subst_te Z P e).
Proof with auto*.
  induction e; intros x Z P k; simpl; f_equal...
Qed.

Lemma subst_te_open_ve : forall e x Z P,
  subst_te Z P (open_ve e x) = open_ve (subst_te Z P e) x.
Proof with auto*.
  intros.
  unfold open_ve.
  apply subst_te_open_ve_rec...
Qed.

Lemma subst_te_open_ve_var : forall Z (x : atom) P e,
  open_ve (subst_te Z P e) x = subst_te Z P (open_ve e x).
Proof with auto*.
  intros.
  rewrite subst_te_open_ve...
Qed.

Lemma subst_ve_open_te_rec : forall e P z u k,
  subst_ve z u (open_te_rec k P e) = open_te_rec k P (subst_ve z u e).
Proof with auto*.
  induction e; intros P z u k; simpl; f_equal...
Qed.

Lemma subst_ve_open_te : forall e P z u,
  subst_ve z u (open_te e P) = open_te (subst_ve z u e) P.
Proof with auto*.
  intros.
  unfold open_te.
  apply subst_ve_open_te_rec...
Qed.

Lemma subst_ve_open_te_var : forall z (X : atom) u e,
  open_te (subst_ve z u e) X = subst_ve z u (open_te e X).
Proof with auto*.
  intros z X u e.
  rewrite subst_ve_open_te...
Qed.

Lemma subst_ve_intro_rec : forall x e y k,
  x `notin` fv_ve e ->
  open_ve_rec k y e = subst_ve x y (open_ve_rec k x e).
Proof with auto*.
  induction e; intros u k Fr; simpl in *; f_equal...
  all: match goal with
  | [|- open_vv_rec ?k ?u ?v = _] => destruct v; unfold open_vv_rec, subst_vv;
      [ destruct (k === n);
        [ destruct (x == x); [ auto | contradict n0; reflexivity ]
        | auto ]
      | destruct (a == x); [ contradict e; simpl in Fr; fsetdec | auto ]
      ]
  end.
Qed.

Lemma subst_ve_intro : forall x e y,
  x `notin` fv_ve e ->
  open_ve e y = subst_ve x y (open_ve e x).
Proof with auto*.
  intros.
  unfold open_ve.
  apply subst_ve_intro_rec...
Qed.

(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)

(** The following lemma depends on [subst_tt_open_tt_var]. *)

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "type_fvar".
    destruct (X == Z)...
  Case "type_all".
    pick fresh Y and apply type_all...
    rewrite subst_tt_open_tt_var...
Qed.

(** The following lemma depends on [subst_tt_type] and
    [subst_te_open_ee_var]. *)

Lemma subst_te_expr : forall Z P e,
  expr e ->
  type P ->
  expr (subst_te Z P e).
Proof with eauto using subst_tt_type.
  intros Z P e He Hp.
  induction He; simpl; auto using subst_tt_type;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_te_open_ve_var;
    try rewrite subst_te_open_te_var;
    eauto using subst_tt_type
  ].
Qed.

Lemma if_hoist {A B : Type} {C1 C2 : Prop} : forall (c : {C1} + {C2}) (a b : A) (f : A -> B),
  (if c then f a else f b) = f (if c then a else b).
Proof.
  intros c a b f.
  destruct c; reflexivity.
Qed.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. *)

Lemma subst_ve_expr : forall (z : atom) (y : atom) e,
  expr e ->
  expr (subst_ve z y e).
Proof with auto.
  intros z y e He.
  induction He; simpl; auto;
  try solve [
    econstructor;
    try (instantiate (1 := L `union` singleton z) || instantiate (1 := T));
    intros;
    try rewrite subst_ve_open_ve_var;
    try rewrite subst_ve_open_te_var;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
  Case "expr_abs".
    apply expr_abs with (L := L `union` singleton z)...
    intros x x_fresh.
    unfold open_ve.
    rewrite subst_ve_open_ve_var...
    apply H1...
  Case "expr_app".
    rewrite (if_hoist (x == z) y x var_f).
    rewrite (if_hoist (y0 == z) y y0 var_f).
    apply expr_app.
  Case "expr_tapp".
    rewrite (if_hoist (x == z) y x var_f).
    apply expr_tapp...
  Case "expr_let".
    apply expr_let with (L := L `union` singleton z)...
    intros x x_fresh.
    unfold open_ve.
    rewrite subst_ve_open_ve_var...
    apply H0...
  Case "expr_pair".
    rewrite (if_hoist (x == z) y x var_f).
    rewrite (if_hoist (y0 == z) y y0 var_f).
    apply expr_pair.
  Case "expr_fst".
    rewrite (if_hoist (x == z) y x var_f).
    apply expr_fst.
  Case "expr_snd".
    rewrite (if_hoist (x == z) y x var_f).
    apply expr_snd.
Qed.

Lemma eq_var_dec : forall v1 v2 : var,
  {v1 = v2} + {v1 <> v2}.
Proof.
  intros [i | a] [j | b]; try (right; discriminate).
  - Case "bound / bound".
    destruct (eq_nat_dec i j).
    + left; f_equal; apply e.
    + right; contradict n; inversion n; reflexivity.
  - Case "free / free".
    destruct (eq_atom_dec a b).
    + left; f_equal; apply e.
    + right; contradict n; inversion n; reflexivity.
Qed.

Lemma eq_typ_dec : forall t1 t2 : typ,
  {t1 = t2} + {t1 <> t2}.
Proof.
  intros t1.
  induction t1; intros t2; destruct t2; try (right; discriminate).
  - Case "typ_top".
    left; reflexivity.
  - Case "typ_bvar".
    destruct (eq_nat_dec n n0).
    + left; f_equal; apply e.
    + right; contradict n1; f_equal; inversion n1; reflexivity.
  - Case "typ_fvar".
    destruct (eq_atom_dec a a0).
    + left; f_equal; apply e.
    + right; contradict n; f_equal; inversion n; reflexivity.
  - Case "typ_arrow".
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "typ_all".
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "typ_prod".
    destruct (IHt1_1 t2_1), (IHt1_2 t2_2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
Qed.

Lemma eq_exp_dec : forall e1 e2 : exp,
  {e1 = e2} + {e1 <> e2}.
Proof.
  intros e1.
  induction e1; intros e2; destruct e2; try (right; discriminate).
  - Case "exp_var".
    destruct (eq_var_dec v v0).
    + left; f_equal; apply e.
    + right; contradict n; f_equal; inversion n; reflexivity.
  - Case "exp_abs".
    destruct (eq_typ_dec t t0), (IHe1 e2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "exp_app".
    destruct (eq_var_dec v v1), (eq_var_dec v0 v2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "exp_tabs".
    destruct (eq_typ_dec t t0), (IHe1 e2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "exp_tapp".
    destruct (eq_typ_dec t t0), (eq_var_dec v v0); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "exp_let".
    destruct (IHe1_1 e2_1), (IHe1_2 e2_2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "exp_pair".
    destruct (eq_var_dec v v1), (eq_var_dec v0 v2); subst; try (right; contradict n; inversion n; reflexivity).
    left; reflexivity.
  - Case "exp_fst".
    destruct (eq_var_dec v v0).
    + left; f_equal; apply e.
    + right; contradict n; f_equal; inversion n; reflexivity.
  - Case "exp_snd".
    destruct (eq_var_dec v v0).
    + left; f_equal; apply e.
    + right; contradict n; f_equal; inversion n; reflexivity.
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

#[global]
Hint Resolve subst_tt_type subst_te_expr subst_ve_expr : core.

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the [Environment] library. *)

#[global]
Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)) : core.
