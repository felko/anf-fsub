(** Administrative lemmas for Fsub.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    This file contains a number of administrative lemmas that we
    require for proving type-safety.  The lemmas mainly concern the
    relations [wf_typ] and [wf_env].

    This file also contains regularity lemmas, which show that various
    relations hold only for locally closed terms.  In addition to
    being necessary to complete the proof of type-safety, these lemmas
    help demonstrate that our definitions are correct; they would be
    worth proving even if they are unneeded for any "real" proofs.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export ANF_Infrastructure.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof.
  intros E T H; induction H; eauto.
Qed.

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  ok (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  eremember (G ++ E) as D.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  ok (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_narrowing : forall V U T E F X,
  wf_typ (F ++ [(X, bind_sub V)] ++ E) T ->
  ok (F ++ [(X, bind_sub U)] ++ E) ->
  wf_typ (F ++ [(X, bind_sub U)] ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F X Hwf_typ Hok.
  eremember (F ++ [(X, bind_sub V)] ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Hok Heq; subst...
  Case "wf_typ_var".
    binds_cases H...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma wf_typ_specializing : forall V U T E F x,
  wf_typ (F ++ [(x, bind_typ V)] ++ E) T ->
  ok (F ++ [(x, bind_typ U)] ++ E) ->
  wf_typ (F ++ [(x, bind_typ U)] ++ E) T.
Proof with simpl_env; eauto.
  intros V U T E F x Hwf_typ Hok.
  eremember (F ++ [(x, bind_typ V)] ++ E) as G.
  generalize dependent F.
  induction Hwf_typ; intros F Hok Heq; subst...
  Case "wf_typ_var".
    binds_cases H...
  Case "typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma wf_typ_strengthening : forall E F x U T,
  wf_typ (F ++ [(x, bind_typ U)] ++ E) T ->
  wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  eremember (F ++ [(x, bind_typ U)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    binds_cases H...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H1...
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T,
  wf_typ (F ++ [(Z, bind_sub Q)] ++ E) T ->
  wf_typ E P ->
  ok (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt Z P T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T WT WP.
  eremember (F ++ [(Z, bind_sub Q)] ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z); subst...
    SCase "X <> Z".
      binds_cases H...
      apply (wf_typ_var (subst_tt Z P U))...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub T1)] ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_typ_open : forall E U T1 T2,
  ok E ->
  wf_typ E (typ_all T1 T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  intros E U T1 T2 Ok WA WU.
  inversion WA; subst.
  pick fresh X.
  rewrite (subst_tt_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  eapply wf_typ_subst_tb...
Qed.

(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma ok_from_wf_env : forall E,
  wf_env E ->
  ok E.
Proof.
  intros E H; induction H; auto.
Qed.

(** We add [ok_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [ok_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

#[global]
Hint Resolve ok_from_wf_env : core.

Lemma notin_open_tt_rec : forall K Y Z T,
  Y `notin` (fv_tt T `union` singleton Z) ->
  Y `notin` fv_tt (open_tt_rec K Z T).
Proof with eauto*.
  intros K Y Z T Y_notin_T_Z.
  generalize dependent K.
  induction T; intros K; simpl in *;
  repeat match goal with
  | V : var |- _ =>
      destruct V; simpl in *; eauto*;
      destruct (K === n); eauto*
  | |- Y `notin` (_ `union` _) => apply notin_union
  | IH : Y `notin` _ -> forall K, _ |- _ => apply IH; eauto*
  | _ => eauto*
  end.
  destruct (K === n); eauto*.
Qed.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; binds_cases J...
  inversion H4; subst...
Qed.

Lemma wf_typ_from_binds_sub : forall x U E,
  wf_env E ->
  binds x (bind_sub U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; binds_cases J...
  inversion H4; subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_typ T)] ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma wf_typ_from_wf_env_sub : forall x T E,
  wf_env ([(x, bind_sub T)] ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_narrowing : forall V E F U X,
  wf_env (F ++ [(X, bind_sub V)] ++ E) ->
  wf_typ E U ->
  wf_env (F ++ [(X, bind_sub U)] ++ E).
Proof with eauto 6 using wf_typ_narrowing.
  induction F; intros U X Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_specializing : forall V E F U x,
  wf_env (F ++ [(x, bind_typ V)] ++ E) ->
  wf_typ E U ->
  wf_env (F ++ [(x, bind_typ U)] ++ E).
Proof with eauto 6 using wf_typ_specializing.
  induction F; intros U x Wf_env Wf;
    inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ [(x, bind_typ T)] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening_concat : forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof with eauto.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_subst_tb : forall Q Z P E F,
  wf_env (F ++ [(Z, bind_sub Q)] ++ E) ->
  wf_typ E P ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
Qed.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
  intros Y X T. unfold open_tt.
  generalize 0.
  induction T; simpl; intros k Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom E))...
    eapply binds_In; eauto.
  Case "wf_typ_all".
    apply notin_union...
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)

Lemma sub_regular : forall E S T,
  sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E S T H.
  induction H...
  Case "sub_trans_tvar".
    eauto*.
  Case "sub_all".
    repeat split...
    SCase "Second of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
      rewrite_env (empty ++ [(Y, bind_sub S1)] ++ E).
      apply (wf_typ_narrowing T1)...
    SCase "Third of original three conjuncts".
      pick fresh Y and apply wf_typ_all...
      destruct (H1 Y)...
Qed.

Lemma typing_regular : forall E e T,
  typing E e T ->
  wf_env E /\ expr e /\ wf_typ E T.
Proof with simpl_env; auto*.
  intros E e T H.
  induction H...
  - Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  - Case "typing_abs".
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. inversion Hok...
    + pick fresh x and apply expr_abs.
      * eauto using type_from_wf_typ, wf_typ_from_wf_env_typ.
      * destruct (H0 x)...
    + apply wf_typ_arrow; eauto using wf_typ_from_wf_env_typ.
      rewrite_env (empty ++ E).
      eapply wf_typ_strengthening; simpl_env; eauto.
  - Case "typing_app".
    repeat split...
    destruct IHtyping1 as [_ [_ K]].
    inversion K...
  - Case "typing_tabs".
    pick fresh Y.
    destruct (H0 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    + pick fresh X and apply expr_tabs.
      * eauto using type_from_wf_typ, wf_typ_from_wf_env_sub...
      * destruct (H0 X)...
    + pick fresh Z and apply wf_typ_all...
      destruct (H0 Z)...
  - Case "typing_tapp".
    destruct (sub_regular _ _ _ H0) as [R1 [R2 R3]].
    repeat split...
    + apply expr_tapp...
      eauto using type_from_wf_typ.
    + destruct IHtyping as [R1' [R2' R3']].
      eapply wf_typ_open; eauto.
  - Case "typing_let".
    repeat split...
    + pick fresh x.
      apply expr_let with (L := L)...
      apply H1.
    + pick fresh x.
      destruct (H1 x) as [wf_xE [expr_open_c_x wf_T2]]...
      rewrite_env (empty ++ E).
      apply wf_typ_strengthening with (x := x) (U := T1)...
  - Case "typing_fst".
    repeat split...
    inversion H; subst.
    + SCase "bind_typ".
      assert (wf_prod : wf_typ E (typ_prod T1 T2)) by eauto using wf_typ_from_binds_typ.
      inversion wf_prod...
    + SCase "bind_sub".
      destruct (sub_regular _ _ _ H1) as [_ [_ wf_prod]].
      inversion wf_prod...
  - Case "typing_snd".
    repeat split...
    inversion H; subst.
    + SCase "bind_typ".
      assert (wf_prod : wf_typ E (typ_prod T1 T2)) by eauto using wf_typ_from_binds_typ.
      inversion wf_prod...
    + SCase "bind_sub".
      destruct (sub_regular _ _ _ H1) as [_ [_ wf_prod]].
      inversion wf_prod...
  - Case "typing_sub".
    repeat split...
    destruct (sub_regular E S T)...
Qed.

Lemma store_typing_regular : forall S Γ,
  store_typing S Γ ->
  wf_env Γ.
Proof with eauto*.
  intros S Γ Typ.
  induction Typ...
  apply wf_env_typ...
  apply (typing_regular Γ v T H).
Qed.

Lemma stores_implies_binds : forall S Γ y v v_value,
  store_typing S Γ ->
  stores S y v v_value ->
  exists T, binds y (bind_typ T) Γ.
Proof with eauto*.
  intros S Γ y v v_value typ.
  assert (wf_Γ : wf_env Γ) by apply (store_typing_regular _ _ typ).
  induction typ; intros store.
  - inversion store.
  - destruct (x == y); subst...
    inversion store.
    destruct (y == x); try (exfalso; apply (n (eq_sym e))).
    inversion wf_Γ; subst...
    destruct (IHtyp H5 H2)...
Qed.

Lemma binds_implies_store : forall S Γ T x,
  store_typing S Γ ->
  binds x (bind_typ T) Γ ->
  exists v v_value, stores S x v v_value.
Proof with eauto*.
  intros *.
  intros store_typ binds.
  induction store_typ; inversion binds; subst.
  destruct (x == x0).
  - inversion H2; subst...
    unfold stores.
    unfold Environment.binds.
    simpl.
    destruct (x0 == x0); try (contradict n; reflexivity).
    eauto.
  - destruct IHstore_typ...
    destruct H1 as [x1_value S_stores_x].
    exists x1, x1_value.
    rewrite_env ([let' x0 v v_value] ++ S).
    apply binds_tail.
    + trivial.
    + simpl; fsetdec.
Qed.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof with eauto*.
  intros e H. induction H...
Qed.

Lemma eval_typing_regular : forall Γ E T U,
  eval_typing Γ E T U ->
  wf_env Γ /\ wf_typ Γ T /\ wf_typ Γ U.
Proof with eauto*.
  intros Γ E T U eval_typ.
  induction eval_typ; repeat split...
  - apply (sub_regular _ _ _ H0).
  - apply (sub_regular _ _ _ H0).
  - pick fresh x.
    specialize (H x ltac:(fsetdec)).
    destruct (typing_regular _ _ _ H) as [wf_xTΓ _].
    inversion wf_xTΓ; subst...
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [ok_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [ok] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)
    
#[global]
Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: sub _ _ _ |- _ => apply (proj1 (sub_regular _ _ _ H))
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end : core.

#[global]
Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  | H: sub E T _ |- _ => apply (proj1 (proj2 (sub_regular _ _ _ H)))
  | H: sub E _ T |- _ => apply (proj2 (proj2 (sub_regular _ _ _ H)))
  end : core.

#[global]
Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  | H: sub ?E T _ |- _ => go E
  | H: sub ?E _ T |- _ => go E
  end : core.
(*
#[global]
Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end : core.
*)