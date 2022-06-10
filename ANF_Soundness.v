(** Type-safety proofs for Fsub.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Export ANF_Lemmas.

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Program.Equality.

(* ********************************************************************** *)
(** * #<a name="subtyping"></a># Properties of subtyping *)

(* ********************************************************************** *)
(** ** Reflexivity (1) *)

Lemma sub_reflexivity : forall E T,
  wf_env E ->
  wf_typ E T ->
  sub E T T.
Proof with eauto.
  intros E T Ok Wf.
  induction Wf; try constructor...
  pick fresh Y and apply sub_all...
Qed.

(* ********************************************************************** *)
(** ** Weakening (2) *)

Lemma sub_weakening : forall E F G S T,
  sub (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  sub (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening.
  intros E F G S T Sub Ok.
  eremember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U)...
  Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
  Case "sub_prod".
    apply sub_prod...
Qed.

(* ********************************************************************** *)
(** ** Narrowing and transitivity (3) *)

Definition transitivity_on Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Lemma sub_narrowing_aux : forall Q F E Z P S T,
  transitivity_on Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof with simpl_env; eauto using wf_typ_narrowing, wf_env_narrowing.
  intros Q F E Z P S T TransQ SsubT PsubQ.
  eremember (F ++ [(Z, bind_sub Q)] ++ E) as G. generalize dependent F.
  induction SsubT; intros F EQ; subst...
  - Case "sub_top".
    apply sub_top...
  - Case "sub_refl_tvar".
    apply sub_refl_tvar...
  - Case "sub_trans_tvar".
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_trans_tvar P)...
      apply TransQ.
      * SSCase "P <: Q".
        rewrite_env (empty ++ (F ++ [(Z, bind_sub P)]) ++ E).
        apply sub_weakening...
      * SSCase "Q <: T".
        binds_get H.
        inversion H1; subst...
    + SCase "X <> Z".
      apply (sub_trans_tvar U)... 
  - Case "sub_all".
    pick fresh Y and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
  - Case "sub_prod".
    apply sub_prod... 
Qed.

Lemma sub_transitivity : forall Q,
  transitivity_on Q.
Proof with simpl_env; auto.
  unfold transitivity_on.
  intros Q E S T SsubQ QsubT.
  assert (W : type Q) by auto.
  generalize dependent T.
  generalize dependent S.
  generalize dependent E.
  remember Q as Q' in |-.
  generalize dependent Q'.
  induction W;
    intros Q' EQ E S SsubQ;
    induction SsubQ; try discriminate; inversion EQ; subst;
    intros T' QsubT;
    inversion QsubT; subst. (* try eauto 4 using sub_trans_tvar. *)
  1-14: eauto 4 using sub_trans_tvar.
  - Case "sub_all / sub_top".
    assert (sub E (typ_all S1 S2) (typ_all T1 T2)).
    { pick fresh y and apply sub_all... }
    auto.
  - Case "sub_all / sub_all".
    pick fresh Y and apply sub_all.
    + SCase "bounds".
      eauto.
    + SCase "bodies".
      lapply (H0 Y); [ intros K | auto ].
      apply (K (open_tt T2 Y))...
      rewrite_env (empty ++ [(Y, bind_sub T0)] ++ E).
      apply (sub_narrowing_aux T1)...
      unfold transitivity_on.
      auto using (IHW T1).
  - Case "sub_prod / sub_top".
    apply sub_top...
    eapply wf_typ_var, H.
  - Case "sub_prod / sub_prod".
    apply sub_trans_tvar with (U := U)...
  - Case "sum_top / sub_prod".
    apply sub_top...
  - Case "sub_prod / sub_prod".
    apply sub_prod.
    apply IHW1 with (Q' := T1)...
    apply IHW2 with (Q' := T2)...
Qed.

Lemma sub_narrowing : forall Q E F Z P S T,
  sub E P Q ->
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub (F ++ [(Z, bind_sub P)] ++ E) S T.
Proof.
  intros.
  eapply sub_narrowing_aux; eauto.
  apply sub_transitivity.
Qed.

(* ********************************************************************** *)
(** ** Type substitution preserves subtyping (10) *)

Lemma sub_through_subst_tt : forall Q E F Z S T P,
  sub (F ++ [(Z, bind_sub Q)] ++ E) S T ->
  sub E P Q ->
  sub (map (subst_tb Z P) F ++ E) (subst_tt Z P S) (subst_tt Z P T).
Proof with
      simpl_env;
      eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
  intros Q E F Z S T P SsubT PsubQ.
  eremember (F ++ [(Z, bind_sub Q)] ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  - Case "sub_top".
    apply sub_top...
  - Case "sub_refl_tvar".
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply sub_reflexivity...
    + SCase "X <> Z".
      apply sub_reflexivity...
      inversion H0; subst.
      binds_cases H3...
      apply (wf_typ_var (subst_tt Z P U))...
  - Case "sub_trans_tvar".
    destruct (X == Z); subst.
    + SCase "X = Z".
      apply (sub_transitivity Q).
      * SSCase "left branch".
        rewrite_env (empty ++ map (subst_tb Z P) G ++ E).
        apply sub_weakening...
      * SSCase "right branch".
        rewrite (subst_tt_fresh Z P Q).
        -- binds_get H.
           inversion H1; subst...
        -- apply (notin_fv_wf E).
           ++ auto.
           ++ destruct (sub_regular (G ++ [(Z, bind_sub Q)] ++ E) U T SsubT) as [wf_G_Z_E _].
              apply ok_from_wf_env in wf_G_Z_E as ok_G_Z_E.
              apply fresh_mid_tail with (F := G) (a := bind_sub Q), ok_G_Z_E.
    + SCase "X <> Z".
      apply (sub_trans_tvar (subst_tt Z P U))...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H...
  - Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite subst_tt_open_tt_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(X, bind_sub T1)] ++ G) ++ E).
    apply H0...
  - Case "sub_prod".
    apply sub_prod...
Qed.

(* ********************************************************************** *)
(** * #<a name="typing"></a># Properties of typing *)

(* ********************************************************************** *)
(** ** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
  typing (G ++ E) e T ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ,
                       wf_typ_from_wf_env_sub,
                       sub_weakening.
  intros E F G e T Typ.
  eremember (G ++ E) as H.
  generalize dependent G.
  induction Typ; intros G EQ Ok; subst...
  Case "typing_abs".
    pick fresh x and apply typing_abs.
    lapply (H x); [intros K | auto].
    rewrite <- concat_assoc.
    apply (H0 x)...
  Case "typing_tabs".
    pick fresh X and apply typing_tabs.
    lapply (H X); [intros K | auto].
    rewrite <- concat_assoc.
    apply (H0 X)...
  Case "typing_let".
    eapply typing_let with (T1 := T1) (L := L `union` dom (G ++ F ++ E)).
    apply IHTyp...
    intros x x_fresh.
    rewrite_env (([(x, bind_typ T1)] ++ G) ++ F ++ E).
    apply H0...
  Case "typing_pair".
    apply typing_pair...
  Case "typing_fst".
    eapply typing_fst...
  Case "typing_snd".
    eapply typing_snd...
Qed.

Lemma eval_typing_weakening : forall E F G E' T U,
  eval_typing (G ++ E) E' T U ->
  wf_env (G ++ F ++ E) ->
  eval_typing (G ++ F ++ E) E' T U.
Proof with eauto*.
  intros E F G  E' T U Typ.
  induction Typ; intros wf.
  - Case "typing_eval_nil".
    apply typing_eval_nil...
    apply sub_weakening...
  - Case "typing_eval_cons".
    apply typing_eval_cons with (L := L `union` dom (G ++ F ++ E)) (U := U)...
    intros x x_fresh.
    assert (c_typing : typing (([(x, bind_typ T)] ++ G) ++ E) (open_ve c x) U) by (apply (H x); eauto).
    eapply typing_weakening with (F := F) in c_typing.
    * SSCase "typing".
      apply c_typing.
    * SSCase "well formedness".
      simpl_env.
      apply wf_env_typ...
      assert (wf_env_xTGE : wf_env (([(x, bind_typ T)] ++ G) ++ E)).
      { eapply typing_regular, c_typing. }
      assert (wf_typ_xTGE_T : wf_typ (([(x, bind_typ T)] ++ G) ++ E) T).
      { apply (wf_typ_from_wf_env_typ x) in wf_env_xTGE.
        simpl_env.
        apply wf_typ_weaken_head... }
      simpl_env in *.
      apply wf_typ_weakening with (F := F)...
      apply (wf_typ_from_wf_env_typ x)...
Qed.

(* ********************************************************************** *)
(** ** Strengthening (6) *)

Lemma sub_strengthening : forall x U E F S T,
  sub (F ++ [(x, bind_typ U)] ++ E) S T ->
  sub (F ++ E) S T.
Proof with eauto using wf_typ_strengthening, wf_env_strengthening.
  intros x U E F S T SsubT.
  eremember (F ++ [(x, bind_typ U)] ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "sub_trans_tvar".
    apply (sub_trans_tvar U0)...
    binds_cases H...
  Case "sub_all".
    pick fresh X and apply sub_all...
    rewrite <- concat_assoc.
    apply H0...
  Case "sub_prod".
    apply sub_prod...
Qed.

Lemma wf_typ_tvar_comes_from_binds : forall Γ (X : atom),
  wf_env Γ ->
  wf_typ Γ X ->
  exists S, binds X (bind_sub S) Γ /\ wf_typ Γ S.
Proof with eauto using wf_typ_from_binds_sub.
  intros Γ X wf_Γ wf_X.
  eremember (X : typ) as T.
  induction wf_X; inversion HeqT; subst...
Qed.

Lemma notin_open_ve_rec : forall k y z e,
  y `notin` (fv_ve e `union` singleton z) ->
  y `notin` fv_ve (open_ve_rec k z e).
Proof with eauto*.
  intros k y z e y_notin_e_z.
  generalize dependent k.
  induction e; intros k; simpl in *;
  repeat match goal with
  | v : var |- _ =>
      destruct v; simpl in *; eauto*;
      destruct (k === n); eauto*
  | |- y `notin` (_ `union` _) => apply notin_union
  | IH : y `notin` _ -> forall k, _ |- _ => apply IH; eauto*
  end.
Qed.

Lemma open_te_preserves_fv_ve : forall k e X,
  fv_ve (open_te_rec k X e) = fv_ve e.
Proof with eauto*.
  intros k e X.
  generalize dependent k.
  induction e; simpl...
Qed.

Lemma typing_strengthening : forall Γ x S Δ e T,
  typing (Γ ++ [(x, bind_typ S)] ++ Δ) e T ->
  x `notin` fv_ve e ->
  typing (Γ ++ Δ) e T.
Proof with eauto using wf_typ_strengthening, wf_env_strengthening.
  intros Γ x S Δ e T typ x_notin_fv_e.
  eremember (Γ ++ [(x, bind_typ S)] ++ Δ) as Γ'.
  assert (e_expr : expr e) by apply (typing_regular _ _ _ typ).
  generalize dependent Γ.
  generalize dependent x.
  induction typ; intros y y_notin_fv_e Γ EQ.
  - Case "typing_var".
    inversion e_expr; subst...
    binds_cases H0...
    contradict y_notin_fv_e.
    apply AtomSetNotin.in_singleton.
  - Case "typing_abs".
    inversion e_expr; subst...
    pick fresh z and apply typing_abs.
    rewrite_env (([(z, bind_typ V)] ++ Γ) ++ Δ).
    apply (H0 z ltac:(fsetdec) (H4 z ltac:(fsetdec)) y).
    + apply notin_open_ve_rec.
      apply notin_union.
      * fsetdec.
      * assert (z_notin_y : z `notin` singleton y) by fsetdec.
        assert (z_neq_y : z <> y) by apply AtomSetNotin.elim_notin_singleton, z_notin_y.
        apply notin_singleton.
        contradict z_neq_y.
        symmetry.
        apply z_neq_y.
    + rewrite concat_assoc.
      reflexivity.
  - Case "typing_app".
    simpl in y_notin_fv_e.
    apply typing_app with (T1 := T1).
    + apply IHtyp1 with (x := y)...
    + apply IHtyp2 with (x0 := y)...
  - Case "typing_tabs".
    inversion e_expr; subst...
    pick fresh Z and apply typing_tabs.
    rewrite_env (([(Z, bind_sub V)] ++ Γ) ++ Δ).
    apply (H0 Z ltac:(fsetdec) (H4 Z ltac:(fsetdec)) y).
    + unfold open_te.
      rewrite open_te_preserves_fv_ve.
      fsetdec.
    + rewrite concat_assoc.
      reflexivity.
  - Case "typing_tapp".
    inversion e_expr; subst...
    simpl in y_notin_fv_e.
    apply typing_tapp with (T1 := T1).
    + apply IHtyp with (x0 := y)...
    + apply sub_strengthening in H...
  - Case "typing_let".
    inversion e_expr; subst...
    simpl in y_notin_fv_e.
    pick fresh z and apply typing_let.
    + SCase "val".
      eapply IHtyp with (x := y)...
    + SCase "cont".
      rewrite_env (([(z, bind_typ T1)] ++ Γ) ++ Δ).
      apply (H0 z ltac:(fsetdec) (H4 z ltac:(fsetdec)) y).
      * apply notin_open_ve_rec.
        apply notin_union.
        -- fsetdec.
        -- assert (z_notin_y : z `notin` singleton y) by fsetdec.
           assert (z_neq_y : z <> y) by apply AtomSetNotin.elim_notin_singleton, z_notin_y.
           apply notin_singleton.
           contradict z_neq_y.
           symmetry.
           apply z_neq_y.
      * rewrite concat_assoc.
        reflexivity.
  - Case "typing_pair".
    simpl in y_notin_fv_e.
    apply typing_pair.
    + apply IHtyp1 with (x := y)...
    + apply IHtyp2 with (x := y)...
  - Case "typing_fst".
    simpl in y_notin_fv_e.
    apply typing_fst with (T2 := T2).
    apply IHtyp with (x0 := y)...
  - Case "typing_snd".
    simpl in y_notin_fv_e.
    apply typing_snd with (T1 := T1).
    apply IHtyp with (x0 := y)...
  - Case "typing_sub".
    apply typing_sub with (S := S0); subst.
    + apply IHtyp with (x := y)...
    + apply sub_strengthening in H.
      apply H.
Qed.

Lemma typing_strengthening_sub_head : forall X S Γ e T,
  typing ([(X, bind_sub S)] ++ Γ) e T ->
  X `notin` fv_te e ->
  typing Γ e T.
Abort.

(************************************************************************ *)
(** ** Narrowing for typing (7) *)

Lemma typing_narrowing : forall Q E F X P e T,
  sub E P Q ->
  typing (F ++ [(X, bind_sub Q)] ++ E) e T ->
  typing (F ++ [(X, bind_sub P)] ++ E) e T.
Proof with eauto 6 using wf_env_narrowing, wf_typ_narrowing, sub_narrowing.
  intros Q E F X P e T PsubQ Typ.
  eremember (F ++ [(X, bind_sub Q)] ++ E) as E'.
  generalize dependent F.
  induction Typ; intros F EQ; subst...
  Case "typing_var".
    binds_cases H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite <- concat_assoc.
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite <- concat_assoc.
    apply H0...
  Case "typing_let".
    pick fresh y and apply typing_let...
    rewrite <- concat_assoc.
    apply H0...
  Case "typing_pair".
    apply typing_pair...
  Case "typing_fst".
    eapply typing_fst...
  Case "typing_snd".
    eapply typing_snd...
Qed.

Lemma sub_specializing : forall Q E F z P S T,
  sub E P Q ->
  sub (F ++ [(z, bind_typ Q)] ++ E) S T ->
  sub (F ++ [(z, bind_typ P)] ++ E) S T.
Proof with eauto using sub_weakening, sub_strengthening.
  intros Q E F z P S T PsubQ SsubT.
  apply sub_weakening.
  apply sub_strengthening in SsubT.
  eauto.
  destruct (sub_regular _ _ _ SsubT) as [wf_E _].
  eapply wf_env_specializing with (V := Q)...
Qed.

Lemma typing_specializing : forall Q F E z P e T,
  sub E P Q ->
  typing (F ++ [(z, bind_typ Q)] ++ E) e T ->
  typing (F ++ [(z, bind_typ P)] ++ E) e T.
Proof with simpl_env; eauto using wf_typ_specializing, wf_env_specializing.
  intros Q F E z P e T PsubQ e_T.
  eremember (F ++ [(z, bind_typ Q)] ++ E) as G. generalize dependent F.
  induction e_T; intros F EQ; subst...
  - Case "typing_var".
    binds_cases H0.
    + apply typing_var.
      * eauto using wf_env_specializing.
      * apply binds_weaken_at_head.
        apply binds_weaken_at_head.
        eauto.
        apply ok_from_wf_env, wf_env_strengthening_concat with (F := F)...
        apply ok_from_wf_env...
    + inversion H1; subst.
      apply typing_sub with (S := P)...
      rewrite_env (empty ++ (F ++ [(x, bind_typ P)]) ++ E).
      apply sub_weakening...
    + apply typing_var...
  - Case "typing_abs".
    pick fresh x and apply typing_abs.
    rewrite_env (([(x, bind_typ V)] ++ F) ++ [(z, bind_typ P)] ++ E).
    apply H0...
  - Case "typing_tabs".
    pick fresh X and apply typing_tabs.
    rewrite_env (([(X, bind_sub V)] ++ F) ++ [(z, bind_typ P)] ++ E).
    apply H0...
  - Case "typing_tapp".
    apply typing_tapp with (T1 := T1).
    apply IHe_T...
    apply sub_specializing with (Q := Q)...
  - Case "typing_let".
    pick fresh x and apply typing_let...
    rewrite_env (([(x, bind_typ T1)] ++ F) ++ [(z, bind_typ P)] ++ E).
    apply H0...
  - Case "typing_pair".
    apply typing_pair...
  - Case "typing_fst".
    apply typing_fst with (T2 := T2)...
  - Case "typing_snd".
    apply typing_snd with (T1 := T1)...
  - Case "typing_sub".
    apply typing_sub with (S := S)...
    apply sub_specializing with (Q := Q)...
Qed.


Lemma eval_specializing : forall Γ E T U T',
  sub Γ T' T ->
  eval_typing Γ E T U ->
  eval_typing Γ E T' U.
Proof with eauto*.
  intros *.
  intros subT eval_typ.
  generalize dependent T'.
  induction eval_typ; intros T' subT.
  - apply typing_eval_nil...
    apply sub_transitivity with (Q := T)...
  - eapply typing_eval_cons with (L := L) (U := U)...
    intros x x_fresh.
    rewrite_env (empty ++ [(x, bind_typ T')] ++ Γ).
    eapply typing_specializing...
Qed.

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma typing_through_subst_ve : forall U E F x T e u,
  typing (F ++ [(x, bind_typ U)] ++ E) e T ->
  binds u (bind_typ U) E ->
  typing (F ++ E) (subst_ve x u e) T.
(* begin show *)

(** We provide detailed comments for the following proof, mainly to
    point out several useful tactics and proof techniques.

    Starting a proof with "Proof with <some tactic>" allows us to
    specify a default tactic that should be used to solve goals.  To
    invoke this default tactic at the end of a proof step, we signal
    the end of the step with three periods instead of a single one,
    e.g., "apply typing_weakening...". *)

Proof with simpl_env;
           eauto 4 using wf_typ_strengthening,
                         wf_env_strengthening,
                         sub_strengthening.

  (** The proof proceeds by induction on the given typing derivation
      for e.  We use the remember tactic, along with generalize
      dependent, to ensure that the goal is properly strengthened
      before we use induction. *)

  intros U E F x T e u TypT TypU.
  eremember (F ++ [(x, bind_typ U)] ++ E) as E'.
  generalize dependent F.
  induction TypT; intros F EQ; subst; simpl subst_ve...

  (** The typing_var case involves a case analysis on whether the
      variable is the same as the one being substituted for. *)

  Case "typing_var".
    destruct (x0 == x); subst.

    (** In the case where x0=x, we first observe that hypothesis H0
        implies that T=U, since x can only be bound once in the
        environment.  The conclusion then follows from hypothesis TypU
        and weakening.  We can use the binds_get tactic, described in
        the Environment library, with H0 to obtain the fact that
        T=U. *)

    SCase "x0 = x".
      binds_get H0.
        inversion H2; subst.

        (** In order to apply typing_weakening, we need to rewrite the
            environment so that it has the right shape.  (We could
            also prove a corollary of typing_weakening.)  The
            rewrite_env tactic, described in the Environment library,
            is one way to perform this rewriting. *)

        rewrite_env (empty ++ F ++ E).
        apply typing_weakening...
        apply typing_var...
        apply wf_env_strengthening in H.
        apply wf_env_strengthening_concat in H.
        apply H.
        

    (** In the case where x0<>x, the result follows by an exhaustive
        case analysis on exactly where x0 is bound in the environment.
        We perform this case analysis by using the binds_cases tactic,
        described in the Environment library. *)

    SCase "x0 <> x".
      binds_cases H0.
        eauto using wf_env_strengthening.
        eauto using wf_env_strengthening.

  (** Informally, the typing_abs case is a straightforward application
      of the induction hypothesis, which is called H0 here. *)

  Case "typing_abs".

    (** We use the "pick fresh and apply" tactic to apply the rule
        typing_abs without having to calculate the appropriate finite
        set of atoms. *)

    pick fresh y and apply typing_abs.
    unfold open_ve.

    (** We cannot apply H0 directly here.  The first problem is that
        the induction hypothesis has (subst_ee open_ee), whereas in
        the goal we have (open_ee subst_ee).  The lemma
        subst_ee_open_ee_var lets us swap the order of these two
        operations. *)

    rewrite subst_ve_open_ve_var...

    (** The second problem is how the concatenations are associated in
        the environments.  In the goal, we currently have

<<       ([(y, bind_typ V)] ++ F ++ E),
>>
        where concatenation associates to the right.  In order to
        apply the induction hypothesis, we need

<<        (([(y, bind_typ V)] ++ F) ++ E).
>>
        We can use the rewrite_env tactic to perform this rewriting,
        or we can rewrite directly with an appropriate lemma from the
        Environment library. *)

    rewrite <- concat_assoc.

    (** Now we can apply the induction hypothesis. *)

    apply H0...

  (** The remaining cases in this proof are straightforward, given
      everything that we have pointed out above. *)

  Case "typing_app".
    rewrite (if_hoist (f == x) u f var_f).
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_app with (T1 := T1).
    SCase "callee".
      rewrite <- (if_hoist (f == x) u f var_f).
      apply IHTypT1...
    SCase "argument".
      rewrite <- (if_hoist (x0 == x) u x0 var_f).
      apply IHTypT2...

  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_ve_open_te_var...
    rewrite <- concat_assoc.
    apply H0...

  Case "typing_tapp".
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_tapp with (T1 := T1).
    SCase "callee".
      rewrite <- (if_hoist (x0 == x) u x0 var_f).
      apply IHTypT...
    SCase "type argument".
      eauto using sub_strengthening.

  Case "typing_let".
    pick fresh y and apply typing_let...
    unfold open_ve.
    rewrite subst_ve_open_ve_var...
    rewrite <- concat_assoc.
    apply H0...

  Case "typing_pair".
    rewrite (if_hoist (x1 == x) u x1 var_f).
    rewrite (if_hoist (x2 == x) u x2 var_f).
    apply typing_pair.
    SCase "first element".
      rewrite <- (if_hoist (x1 == x) u x1 var_f).
      apply IHTypT1...
    SCase "second element".
      rewrite <- (if_hoist (x2 == x) u x2 var_f).
      apply IHTypT2...

  Case "typing_fst".
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_fst with (T2 := T2).
    rewrite <- (if_hoist (x0 == x) u x0 var_f).
    apply IHTypT...

  Case "typing_snd".
    rewrite (if_hoist (x0 == x) u x0 var_f).
    apply typing_snd with (T1 := T1).
    rewrite <- (if_hoist (x0 == x) u x0 var_f).
    apply IHTypT...
Qed.
(* end show *)

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma typing_through_subst_te : forall Q E F Z e T P,
  typing (F ++ [(Z, bind_sub Q)] ++ E) e T ->
  sub E P Q ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         sub_through_subst_tt.
  intros Q E F Z e T P Typ PsubQ.
  eremember (F ++ [(Z, bind_sub Q)] ++ E) as G.
  generalize dependent F.
  induction Typ; intros F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  Case "typing_var".
    apply typing_var...
      rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
      binds_cases H0...
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    rewrite subst_te_open_ve_var...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E).
    apply H0...
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_sub V)] ++ F) ++ E).
    apply H0...
  Case "typing_tapp".
    rewrite subst_tt_open_tt...
  Case "typing_let".
    pick fresh y and apply typing_let.
    instantiate (1 := subst_tt Z P T1).
    apply IHTyp...
    rewrite subst_te_open_ve_var.
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ T1)] ++ F) ++ E).
    apply H0...
  Case "typing_pair".
    apply typing_pair.
    apply IHTyp1...
    apply IHTyp2...
  Case "typing_fst".
    eapply typing_fst, IHTyp...
  Case "typing_snd".
    eapply typing_snd, IHTyp...
Qed.

(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

(* ********************************************************************** *)
(** ** Inversion of typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing ([(x, bind_typ S1)] ++ E) (open_ve e1 x) S2 /\ sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  eremember (exp_abs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    split...
    exists T1. exists L...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing ([(X, bind_sub U1)] ++ E) (open_te e1 X) (open_tt S2 X)
     /\ sub ([(X, bind_sub U1)] ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros E S1 e1 T Typ.
  eremember (exp_tabs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ [(Y, bind_sub U1)] ++ E).
    apply (typing_narrowing S1)...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma typing_abs_typ_arrow_implies_sub_param : forall Γ U e T1 T2,
  typing Γ (exp_abs U e) (typ_arrow T1 T2) ->
  sub Γ T1 U.
Proof with eauto*.
  intros *.
  intros typ.
  destruct (typing_regular _ _ _ typ) as [wf_Γ [_ wf_T1_arr_T2]].
  inversion wf_T1_arr_T2; subst.
  eremember (exp_abs U e) as abs.
  eremember (typ_arrow T1 T2) as S.
  rename wf_T1_arr_T2 into wf_S.
  assert (S_sub_T1_arr_T2 : sub Γ S (typ_arrow T1 T2)) by (subst; apply sub_reflexivity; eauto).
  clear HeqS.
  induction typ; inversion Heqabs; subst.
  - inversion S_sub_T1_arr_T2...
  - eapply IHtyp...
    apply sub_transitivity with (Q := T)...
Qed.

Lemma typing_tabs_typ_all_implies_sub_param : forall Γ U e T1 T2,
  typing Γ (exp_tabs U e) (typ_all T1 T2) ->
  sub Γ T1 U.
Proof with eauto*.
  intros *.
  intros typ.
  destruct (typing_regular _ _ _ typ) as [wf_Γ [_ wf_all_T1_T2]].
  inversion wf_all_T1_T2; subst.
  eremember (exp_tabs U e) as tabs.
  eremember (typ_all T1 T2) as S.
  rename wf_all_T1_T2 into wf_S.
  assert (S_sub_all_T1_T2 : sub Γ S (typ_all T1 T2)) by (subst; apply sub_reflexivity; eauto).
  clear HeqS.
  induction typ; inversion Heqtabs; subst.
  - inversion S_sub_all_T1_T2...
  - eapply IHtyp...
    apply sub_transitivity with (Q := T)...
Qed.

Lemma typing_pair_typ_prod_implies_sub_components : forall Γ x1 x2 T1 T2,
  typing Γ (exp_pair x1 x2) (typ_prod T1 T2) ->
  typing Γ x1 T1 /\ typing Γ x2 T2.
Proof with eauto*.
  intros *.
  intros typ.
  destruct (typing_regular _ _ _ typ) as [wf_Γ [_ wf_prod_T1_T2]].
  inversion wf_prod_T1_T2; subst.
  eremember (exp_pair x1 x2) as pair.
  eremember (typ_prod T1 T2) as S.
  rename wf_prod_T1_T2 into wf_S.
  assert (S_sub_prod_T1_T2 : sub Γ S (typ_prod T1 T2)) by (subst; apply sub_reflexivity; eauto).
  clear HeqS.
  induction typ; inversion Heqpair; subst.
  - inversion S_sub_prod_T1_T2; subst...
  - eapply IHtyp...
    apply sub_transitivity with (Q := T)...
Qed.

Ltac impossible_typing typ :=
  clear - typ;
  match type of typ with
  | typing ?Γ ?e ?T =>
    let S := fresh "S" in
    eremember T as S eqn:HeqS;
    assert (S_sub_T : sub Γ S T) by (subst; apply sub_reflexivity; eauto);
    clear HeqS;
    dependent induction typ;
      [ inversion S_sub_T
      | (* cannot name IH in the dependent induction tactic, so we need to match *)
        match goal with 
        | H : sub ?Γ S ?T, IH : forall _ _, e = _ -> _ |- _ =>
            eapply IH; [ eauto | eapply sub_transitivity with (Q := T); eauto ]; trivial
        end ]
  end.

Goal forall Γ U e T1 T2,
  ~ typing Γ (exp_tabs U e) (typ_arrow T1 T2).
Proof with eauto*.
  intros Γ U e T1 T2 typ.
  impossible_typing typ.
Qed.

Goal forall Γ x y T1 T2,
  ~ typing Γ (exp_pair x y) (typ_all T1 T2).
Proof with eauto*.
  intros Γ x y T1 T2 typ.
  impossible_typing typ.
Qed.

Lemma binds_sub_arrow_implies_store_abs : forall S Γ TFun T1 T2 f,
  store_typing S Γ ->
  binds f (bind_typ TFun) Γ ->
  sub Γ TFun (typ_arrow T1 T2) ->
  exists U e abs_value, stores S f (exp_abs U e) abs_value /\ sub Γ T1 U.
Proof with eauto*.
  intros *.
  intros store_typ Γ_binds_f TFun_sub_T1_arr_T2.
  eremember (typ_arrow T1 T2) as T1_arr_T2.
  induction store_typ; inversion Γ_binds_f; inversion HeqT1_arr_T2; subst.
  destruct (f == x).
  - inversion H2; subst...
    unfold stores.
    unfold binds.
    simpl.
    destruct (x == x); [ clear e | contradict n; reflexivity ].
    inversion v_value; subst.
    + inversion H; subst.
      * exists T, e1, v_value.
        inversion TFun_sub_T1_arr_T2; subst.
        split...
      * exists T, e1, v_value.
        split...
        rewrite_env (empty ++ [(x, bind_typ TFun)] ++ Γ).
        apply sub_weakening.
        -- assert (abs_has_type_T1_arr_T2 : typing Γ (exp_abs T e1) (typ_arrow T1 T2)).
           { apply typing_sub with (S := TFun)...
             rewrite_env (empty ++ [(x, bind_typ TFun)] ++ Γ) in TFun_sub_T1_arr_T2.
             apply sub_strengthening in TFun_sub_T1_arr_T2... }
           apply (typing_abs_typ_arrow_implies_sub_param _ _ _ _ _ abs_has_type_T1_arr_T2).
        -- apply wf_env_typ...
    + assert (tabs_has_type_T1_arr_T2 : typing Γ (exp_tabs T e1) (typ_arrow T1 T2)).
      { apply typing_sub with (S := TFun)...
        rewrite_env (empty ++ [(x, bind_typ TFun)] ++ Γ) in TFun_sub_T1_arr_T2.
        apply sub_strengthening in TFun_sub_T1_arr_T2... }
      exfalso; impossible_typing tabs_has_type_T1_arr_T2.
    + assert (pair_has_type_T1_arr_T2 : typing Γ (exp_pair x0 y) (typ_arrow T1 T2)).
      { apply typing_sub with (S := TFun)...
        rewrite_env (empty ++ [(x, bind_typ TFun)] ++ Γ) in TFun_sub_T1_arr_T2.
        apply sub_strengthening in TFun_sub_T1_arr_T2... }
      exfalso; impossible_typing pair_has_type_T1_arr_T2.
  - assert (TFun_sub_T1_arr_T2' : sub Γ TFun (typ_arrow T1 T2)).
    { rewrite_env (empty ++ [(x, bind_typ T)] ++ Γ) in TFun_sub_T1_arr_T2.
      apply sub_strengthening in TFun_sub_T1_arr_T2... }
    destruct IHstore_typ as [U [e [abs_value [xv_S_stores_f T1_sub_U]]]]...
    exists U, e, abs_value.
    split.
    + rewrite_env ([let' x v v_value] ++ S).
      apply binds_tail.
      * trivial.
      * simpl; fsetdec.
    + rewrite_env (empty ++ [(x, bind_typ T)] ++ Γ).
      apply sub_weakening...
Qed.

Lemma binds_sub_all_implies_store_tabs : forall S Γ TAll T1 T2 f,
  store_typing S Γ ->
  binds f (bind_typ TAll) Γ ->
  sub Γ TAll (typ_all T1 T2) ->
  exists U e tabs_value, stores S f (exp_tabs U e) tabs_value /\ sub Γ T1 U.
Proof with eauto*.
  intros *.
  intros store_typ Γ_binds_f TAll_sub_all_T1_T2.
  induction store_typ; inversion Γ_binds_f; subst.
  - destruct (f == x).
    + inversion H2; subst...
      unfold stores.
      unfold binds.
      simpl.
      destruct (x == x); [ clear e | contradict n; reflexivity ].
      inversion v_value; subst.
      * assert (abs_has_type_all_T1_T2 : typing Γ (exp_abs T e1) (typ_all T1 T2)).
        { apply typing_sub with (S := TAll)...
          rewrite_env (empty ++ [(x, bind_typ TAll)] ++ Γ) in TAll_sub_all_T1_T2.
          apply sub_strengthening in TAll_sub_all_T1_T2... }
        exfalso; impossible_typing abs_has_type_all_T1_T2.
      * inversion H; subst.
        -- exists T, e1, v_value.
           inversion TAll_sub_all_T1_T2; subst.
           split...
        -- exists T, e1, v_value.
           split...
           rewrite_env (empty ++ [(x, bind_typ TAll)] ++ Γ).
           apply sub_weakening.
           ++ assert (tabs_has_type_all_T1_T2 : typing Γ (exp_tabs T e1) (typ_all T1 T2)).
              { apply typing_sub with (S := TAll)...
                rewrite_env (empty ++ [(x, bind_typ TAll)] ++ Γ) in TAll_sub_all_T1_T2.
                apply sub_strengthening in TAll_sub_all_T1_T2... }
              apply (typing_tabs_typ_all_implies_sub_param _ _ _ _ _ tabs_has_type_all_T1_T2).
           ++ apply wf_env_typ...
      * assert (pair_has_type_all_T1_T2 : typing Γ (exp_pair x0 y) (typ_all T1 T2)).
        { apply typing_sub with (S := TAll)...
          rewrite_env (empty ++ [(x, bind_typ TAll)] ++ Γ) in TAll_sub_all_T1_T2.
          apply sub_strengthening in TAll_sub_all_T1_T2... }
        exfalso; impossible_typing pair_has_type_all_T1_T2.
    + assert (TAll_sub_all_T1_T2' : sub Γ TAll (typ_all T1 T2)).
      { rewrite_env (empty ++ [(x, bind_typ T)] ++ Γ) in TAll_sub_all_T1_T2.
        apply sub_strengthening in TAll_sub_all_T1_T2... }
      destruct IHstore_typ...
      destruct H1 as [x1 [x1_value [S_stores_x T1_sub_x0]]].
      exists x0, x1, x1_value.
      split.
      * rewrite_env ([let' x v v_value] ++ S).
        apply binds_tail.
        -- trivial.
        -- simpl; fsetdec.
      * rewrite_env (empty ++ [(x, bind_typ T)] ++ Γ).
        apply sub_weakening...
Qed.

Lemma binds_sub_prod_implies_store_pair : forall S Γ TProd T1 T2 x,
  store_typing S Γ ->
  binds x (bind_typ TProd) Γ ->
  sub Γ TProd (typ_prod T1 T2) ->
  exists x1 x2 pair_value, stores S x (exp_pair x1 x2) pair_value /\ typing Γ x1 T1 /\ typing Γ x2 T2.
Proof with eauto*.
  intros *.
  intros store_typ Γ_binds_x TProd_sub_prod_T1_T2.
  induction store_typ; inversion Γ_binds_x; subst...
  - Case "typing_store_cons_typ".
    destruct (x == x0); subst.
    + SCase "x = x0".
      inversion H2; subst. 
      unfold stores.
      unfold binds.
      simpl.
      destruct (x0 == x0); [ clear e | contradict n; reflexivity ].
      inversion v_value; subst.
      * assert (abs_has_type_prod_T1_T2 : typing Γ (exp_abs T e1) (typ_prod T1 T2)).
        { apply typing_sub with (S := TProd)...
          rewrite_env (empty ++ [(x0, bind_typ TProd)] ++ Γ) in TProd_sub_prod_T1_T2.
          apply sub_strengthening in TProd_sub_prod_T1_T2... }
        exfalso; impossible_typing abs_has_type_prod_T1_T2.
      * assert (tabs_has_type_prod_T1_T2 : typing Γ (exp_tabs T e1) (typ_prod T1 T2)).
        { apply typing_sub with (S := TProd)...
          rewrite_env (empty ++ [(x0, bind_typ TProd)] ++ Γ) in TProd_sub_prod_T1_T2.
          apply sub_strengthening in TProd_sub_prod_T1_T2... }
        exfalso; impossible_typing tabs_has_type_prod_T1_T2.
      * inversion H; subst.
        -- exists x, y, v_value.
           inversion TProd_sub_prod_T1_T2; subst.
           repeat split...
           ++ apply typing_sub with (S := T0)...
              rewrite_env (empty ++ [(x0, bind_typ (typ_prod T0 T3))] ++ Γ).
              apply typing_weakening...
           ++ apply typing_sub with (S := T3)...
              rewrite_env (empty ++ [(x0, bind_typ (typ_prod T0 T3))] ++ Γ).
              apply typing_weakening...
        -- exists x, y, v_value.
           rewrite_env (empty ++ [(x0, bind_typ TProd)] ++ Γ).
           assert (prod_has_type_prod_T1_T2 : typing Γ (exp_pair x y) (typ_prod T1 T2)).
           { apply typing_sub with (S := TProd)...
             rewrite_env (empty ++ [(x0, bind_typ TProd)] ++ Γ) in TProd_sub_prod_T1_T2.
             apply sub_strengthening in TProd_sub_prod_T1_T2... }
           repeat split...
           all: apply typing_weakening; eauto;
                apply (typing_pair_typ_prod_implies_sub_components _ _ _ _ _ prod_has_type_prod_T1_T2).
    + SCase "x <> x0".
      assert (TProd_sub_prod_T1_T2' : sub Γ TProd (typ_prod T1 T2)).
      { rewrite_env (empty ++ [(x0, bind_typ T)] ++ Γ) in TProd_sub_prod_T1_T2.
        apply sub_strengthening in TProd_sub_prod_T1_T2... }
      destruct IHstore_typ as [x1 [x2 [pair_value [S_stores_x [typ1 typ2]]]]]...
      exists x1, x2, pair_value.
      repeat split.
      * rewrite_env ([let' x0 v v_value] ++ S).
        apply binds_tail.
        -- trivial.
        -- simpl; fsetdec.
      * rewrite_env (empty ++ [(x0, bind_typ T)] ++ Γ).
        apply typing_weakening...
      * rewrite_env (empty ++ [(x0, bind_typ T)] ++ Γ).
        apply typing_weakening...
Qed.

Lemma stores_implies_typing : forall S Γ x v v_value,
  store_typing S Γ ->
  stores S x v v_value ->
  exists T, typing Γ v T.
Proof with eauto*.
  intros S Γ y v v_value store_typ store.
  induction store_typ; inversion store.
  - destruct (y == x); subst.
    + Case "x = y".
      exists T.
      inversion H2; subst.
      rewrite_env (empty ++ [(x, bind_typ T)] ++ Γ).
      apply typing_weakening.
      apply H.
      destruct (typing_regular Γ v T H) as [wf_Γ [_ wf_T]].
      apply wf_env_typ...
    + Case "x <> y".
      destruct (IHstore_typ H2) as [U v_T].
      exists U.
      rewrite_env (empty ++ [(x, bind_typ T)] ++ Γ).
      apply typing_weakening.
      apply v_T.
      destruct (typing_regular Γ v0 T H) as [wf_Γ [_ wf_T]].
      apply wf_env_typ...
Qed.

Lemma typing_of_var_comes_from_binds : forall Γ (x : atom) T,
  typing Γ x T ->
  exists S, binds x (bind_typ S) Γ /\ sub Γ S T.
Proof with eauto using sub_reflexivity, sub_transitivity.
  intros Γ x T typ.
  destruct (typing_regular _ _ _ typ) as [_ [_ wf_T]].
  eremember (x : exp) as e.
  induction typ; inversion Heqe; subst.
  - Case "typing_var".
    exists T; split.
    + apply H0.
    + apply sub_reflexivity...
  - Case "typing_sub".
    destruct IHtyp as [R [x_binds_R sub_R]]...
    exists R; split.
    + apply x_binds_R.
    + apply sub_transitivity with (Q := S)...
Qed.

Lemma stores_preserves_typing : forall S Γ x v v_value T,
  store_typing S Γ ->
  stores S x v v_value ->
  typing Γ x T ->
  typing Γ v T.
Proof with eauto*.
  intros S Γ x v v_value T store_typ store typ.
  induction store_typ as [|y U w w_value S' Γ' store_typ' IH typ' y_fresh].
  - inversion store as [some_w_eq_some_v].
  - inversion store as [some_w_eq_some_v].
    destruct (x == y); subst.
    + Case "x = y".
      inversion some_w_eq_some_v; subst.
      destruct (typing_of_var_comes_from_binds _ _ _ typ) as [S [y_binds_S S_sub_T]].
      inversion y_binds_S.
      destruct (y == y); try (contradict n; reflexivity).
      inversion H0; subst.
      rewrite_env (empty ++ [(y, bind_typ S)] ++ Γ').
      apply typing_weakening.
      * apply typing_sub with (S := S).
        apply typ'.
        rewrite_env (empty ++ [(y, bind_typ S)] ++ Γ') in S_sub_T.
        apply sub_strengthening in S_sub_T.
        apply S_sub_T.
      * apply (typing_regular _ _ _ typ).
    + Case "x <> y".
      assert (IHstore : stores S' x v v_value).
      { inversion store.
        destruct (x == y); try (contradict e; apply n).
        apply H0.
      }
      assert (IHtyp : typing Γ' x T).
      { rewrite_env (empty ++ [(y, bind_typ U)] ++ Γ') in typ.
        apply typing_strengthening in typ; simpl...
      }
      rewrite_env (empty ++ [(y, bind_typ U)] ++ Γ').
      apply typing_weakening...
Qed.

Lemma cont_typ_inversion : forall Γ c c_scope E T V,
  eval_typing Γ (cont c c_scope :: E) T V ->
  exists U L,
    (forall x : atom, x `notin` L ->
      typing ([(x, bind_typ T)] ++ Γ) (open_ve c x) U)
    /\ eval_typing Γ E U V.
Proof with eauto.
  intros Γ c c_scope E T V Typ.
  inversion Typ; subst.
  exists U, L.
  split...
Qed.

Lemma stores_functional : forall S x v1 v1_value v2 v2_value,
  stores S x v1 v1_value ->
  stores S x v2 v2_value ->
  { eq : v1 = v2 | eq_rect v1 value v1_value v2 eq = v2_value }.
Proof with eauto*.
  intros *. intros store1 store2.
  unfold stores, binds in *.
  rewrite store1 in store2.
  inversion store2...
  assert (exist value v1 v1_value = exist value v2 v2_value).
  { congruence. }
  inversion_sigma.
  exists H1...
Qed.

Lemma preservation' : forall S E e S' E' e' V,
  state_typing ⟨ S | E | e ⟩ V ->
  (forall L, red' L ⟨ S | E | e ⟩ ⟨ S' | E' | e' ⟩) ->
  state_typing ⟨ S' | E' | e' ⟩ V.
Proof with simpl_env; eauto*.
  intros S E e S' E' e' V [T Γ store_typ cont_typ current_typ] Red.
  simpl in *.
  induction current_typ; subst; rename E0 into Γ.
  - Case "typing_var".
    inversion cont_typ; subst.
    + SCase "typing_eval_nil".
      specialize (Red {}); inversion Red; subst; inversion v_value.
    + SCase "typing_eval_cons".
      specialize (Red (dom Γ `union` L)); inversion Red; subst.
      * SSCase "red_lift".
        inversion v_value.
      * SSCase "red_let_var".
        apply typing_state with (Γ := [(y, bind_typ T)] ++ Γ) (T := U); simpl.
        -- SSSCase "store_typing".
           apply typing_store_cons...
           eapply stores_preserves_typing...
        -- SSSCase "eval_typing".
           rewrite_env (empty ++ [(y, bind_typ T)] ++ Γ).
           apply eval_typing_weakening...
           apply wf_env_typ...
           destruct (typing_regular _ _ _ (H1 y (ltac:(fsetdec)))) as [wf_xT_Γ _].
           inversion wf_xT_Γ; subst...
        -- SSSCase "typing".
           apply H1...
  - Case "typing_abs".
    inversion cont_typ; subst.
    + SCase "final".
      specialize (Red {}); inversion Red.
    + SCase "cont".
      specialize (Red (dom Γ `union` L0)); inversion Red; subst.
      apply typing_state with (Γ := [(x, bind_typ (typ_arrow V0 T1))] ++ Γ) (T := U); simpl.
      * SSCase "store_typing".
        apply typing_store_cons...
        eapply typing_abs.
        apply H.
      * SSCase "eval_typing".
        rewrite_env (empty ++ [(x, bind_typ (typ_arrow V0 T1))] ++ Γ).
        apply eval_typing_weakening...
        apply (typing_regular _ _ _ (H1 x ltac:(fsetdec))).
      * SSCase "typing".
        apply (H1 x)...
  - Case "typing_app".
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ1) as [TFun [Γ_binds_f S_sub_T]].
    destruct (binds_sub_arrow_implies_store_abs _ _ _ _ _ _ store_typ Γ_binds_f S_sub_T) as [U [e [abs_value [S_stores_abs T1_sub_U]]]].
    assert (abs_typing : typing Γ (exp_abs U e) (typ_arrow T1 T2)).
    { apply stores_preserves_typing with (S := S) (Γ := Γ) (x := f) (v_value := abs_value)... }
    destruct (typing_inv_abs _ _ _ _ abs_typing T1 T2 ltac:(eauto using sub_reflexivity)) as [P1 [S2 [L' P2]]].
    inversion cont_typ; subst.
    + SCase "final".
      specialize (Red (dom Γ `union` L' `union` fv_ve (open_ve e x))); inversion Red; subst.
      assert (arg_typing : typing Γ v T1).
      { eapply stores_preserves_typing with (x := x) (v_value := v_value)... }
      destruct (stores_functional _ _ _ _ _ _ S_stores_abs H4) as [eq_abs _]; injection eq_abs as e_eq_e0 U_eq_U0; subst.
      eapply typing_state with (Γ := Γ) (T := T2); simpl.
      * SSCase "store_typing".
        assumption.
      * SSCase "eval_typing".
        apply typing_eval_nil...
      * SSCase "typing".
        destruct (P2 x) as [xU_Γ_e_S2 S2_sub_V]...
        apply typing_sub with (S := S2)...
        rewrite_env (empty ++ Γ).
        apply typing_strengthening with (x := x) (S := U0)...
    + SCase "cont".
      assert (wf_T2 : wf_typ Γ T2).
      { destruct (sub_regular _ _ _ S_sub_T) as [_ [_ wf_T1_arr_T2]].
        inversion wf_T1_arr_T2... }
      specialize (Red (dom Γ `union` L `union` L' `union` fv_ve (open_ve e x))); inversion Red; subst.
      * SSCase "red_lift".
        eapply typing_state with (Γ := [(x0, bind_typ T2)] ++ Γ) (T := U0); simpl.
        -- apply typing_store_cons...
        -- rewrite_env (empty ++ Γ) in H0.
           apply eval_typing_weakening with (F := [(x0, bind_typ T2)]) in H0.
           apply H0.
           apply wf_env_typ...
        -- apply (H x0)...
      * SSCase "red_app".
        assert (arg_typing : typing Γ v T1).
        { eapply stores_preserves_typing with (x := x) (v_value := v_value)... }
        eapply typing_state with (Γ := Γ) (T := T2); simpl...
        destruct (stores_functional _ _ _ _ _ _ S_stores_abs H4) as [eq_abs _]; injection eq_abs as e_eq_e0 U_eq_U0; subst.
        destruct (P2 x ltac:(fsetdec)).
        apply typing_sub with (S := S2)...
        rewrite_env (empty ++ Γ).
        apply typing_strengthening with (x := x) (S := U1)...
  - Case "typing_tabs".
    inversion cont_typ; subst.
    + SCase "final".
      specialize (Red {}); inversion Red.
    + SCase "cont".
      specialize (Red (dom Γ `union` L0)); inversion Red; subst.
      apply typing_state with (Γ := [(x, bind_typ (typ_all V0 T1))] ++ Γ) (T := U); simpl.
      * SSCase "store_typing".
        apply typing_store_cons...
        eapply typing_tabs.
        apply H.
      * SSCase "eval_typing".
        rewrite_env (empty ++ [(x, bind_typ (typ_all V0 T1))] ++ Γ).
        apply eval_typing_weakening...
        apply (typing_regular _ _ _ (H1 x ltac:(fsetdec))).
      * SSCase "typing".
        apply (H1 x)...
  - Case "typing_tapp".
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ) as [TAll [Γ_binds_x S_sub_T]].
    destruct (binds_sub_all_implies_store_tabs _ _ _ _ _ _ store_typ Γ_binds_x S_sub_T) as [U [e [tabs_value [S_stores_tabs T1_sub_U]]]].
    assert (tabs_typing : typing Γ (exp_tabs U e) (typ_all T1 T2)).
    { apply stores_preserves_typing with (S := S) (Γ := Γ) (x := x) (v_value := tabs_value)... }
    destruct (typing_inv_tabs _ _ _ _ tabs_typing T1 T2 ltac:(eauto using sub_reflexivity)) as [P1 [S2 [L' P2]]].
    inversion cont_typ; subst.
    + SCase "final".
      specialize (Red (dom Γ `union` L')); inversion Red; subst.
      destruct (stores_functional _ _ _ _ _ _ S_stores_tabs H5) as [eq_abs _]; injection eq_abs as e_eq_e0 U_eq_U0; subst.
      apply typing_state with (Γ := Γ) (T := open_tt T2 T); simpl.
      * SSCase "store_typing".
        assumption.
      * SSCase "eval_typing".
        assumption.
      * SSCase "typing".
        pick fresh X.
        destruct (P2 X) as [? ?]...
        rewrite (subst_te_intro X)...
        rewrite (subst_tt_intro X)...
        rewrite_env (map (subst_tb X T) empty ++ Γ).
        apply (typing_through_subst_te T1)...
    + SCase "cont".
      destruct (sub_regular _ _ _ S_sub_T) as [_ [_ wf_all_T1_T2]].
      inversion wf_all_T1_T2; subst...
      specialize (Red (dom Γ `union` L `union` L')); inversion Red; subst.
      * SSCase "red_lift".
        inversion v_value.
      * SSCase "red_tapp".
        eapply typing_state with (Γ := Γ) (T := open_tt T2 T); simpl.
        -- SSSCase "store_typing".
           assumption.
        -- SSSCase "eval_typing".
           apply typing_eval_cons with (L := L) (U := U0)...
        -- SSSCase "typing".
           destruct (stores_functional _ _ _ _ _ _ S_stores_tabs H7) as [eq_abs _]; injection eq_abs as e_eq_e0 U_eq_U0; subst.
           pick fresh X.
           destruct (P2 X) as [? ?]...
           rewrite (subst_te_intro X)...
           rewrite (subst_tt_intro X)...
           rewrite_env (map (subst_tb X T) empty ++ Γ).
           apply (typing_through_subst_te T1)...
  - Case "typing_let".
    specialize (Red (dom Γ `union` L)); inversion Red; subst.
    * SSCase "red_lift".
      inversion v_value.
    * SSCase "red_let_var".
      eapply typing_state with (Γ := [(x, bind_typ T1)] ++ Γ) (T := T2); simpl.
      -- apply typing_store_cons...
      -- rewrite_env (empty ++ [(x, bind_typ T1)] ++ Γ).
        apply eval_typing_weakening...
      -- apply H...
    * SSCase "red_let_exp".
      eapply typing_state with (Γ := Γ) (T := T1); simpl.
      -- assumption.
      -- apply typing_eval_cons with (L := L) (U := T2)...
      -- assumption.
  - Case "typing_pair".
    inversion cont_typ; subst.
    + SCase "final".
      specialize (Red {}); inversion Red.
    + SCase "cont".
      specialize (Red (dom Γ `union` L)); inversion Red; subst.
      apply typing_state with (Γ := [(x, bind_typ (typ_prod T1 T2))] ++ Γ) (T := U); simpl.
      * SSCase "store_typing".
        apply typing_store_cons...
        apply typing_pair...
      * SSCase "eval_typing".
        rewrite_env (empty ++ [(x, bind_typ (typ_prod T1 T2))] ++ Γ).
        apply eval_typing_weakening...
      * SSCase "typing".
        apply (H x)...
  - Case "typing_fst".
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ) as [TProd [Γ_binds_x TProd_sub_prod_T1_T2]].
    destruct (binds_sub_prod_implies_store_pair _ _ _ _ _ _ store_typ Γ_binds_x TProd_sub_prod_T1_T2) as [x1 [x2 [pair_value [S_stores_pair [typ1 typ2]]]]].
    inversion cont_typ; subst.
    + SCase "final".
      specialize (Red {}); inversion Red; subst.
      eapply typing_state; simpl...
    + SCase "cont".
      specialize (Red (dom Γ `union` L)); inversion Red; subst.
      * apply typing_state with (Γ := [(x0, bind_typ T1)] ++ Γ) (T := U); simpl.
        -- SSCase "store_typing".
           apply typing_store_cons...
           apply typing_fst with (T2 := T2)...
        -- SSCase "eval_typing".
           rewrite_env (empty ++ [(x0, bind_typ T1)] ++ Γ).
           apply eval_typing_weakening...
        -- SSCase "typing".
           apply (H x0)...
      * apply typing_state with (Γ := Γ) (T := T1); simpl...
  - Case "typing_snd".
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ) as [TProd [Γ_binds_x TProd_sub_prod_T1_T2]].
    destruct (binds_sub_prod_implies_store_pair _ _ _ _ _ _ store_typ Γ_binds_x TProd_sub_prod_T1_T2) as [x1 [x2 [pair_value [S_stores_pair [typ1 typ2]]]]].
    inversion cont_typ; subst.
    + SCase "final".
      specialize (Red {}); inversion Red; subst.
      eapply typing_state; simpl...
    + SCase "cont".
      specialize (Red (dom Γ `union` L)); inversion Red; subst.
      * apply typing_state with (Γ := [(x0, bind_typ T2)] ++ Γ) (T := U); simpl.
        -- SSCase "store_typing".
          apply typing_store_cons...
          apply typing_snd with (T1 := T1)...
        -- SSCase "eval_typing".
          rewrite_env (empty ++ [(x0, bind_typ T2)] ++ Γ).
          apply eval_typing_weakening...
        -- SSCase "typing".
          apply (H x0)...
      * apply typing_state with (Γ := Γ) (T := T2); simpl...
  - Case "typing_sub".
    apply IHcurrent_typ...
    eapply eval_specializing...
Qed.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 Val Typ.
  eremember empty as E.
  eremember (typ_arrow U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_tabs : forall e U1 U2,
  value e ->
  typing empty e (typ_all U1 U2) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 Val Typ.
  eremember empty as E.
  eremember (typ_all U1 U2) as T.
  revert U1 U2 HeqT HeqT.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_pair : forall e U1 U2,
  value e ->
  typing empty e (typ_prod U1 U2) ->
  exists (x y : atom), e = exp_pair x y.
Proof with eauto*.
  intros e U1 U2 Val Typ.
  eremember empty as E.
  eremember (typ_prod U1 U2) as T.
  revert U1 U2 HeqT HeqT.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall S E e T,
  state_typing ⟨ S | E | e ⟩ T ->
  final_state ⟨ S | E | e ⟩ \/ exists L S' E' e', red' L ⟨ S | E | e ⟩ ⟨ S' | E' | e' ⟩.
Proof with eauto.
  intros S E e T [U Γ store_typ eval_typ current_typ].
  simpl in *.
  induction current_typ; subst.
  - Case "typing_var".
    inversion eval_typ; subst.
    + left; split; simpl...
    + right.
      destruct (binds_implies_store _ _ _ _ store_typ H0) as [v [v_value store]].
      exists {}, (let' x v v_value :: S), E1, (open_ve c x).
      apply red_let_var'...
  - Case "typing_abs".
    inversion eval_typ; subst.
    + left; split; simpl...
      apply answer_val.
      destruct (sub_regular _ _ _ H2) as [_ [wf_V_arr_T1 _]].
      inversion wf_V_arr_T1; subst.
      apply value_abs with (L := L).
      * eapply type_from_wf_typ...
      * intros x x_fresh.
        apply (typing_regular _ _ _ (H x ltac:(fsetdec))).
    + right.
      assert (forall x0, x0 `notin` L -> expr (open_ve e x0)).
      { intros x0 x0_fresh.
        destruct (typing_regular _ _ _ (H x0 ltac:(fsetdec))) as [_ [wf_open_e_x _]]... }
      pick fresh x.
      destruct (typing_regular _ _ _ (H x ltac:(fsetdec))) as [wf_xV_E0 _].
      inversion wf_xV_E0; subst.
      assert (V_type : type V) by (eapply type_from_wf_typ; eauto).
      assert (abs_value : value (exp_abs V e)).
      { apply value_abs with (L := L)... }
      exists L, (let' x (exp_abs V e) abs_value :: S), E1, (open_ve c x).
      apply red_lift'.
      fsetdec.
  - Case "typing_app".
    right.
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ1) as [TFun [Γ_binds_f S_sub_T]].
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ2) as [TArg [Γ_binds_x _]].
    destruct (binds_sub_arrow_implies_store_abs _ _ _ _ _ _ store_typ Γ_binds_f S_sub_T) as [U [e [abs_value [S_stores_abs T1_sub_U]]]].
    destruct (binds_implies_store _ _ _ _ store_typ Γ_binds_x) as [v [v_value store]].
    exists {}, S, E, (open_ve e x).
    apply red_app' with (U := U) (v := v) (v_value := v_value) (abs_value := abs_value)...
  - Case "typing_tabs".
    inversion eval_typ; subst.
    + left; split; simpl...
      apply answer_val.
      destruct (sub_regular _ _ _ H2) as [_ [wf_all_V_T1 _]].
      inversion wf_all_V_T1; subst.
      apply value_tabs with (L := L).
      * eapply type_from_wf_typ...
      * intros x x_fresh.
        apply (typing_regular _ _ _ (H x ltac:(fsetdec))).
    + right.
      assert (forall x0, x0 `notin` L -> expr (open_te e x0)).
      { intros x0 x0_fresh.
        destruct (typing_regular _ _ _ (H x0 ltac:(fsetdec))) as [_ [wf_open_e_x _]]... }
      pick fresh x.
      destruct (typing_regular _ _ _ (H x ltac:(fsetdec))) as [wf_xV_E0 _].
      inversion wf_xV_E0; subst.
      assert (V_type : type V) by (eapply type_from_wf_typ; eauto).
      assert (tabs_value : value (exp_tabs V e)).
      { apply value_tabs with (L := L)... }
      exists L, (let' x (exp_tabs V e) tabs_value :: S), E1, (open_ve c x).
      apply red_lift'.
      fsetdec.
  - Case "typing_tapp".
    right.
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ) as [TAll [Γ_binds_f S_sub_T]].
    destruct (binds_sub_all_implies_store_tabs _ _ _ _ _ _ store_typ Γ_binds_f S_sub_T) as [U [e [tabs_value [S_stores_tabs T1_sub_U]]]].
    exists {}, S, E, (open_te e T0).
    apply red_tapp' with (U := U) (tabs_value := tabs_value)...
  - Case "typing_let".
    right.
    assert (c_scope : scope c).
    { exists L.
      intros x x_fresh.
      apply (typing_regular _ _ _ (H x ltac:(fsetdec))). }
    exists L, S, (cont c c_scope :: E), e.
    apply red_let_exp'.
  - Case "typing_pair".
    inversion eval_typ; subst.
    + left; split; simpl...
    + right.
      assert (pair_value : value (exp_pair x1 x2)).
      { apply value_pair. }
      pick fresh x.
      exists L, (let' x (exp_pair x1 x2) pair_value :: S), E1, (open_ve c x).
      apply red_lift'...
  - Case "typing_fst".
    right.
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ) as [TProd [Γ_binds_x TProd_sub_prod_T1_T2]].
    destruct (binds_sub_prod_implies_store_pair _ _ _ _ _ _ store_typ Γ_binds_x TProd_sub_prod_T1_T2) as [x1 [x2 [pair_value [S_stores_abs _]]]].
    exists {}, S, E, x1.
    eapply red_fst'...
  - Case "typing_snd".
    right.
    destruct (typing_of_var_comes_from_binds _ _ _ current_typ) as [TProd [Γ_binds_x TProd_sub_prod_T1_T2]].
    destruct (binds_sub_prod_implies_store_pair _ _ _ _ _ _ store_typ Γ_binds_x TProd_sub_prod_T1_T2) as [x1 [x2 [pair_value [S_stores_abs _]]]].
    exists {}, S, E, x2.
    eapply red_snd'...
  - Case "typing_sub".
    destruct IHcurrent_typ...
    eapply eval_specializing...
Qed.
