Set Warnings "-notation-overridden".
From Coq Require Import List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Hoare.
From PLF Require Import Semantics.
From PLF Require Import Soundness.


(* Before we talk about the ghost variable rule itself,
   we need 2 preliminaries:
   1. An equivalence relation on states that doesn't care
      about the values of ghost variables.
   2. We need to define what it means for a variable to
      not appear in an expression, and prove the basic property:
      If a variable doesn't appear in an expression, its value
      cannot impact the evaluation of the expression.
   
   We'll use the shorthand DHG to mean "doesn't have ghosts". *)

Lemma differ_refl
    gvars st :
      <<gvars>> st ~ st.
Proof.
  intros x.
  right.
  reflexivity.
Qed.

Lemma differ_symm
    gvars st st'
    (H_differ : <<gvars>> st ~ st') :
      <<gvars>> st' ~ st.
Proof.
  intros x.
  destruct (H_differ x); auto.
Qed.

Lemma differ_trans
    gvars st st' st''
    (H_differ1 : <<gvars>> st ~ st')
    (H_differ2 : <<gvars>> st' ~ st'') :
      <<gvars>> st ~ st''.
Proof.
  intros x.
  destruct (H_differ1 x) as [H_In_gvars | H_st_st'].
  - left.
    assumption.
  - rewrite H_st_st'.
    apply H_differ2.
Qed.

Lemma t_update_gvar
    gvars g v st
    (H_In_gvars : In g gvars) :
      <<gvars>> st ~ (g !-> v ; st).
Proof.
  intros x.
  destruct (string_dec g x) as [H_g_x | H_g_x].
  - subst.
    left.
    assumption.
  - rewrite t_update_neq; try assumption.
    apply differ_refl.
Qed.

Inductive aexp_dhg (gvars : list string) : aexp -> Prop :=
  | ADHG_num : forall (n : nat),
      aexp_dhg gvars n
  | ADHG_var : forall (x : string),
      ~(In x gvars) ->
      aexp_dhg gvars x
  | ADHG_add : forall a1 a2,
      aexp_dhg gvars a1 ->
      aexp_dhg gvars a2 ->
      aexp_dhg gvars <{ a1 + a2 }>
  | ADHG_sub : forall a1 a2,
      aexp_dhg gvars a1 ->
      aexp_dhg gvars a2 ->
      aexp_dhg gvars <{ a1 - a2 }>
  | ADHG_mul : forall a1 a2,
      aexp_dhg gvars a1 ->
      aexp_dhg gvars a2 ->
      aexp_dhg gvars <{ a1 * a2 }>.

Lemma adhg_eval
    gvars a st st'
    (H_adhg : aexp_dhg gvars a)
    (H_differ : <<gvars>> st ~ st') :
      aeval st a = aeval st' a.
Proof.
  induction H_adhg; simpl in *; try auto.
  set (H_st_st'_x := H_differ x).
  destruct H_st_st'_x.
  - exfalso.
    auto.
  - assumption.
Qed.

Inductive bexp_dhg (gvars : list string) : bexp -> Prop :=
  | BDHG_true :
      bexp_dhg gvars <{ true }>
  | BDHG_false :
      bexp_dhg gvars <{ false }>
  | BDHG_eq : forall a1 a2,
      aexp_dhg gvars a1 ->
      aexp_dhg gvars a2 ->
      bexp_dhg gvars <{ a1 = a2 }>
  | BDHG_neq : forall a1 a2,
      aexp_dhg gvars a1 ->
      aexp_dhg gvars a2 ->
      bexp_dhg gvars <{ a1 <> a2 }>
  | BDHG_le : forall a1 a2,
      aexp_dhg gvars a1 ->
      aexp_dhg gvars a2 ->
      bexp_dhg gvars <{ a1 <= a2 }>
  | BDHG_gt : forall a1 a2,
      aexp_dhg gvars a1 ->
      aexp_dhg gvars a2 ->
      bexp_dhg gvars <{ a1 > a2 }>
  | BDHG_not : forall b,
      bexp_dhg gvars b ->
      bexp_dhg gvars <{ ~b }>
  | BDHG_and : forall b1 b2,
      bexp_dhg gvars b1 ->
      bexp_dhg gvars b2 ->
      bexp_dhg gvars <{ b1 && b2 }>.

Lemma bdhg_eval
    gvars b st st'
    (H_dhg : bexp_dhg gvars b)
    (H_differ : <<gvars>> st ~ st') :
      beval st b = beval st' b.
Proof.
  induction H_dhg; simpl in *;
  try reflexivity;
  try (f_equal; apply adhg_eval with gvars; assumption);
  try (f_equal; f_equal; apply adhg_eval with gvars; assumption);
  try (f_equal; assumption).
Qed.

Definition assertion_dhg
    (gvars : list string) (P : Assertion)
    : Prop :=
  forall st st',
    <<gvars>> st ~ st' ->
    (P st <-> P st').

Lemma bexp_assertion_dhg
    gvars b
    (H_bdhg : bexp_dhg gvars b) :
      assertion_dhg gvars b.
Proof.
  unfold assertion_dhg.
  simpl.
  intros st st' H_differ.
  assert (H_b_st_st' : beval st b = beval st' b) by (apply bdhg_eval with gvars; assumption).
  rewrite H_b_st_st'.
  reflexivity.
Qed.

Reserved Notation " '<(' gvars ')>' c '~>' c' "
                  (at level 3,
                   c custom com at level 99,
                   c' custom com at level 99). 
Inductive remove_ghost_variables (gvars : list string) : com -> com -> Prop :=
  | GSkip :
      <(gvars)> skip ~> skip
  | GAsgnNonGhost : forall x a,
      ~ In x gvars ->
      aexp_dhg gvars a ->
      <(gvars)> x := a ~> x := a
  | GAsgnGhost : forall g a (H_In_gvars : In g gvars),
      <(gvars)> g := a ~> skip
  | GSeq : forall c1 c1' c2 c2',
      <(gvars)> c1 ~> c1' ->
      <(gvars)> c2 ~> c2' ->
      <(gvars)> <{ c1 ; c2 }> ~> <{ c1' ; c2' }>
  | GSeqSkip1 : forall c1 c2 c2',
      <(gvars)> c1 ~> skip ->
      <(gvars)> c2 ~> c2' ->
      <(gvars)> <{ c1 ; c2 }> ~> c2'
  | GIf : forall b c1 c1' c2 c2',
      <(gvars)> c1 ~> c1' ->
      <(gvars)> c2 ~> c2' ->
      bexp_dhg gvars b ->
      <(gvars)> if b then c1 else c2 end ~> if b then c1' else c2' end
  | GWhile : forall b c c',
      <(gvars)> c ~> c' ->
      bexp_dhg gvars b ->
      <(gvars)> while b do c end ~> while b do c' end
  | GAtomic : forall c c',
      <(gvars)> c ~> c' ->
      <(gvars)> atomic c end ~> atomic c' end
  | GAtomicAsgn : forall c x a,
      <(gvars)> c ~> x := a ->
      <(gvars)> atomic c end ~> x := a
  | GPar : forall c1 c1' c2 c2',
      <(gvars)> c1 ~> c1' ->
      <(gvars)> c2 ~> c2' ->
      <(gvars)> c1 || c2 ~> c1' || c2'
  
  where " '<(' gvars ')>' c '~>' c' " := (remove_ghost_variables gvars c c').


Lemma seq_multistep
    cl1 cr1 c3 st1 st3 :
  (<{ cl1 ; cr1 }> / st1 -->* c3 / st3) <->
  (
    (
      exists cl3,
        c3 = <{ cl3 ; cr1 }> /\
        cl1 / st1 -->* cl3 / st3
    ) \/
    (
      exists st2,
        cl1 / st1 -->* <{ skip }> / st2 /\
        cr1 / st2 -->* c3 / st3
    )
  ).
Proof.
  split.
  - intros H_step.
    remember (<{ cl1 ; cr1 }>, st1) as p1.
    remember (c3, st3) as p2.
    generalize dependent cl1.
    generalize dependent cr1.
    generalize dependent st1.
    generalize dependent c3.
    generalize dependent st3.
    induction H_step; intros; subst.
    + invert Heqp1.
      left.
      exists cl1.
      split; [reflexivity | constructor].
    + destruct y as [c2 st2].
      specialize (IHH_step st3 c3 eq_refl st2).
      invert H.
      * specialize (IHH_step cr1 c1' eq_refl).
        destruct IHH_step.
        -- destruct H as [cl3 [H_eq_c3 H_step']].
           left.
           exists cl3.
           split; try assumption.
           apply multi_step with (c1', st2); assumption.
        -- destruct H as [st2' [H_step' H_step'']].
           right.
           exists st2'.
           split; try assumption.
           apply multi_step with (c1', st2); assumption.
      * right.
        exists st2.
        split; [constructor | assumption].
  - intros [[cl3 [H_eq_c3 H_step]] | [st2 [H_step1 H_step2]]].
    + subst.
      remember (cl1, st1) as p1.
      remember (cl3, st3) as p2.
      generalize dependent cl1.
      generalize dependent st1.
      induction H_step; intros; subst.
      * invert Heqp1.
        constructor.
      * destruct y as [cl2 st2].
        specialize (IHH_step eq_refl st2 cl2 eq_refl).
        apply multi_step with (<{ cl2 ; cr1 }>, st2); try assumption.
        constructor.
        assumption.
    + rename c3 into c4.
      rename st3 into st4.
      rename st2 into st3.
      remember (cl1, st1) as p1.
      remember (<{ skip }>, st3) as p2.
      generalize dependent cl1.
      generalize dependent cr1.
      generalize dependent st1.
      generalize dependent st3.
      induction H_step1; intros; subst.
      * invert Heqp1.
        apply multi_step with (cr1, st1); [ constructor | assumption ].
      * destruct y as [cl2 st2].
        specialize (IHH_step1 st3 eq_refl st2 cr1 H_step2 cl2 eq_refl).
        apply multi_step with (<{ cl2; cr1 }>, st2); try assumption.
        constructor.
        assumption.
Qed.


Inductive rmulti {T : Type} (R : T -> T -> Prop) : T -> T -> Prop :=
  | rmulti_refl : forall x,
      rmulti R x x
  | rmulti_step : forall x y z,
      rmulti R x y ->
      R y z ->
      rmulti R x z.

Lemma multi_iff_rmulti
    {T : Type} (R : T -> T -> Prop) x y :
      multi R x y <-> rmulti R x y.
Admitted.

Inductive while_multistep (b : bexp) : com -> state -> com -> state -> Prop :=
  | WMS_empty' : forall c st,
    while_multistep b c st <{ while b do c end }> st
  | WMS_if' : forall c st,
    while_multistep b c st <{ if b then c ; while b do c end else skip end }> st
  | WMS_end' : forall c st,
    beval st b = false ->
    while_multistep b c st <{ skip }> st
  | WMS_seq' : forall c st c' st',
    beval st b = true ->
    c / st -->* c' / st' ->
    while_multistep b c st <{ c' ; while b do c end }> st'
  | WMS_cycle : forall c st st' c'' st'',
    beval st b = true ->
    c / st -->* <{ skip }> / st' ->
    while_multistep b c st' c'' st'' ->
    while_multistep b c st c'' st''.

Lemma while_multistep_lemma
    b c st c' st'
    (H_steps : <{ while b do c end }> / st -->* c' / st') :
      while_multistep b c st c' st'.
Proof.
  remember (<{ while b do c end }>, st) as p.
  remember (c', st') as p'.
  generalize dependent b.
  generalize dependent c.
  generalize dependent st.
  generalize dependent c'.
  generalize dependent st'.
  apply multi_iff_rmulti in H_steps.
  induction H_steps; intros; subst.
  - invert Heqp.
    constructor.
  - rename c' into c''.
    rename st' into st''.
    destruct y as [c' st'].
    specialize (IHH_steps st' c' eq_refl st c b eq_refl).
    generalize dependent st''.
    generalize dependent c''.
    clear H_steps.
    induction IHH_steps; intros.
    + invert H.
      constructor.
    + invert H.
      * constructor; try assumption.
        constructor.
      * constructor.
        assumption.
    + invert H0.
    + invert H1.
      * constructor; try assumption.
        apply multi_trans with (c', st'); try assumption.
        apply multi_R.
        assumption.
      * econstructor; try assumption.
        -- apply H0.
        -- constructor.
    + specialize (IHIHH_steps c''0 st''0 H1).
      econstructor; try assumption.
      * apply H0.
      * assumption.
Qed.

Lemma par_multistep1
    c1 c2 st c1' st'
    (H_steps1 : c1 / st -->* c1' / st') :
      <{ c1 || c2 }> / st -->* <{ c1' || c2 }> / st'.
Proof.
  remember (c1, st) as p.
  remember (c1', st') as p'.
  generalize dependent c1.
  generalize dependent st.
  induction H_steps1; intros; subst.
  - invert Heqp.
    constructor.
  - destruct y as [c1_m st_m].
    specialize (IHH_steps1 eq_refl st_m c1_m eq_refl).
    apply multi_trans with (<{ c1_m || c2 }>, st_m); try assumption.
    apply multi_R.
    constructor.
    assumption.
Qed.

Lemma par_multistep2
    c1 c2 st c2' st'
    (H_steps2 : c2 / st -->* c2' / st') :
      <{ c1 || c2 }> / st -->* <{ c1 || c2' }> / st'.
Proof.
  remember (c2, st) as p.
  remember (c2', st') as p'.
  generalize dependent c2.
  generalize dependent st.
  induction H_steps2; intros; subst.
  - invert Heqp.
    constructor.
  - destruct y as [c2_m st_m].
    specialize (IHH_steps2 eq_refl st_m c2_m eq_refl).
    apply multi_trans with (<{ c1 || c2_m }>, st_m); try assumption.
    apply multi_R.
    constructor.
    assumption.
Qed.


Inductive no_par : com -> Prop :=
  | NP_Skip :
      no_par <{ skip }>
  | NP_Asgn : forall x a,
      no_par <{ x := a }>
  | NP_Seq : forall c1 c2,
      no_par c1 ->
      no_par c2 ->
      no_par <{ c1 ; c2 }>
  | NP_If : forall b c1 c2,
      no_par c1 ->
      no_par c2 ->
      no_par <{ if b then c1 else c2 end }>
  | NP_While : forall b c,
      no_par c ->
      no_par <{ while b do c end }>
  | NP_Atomic : forall c,
      no_par c ->
      no_par <{ atomic c end }>.

Inductive no_par_in_atomic : com -> Prop :=
  | NPIA_Skip :
      no_par_in_atomic <{ skip }>
  | NPIA_Asgn : forall x a,
      no_par_in_atomic <{ x := a }>
  | NPIA_Seq : forall c1 c2,
      no_par_in_atomic c1 ->
      no_par_in_atomic c2 ->
      no_par_in_atomic <{ c1 ; c2 }>
  | NPIA_If : forall b c1 c2,
      no_par_in_atomic c1 ->
      no_par_in_atomic c2 ->
      no_par_in_atomic <{ if b then c1 else c2 end }>
  | NPIA_While : forall b c,
      no_par_in_atomic c ->
      no_par_in_atomic <{ while b do c end }>
  | NPIA_Atomic : forall c,
      no_par c ->
      no_par_in_atomic <{ atomic c end }>
  | NPIA_Par : forall c1 c2,
      no_par_in_atomic c1 ->
      no_par_in_atomic c2 ->
      no_par_in_atomic <{ c1 || c2 }>.

Lemma step_npia
    c st c' st'
    (H_npia : no_par_in_atomic c)
    (H_step : c / st --> c' / st') :
      no_par_in_atomic c'.
Proof.
  generalize dependent st.
  generalize dependent c'.
  generalize dependent st'.
  induction H_npia; intros.
  - invert H_step.
  - invert H_step.
    constructor.
  - invert H_step.
    + constructor; try assumption.
      eapply IHH_npia1.
      eassumption.
    + assumption.
  - invert H_step.
    + assumption.
    + assumption.
  - invert H_step.
    constructor; constructor; try assumption.
    constructor.
    assumption.
  - invert H_step.
    constructor.
  - invert H_step.
    + constructor; try assumption.
      eapply IHH_npia1.
      eassumption.
    + constructor; try assumption.
      eapply IHH_npia2.
      eassumption.
    + constructor.
Qed.

Lemma fcomp_npia
    c st c' st'
    (C : fcomp c st c' st')
    (H_npia : no_par_in_atomic c) :
      no_par_in_atomic c'.
Proof.
  induction C.
  - assumption.
  - eapply step_npia.
    + apply IHC.
      assumption.
    + eassumption.
  - apply IHC.
    assumption.
Qed.


Definition assertion_doesnt_restrict
    (gvars : list string) (P : Assertion) : Prop :=
  forall st, exists st',
    <<gvars>> st ~ st' /\
    P st'.

Definition rely_doesnt_restrict
    (gvars : list string) (R : list Assertion) : Prop :=
  forall st st', exists st'',
    <<gvars>> st' ~ st'' /\
    Forall (fun r => r st -> r st'') R.

Lemma remove_to_skip
    gvars c st
    (H_remove_gvars : <(gvars)> c ~> skip) :
      exists st',
        <<gvars>> st ~ st' /\
        c / st -->* <{ skip }> / st'.
Proof.
  remember <{ skip }>.
  generalize dependent st.
  induction H_remove_gvars; intros; subst; try discriminate.
  - exists st.
    split.
    + apply differ_refl.
    + constructor.
  - exists (g !-> aeval st a ; st).
    split.
    + apply t_update_gvar.
      assumption.
    + apply multi_R.
      constructor.
  - specialize (IHH_remove_gvars1 eq_refl st).
    destruct IHH_remove_gvars1 as [st' [H_differ H_steps1]].
    specialize (IHH_remove_gvars2 eq_refl st').
    destruct IHH_remove_gvars2 as [st'' [H_differ' H_steps2]].
    exists st''.
    split.
    + apply differ_trans with st'; assumption.
    + apply seq_multistep.
      right.
      exists st'.
      split; assumption.
Qed.

Lemma multistep_add_gvars
    gvars c_dhg st_dhg c_dhg' st_dhg' c_hg st_hg
    (H_np : no_par c_dhg)
    (H_remove_gvars : <(gvars)> c_hg ~> c_dhg)
    (H_differ : <<gvars>> st_hg ~ st_dhg)
    (H_steps_dhg : c_dhg / st_dhg -->* c_dhg' / st_dhg') :
      exists c_hg' st_hg',
        <(gvars)> c_hg' ~> c_dhg' /\
        <<gvars>> st_hg' ~ st_dhg' /\
        c_hg / st_hg -->* c_hg' / st_hg' /\ 
        Forall (fun g => st_dhg g = st_dhg' g) gvars.
Proof.
  generalize dependent c_dhg'.
  generalize dependent st_dhg'.
  generalize dependent st_dhg.
  generalize dependent st_hg.
  induction H_remove_gvars; intros.
  - invert H_steps_dhg.
    2: invert H.
    exists <{ skip }>, st_hg.
    repeat split; try (constructor; assumption); try assumption.
    apply Forall_forall.
    intros g H_In_gvars.
    reflexivity.
  - invert H_steps_dhg.
    + exists <{ x := a }>, st_hg.
      repeat split; try (constructor; assumption); try assumption.
      apply Forall_forall.
      intros g H_In_gvars.
      reflexivity.
    + rename c_dhg' into c_dhg''.
      rename st_dhg' into st_dhg''.
      destruct y as [c_dhg' st_dhg'].
      invert H1.
      invert H2.
      2: invert H1.
      exists <{ skip }>, (x !-> aeval st_hg a ; st_hg).
      repeat split; try (constructor; assumption).
      * intros x'.
        destruct (string_dec x x').
        -- subst.
           right.
           rewrite t_update_eq.
           rewrite t_update_eq.
           apply adhg_eval with gvars; assumption.
        -- rewrite t_update_neq; try assumption.
           rewrite t_update_neq; try assumption.
           apply H_differ.
      * econstructor; constructor.
      * apply Forall_forall.
        intros g H_In_gvars.
        destruct (string_dec x g).
        -- subst.
           exfalso.
           auto.
        -- rewrite t_update_neq; try assumption.
           reflexivity.
  - invert H_steps_dhg.
    2: invert H.
    exists <{ skip }>, (g !-> aeval st_hg a ; st_hg).
    repeat split; try (constructor; assumption).
    * apply differ_trans with st_hg; try assumption.
      apply differ_symm.
      apply t_update_gvar.
      assumption.
    * econstructor; constructor.
    * apply Forall_forall.
      intros g' H_In_gvars'.
      reflexivity.
  - rename c1 into c1_hg.
    rename c1' into c1_dhg.
    rename c2 into c2_hg.
    rename c2' into c2_dhg.
    invert H_np.
    specialize (IHH_remove_gvars1 H1).
    specialize (IHH_remove_gvars2 H2).
    clear H1 H2.
    apply seq_multistep in H_steps_dhg.
    destruct H_steps_dhg as [[c1_dhg' [H_eq_c_dhg' H_steps_1dhg]] | [st_dhg_m [H_steps_1dhg H_steps_2dhg]]].
    + clear IHH_remove_gvars2.
      specialize (IHH_remove_gvars1 st_hg st_dhg H_differ st_dhg' c1_dhg' H_steps_1dhg).
      destruct IHH_remove_gvars1 as [c1_hg' [st_hg' [H_remove_gvars1' [H_differ' [H_steps_1hg H_eq_gvars]]]]].
      subst.
      exists <{ c1_hg' ; c2_hg }>, st_hg'.
      repeat split; try (constructor; assumption); try assumption.
      apply seq_multistep.
      left.
      exists c1_hg'.
      split; auto.
    + specialize (IHH_remove_gvars1 st_hg st_dhg H_differ st_dhg_m <{ skip }> H_steps_1dhg).
      destruct IHH_remove_gvars1 as [skip' [st_hg_m [H_remove_gvars_skip [H_differ_m [H_steps_1hg H_eq_gvars1]]]]].
      apply remove_to_skip with (st := st_hg_m) in H_remove_gvars_skip.
      destruct H_remove_gvars_skip as [st_hg_m' [H_differ_m_ H_steps]].
      assert (H_differ_m' : <<gvars>> st_hg_m' ~ st_dhg_m). {
        apply differ_trans with st_hg_m; try assumption.
        apply differ_symm.
        assumption.
      }
      specialize (IHH_remove_gvars2 st_hg_m' st_dhg_m H_differ_m' st_dhg' c_dhg' H_steps_2dhg).
      destruct IHH_remove_gvars2 as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps_2hg H_eq_gvars2]]]]].
      exists c_hg', st_hg'.
      repeat split; try assumption.
      * apply seq_multistep.
        right.
        exists st_hg_m'.
        split; try assumption.
        apply multi_trans with (skip', st_hg_m); assumption.
      * rewrite Forall_forall in *.
        intros g' H_In_gvars'.
        transitivity (st_dhg_m g').
        -- apply H_eq_gvars1.
           assumption.
        -- apply H_eq_gvars2.
           assumption.
  - rename c1 into c1_hg.
    rename c2 into c2_hg.
    rename c2' into c2_dhg.
    specialize (IHH_remove_gvars1 NP_Skip st_hg st_dhg H_differ st_dhg <{ skip }> (multi_refl cstep (<{ skip }>, st_dhg))).
    destruct IHH_remove_gvars1 as [skip' [st_hg_m [H_remove_gvars_skip [H_differ_m [H_steps_1hg H_eq_gvars1]]]]].
    apply remove_to_skip with (st := st_hg_m) in H_remove_gvars_skip.
    destruct H_remove_gvars_skip as [st_hg_m' [H_differ_m_ H_steps]].
    assert (H_differ_m' : <<gvars>> st_hg_m' ~ st_dhg). {
      apply differ_trans with st_hg_m; try assumption.
      apply differ_symm.
      assumption.
    }
    specialize (IHH_remove_gvars2 H_np st_hg_m' st_dhg H_differ_m' st_dhg' c_dhg' H_steps_dhg).
    destruct IHH_remove_gvars2 as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps_2hg H_eq_gvars2]]]]].
    exists c_hg', st_hg'.
    repeat split; try assumption.
    apply seq_multistep.
    right.
    exists st_hg_m'.
    split; try assumption.
    apply multi_trans with (skip', st_hg_m); assumption.
  - rename c1 into c1_hg.
    rename c1' into c1_dhg.
    rename c2 into c2_hg.
    rename c2' into c2_dhg.
    invert H_np.
    specialize (IHH_remove_gvars1 H2).
    specialize (IHH_remove_gvars2 H4).
    clear H2 H4.
    invert H_steps_dhg.
    + exists <{ if b then c1_hg else c2_hg end }>, st_hg.
      repeat split; try (constructor; assumption); try assumption.
      apply Forall_forall.
      intros g H_In_gvars.
      reflexivity.
    + rename c_dhg' into c_dhg''.
      rename st_dhg' into st_dhg''.
      rename H0 into H_step_dhg.
      rename H1 into H_steps_dhg.
      destruct y as [c_dhg' st_dhg'].
      invert H_step_dhg.
      * clear IHH_remove_gvars2.
        specialize (IHH_remove_gvars1 st_hg st_dhg' H_differ st_dhg'' c_dhg'' H_steps_dhg).
        destruct IHH_remove_gvars1 as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [H_steps_hg H_eq_gvars']]]]].
        exists c_hg'', st_hg''.
        repeat split; try assumption.
        econstructor.
        -- apply CS_IfTrue.
           rewrite <- H1.
           apply bdhg_eval with gvars; assumption.
        -- assumption.
      * clear IHH_remove_gvars1.
        specialize (IHH_remove_gvars2 st_hg st_dhg' H_differ st_dhg'' c_dhg'' H_steps_dhg).
        destruct IHH_remove_gvars2 as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [H_steps_hg H_eq_gvars']]]]].
        exists c_hg'', st_hg''.
        repeat split; try assumption.
        econstructor.
        -- apply CS_IfFalse.
           rewrite <- H1.
           apply bdhg_eval with gvars; assumption.
        -- assumption.
  - invert H_np.
    specialize (IHH_remove_gvars H1).
    clear H1.
    apply while_multistep_lemma in H_steps_dhg.
    generalize dependent st_hg.
    induction H_steps_dhg; intros.
    + exists <{ while b do c end }>, st_hg.
      repeat split; try (constructor; assumption); try assumption.
      apply Forall_forall.
      intros g H_In_gvars.
      reflexivity.
    + exists <{ if b then c ; while b do c end else skip end }>, st_hg.
      repeat split; try assumption.
      * constructor; try assumption; constructor; try assumption.
        constructor; assumption.
      * apply multi_R.
        constructor.
      * apply Forall_forall.
        intros g H_In_gvars.
        reflexivity.
    + exists <{ skip }>, st_hg.
      repeat split; try (constructor; assumption); try assumption.
      * econstructor.
        1: constructor.
        apply multi_R.
        constructor.
        rewrite <- H0.
        apply bdhg_eval with gvars; assumption.
      * apply Forall_forall.
        intros g H_In_gvars.
        reflexivity.
    + specialize (IHH_remove_gvars st_hg st H_differ st' c' H1).
      destruct IHH_remove_gvars as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps H_eq_gvars]]]]].
      exists <{ c_hg' ; while b do c end }>, st_hg'.
      repeat split; try assumption.
      * constructor; try assumption.
        constructor; assumption.
      * econstructor.
        1: constructor.
        econstructor.
        1: constructor. {
          rewrite <- H0.
          apply bdhg_eval with gvars; assumption.
        }
        apply seq_multistep.
        left.
        exists c_hg'.
        split; try reflexivity.
        assumption.
    + specialize (IHH_steps_dhg H_remove_gvars IHH_remove_gvars).
      specialize (IHH_remove_gvars st_hg st H_differ st' <{ skip }> H1).
      destruct IHH_remove_gvars as [skip' [st_hg' [H_remove_gvars_skip [H_differ' [H_steps H_eq_gvars]]]]].
      apply remove_to_skip with (st := st_hg') in H_remove_gvars_skip.
      destruct H_remove_gvars_skip as [st_hg'_ [H_differ_skip H_steps_skip]].
      assert (H_differ'_ : <<gvars>> st_hg'_ ~ st'). {
        apply differ_trans with st_hg'; try assumption.
        apply differ_symm.
        assumption.
      }
      specialize (IHH_steps_dhg st_hg'_ H_differ'_).
      destruct IHH_steps_dhg as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [H_steps' H_eq_gvars']]]]].
      exists c_hg'', st_hg''.
      repeat split; try assumption.
      * econstructor.
        1: constructor.
        econstructor.
        1: constructor. {
          rewrite <- H0.
          apply bdhg_eval with gvars; assumption.
        }
        apply seq_multistep.
        right.
        exists st_hg'_.
        split; try assumption.
        apply multi_trans with (skip', st_hg'); assumption.
      * rewrite Forall_forall in *.
        intros g' H_In_gvars'.
        transitivity (st' g').
        -- apply H_eq_gvars.
           assumption.
        -- apply H_eq_gvars'.
           assumption.
  - invert H_np.
    specialize (IHH_remove_gvars H0).
    clear H0.
    invert H_steps_dhg.
    + exists <{ atomic c end }>, st_hg.
      repeat split; try (constructor; assumption); try assumption.
      apply Forall_forall.
      intros g H_In_gvars.
      reflexivity.
    + rename c_dhg' into c_dhg''.
      rename st_dhg' into st_dhg''.
      rename H into H_step_dhg.
      rename H0 into H_steps_dhg.
      destruct y as [c_dhg' st_dhg'].
      invert H_step_dhg.
      invert H_steps_dhg.
      2: invert H.
      specialize (IHH_remove_gvars st_hg st_dhg H_differ st_dhg'' <{ skip }> H0).
      destruct IHH_remove_gvars as [skip' [st_hg'' [H_remove_gvars_skip [H_differ'' [H_steps H_eq_gvars]]]]].
      apply remove_to_skip with (st := st_hg'') in H_remove_gvars_skip.
      destruct H_remove_gvars_skip as [st_hg''_ [H_differ''_ H_steps']].
      exists <{ skip }>, st_hg''_.
      repeat split; try (constructor; assumption); try assumption.
      * apply differ_trans with st_hg''; try assumption.
        apply differ_symm.
        assumption.
      * apply multi_R.
        constructor.
        apply multi_trans with (skip', st_hg''); assumption.
  - rename c into c_hg.
    specialize (IHH_remove_gvars H_np st_hg st_dhg H_differ st_dhg' c_dhg' H_steps_dhg).
    destruct IHH_remove_gvars as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps_hg H_eq_gvars]]]]].
    invert H_steps_dhg.
    + exists <{ atomic c_hg end }>, st_hg.
      repeat split; try (constructor; assumption); try assumption.
    + invert H.
      invert H0.
      2: invert H.
      apply remove_to_skip with (st := st_hg') in H_remove_gvars'.
      destruct H_remove_gvars' as [st_hg'' [H_differ'' H_steps_hg']].
      exists <{ skip }>, st_hg''.
      repeat split; try (constructor; assumption); try assumption.
      * apply differ_trans with st_hg'; try assumption.
        apply differ_symm.
        assumption.
      * apply multi_R.
        constructor.
        apply multi_trans with (c_hg', st_hg'); assumption.
  - invert H_np.
Qed.

Lemma step_add_gvars
    gvars c_dhg st_dhg c_dhg' st_dhg' c_hg st_hg
    (H_npia : no_par_in_atomic c_dhg)
    (H_remove_gvars : <(gvars)> c_hg ~> c_dhg)
    (H_differ : <<gvars>> st_hg ~ st_dhg)
    (H_step_dhg : c_dhg / st_dhg --> c_dhg' / st_dhg') :
      exists c_hg_m st_hg_m c_hg' st_hg',
        <<gvars>> st_hg_m ~ st_dhg /\
        c_hg / st_hg -->* c_hg_m / st_hg_m /\
        <(gvars)> c_hg' ~> c_dhg' /\
        << gvars>> st_hg' ~ st_dhg' /\
        c_hg_m / st_hg_m --> c_hg' / st_hg' /\
        Forall (fun g => st_dhg g = st_dhg' g) gvars.
Proof.
  generalize dependent c_dhg'.
  generalize dependent st_hg.
  induction H_remove_gvars; intros.
  - invert H_step_dhg.
  - invert H_step_dhg.
    exists <{ x := a }>, st_hg, <{ skip }>, (x !-> aeval st_hg a ; st_hg).
    repeat split; try assumption; try (constructor; assumption).
    + intros x'.
      destruct (string_dec x x').
      * subst.
        right.
        rewrite t_update_eq.
        rewrite t_update_eq.
        apply adhg_eval with gvars; assumption.
      * rewrite t_update_neq; try assumption.
        rewrite t_update_neq; try assumption.
        apply H_differ.
    + apply Forall_forall.
      intros g H_In_gvars.
      destruct (string_dec x g).
      * subst.
        exfalso.
        auto.
      * symmetry.
        apply t_update_neq.
        assumption.
  - invert H_step_dhg.
  - rename c1 into c1_hg.
    rename c1' into c1_dhg.
    rename c2 into c2_hg.
    rename c2' into c2_dhg.
    invert H_npia.
    specialize (IHH_remove_gvars1 H1).
    specialize (IHH_remove_gvars2 H2).
    clear H1 H2.
    specialize (IHH_remove_gvars1 st_hg H_differ).
    specialize (IHH_remove_gvars2 st_hg H_differ).
    invert H_step_dhg.
    + rename c1' into c1_dhg'.
      specialize (IHH_remove_gvars1 c1_dhg' H0).
      destruct IHH_remove_gvars1 as [c1_hg_m [st_hg_m [c1_hg' [st_hg' [H_differ_m [H_steps_m [H_remove_gvars' [H_differ' [H_step' H_eq_gvars]]]]]]]]].
      exists <{ c1_hg_m ; c2_hg }>, st_hg_m, <{ c1_hg' ; c2_hg }>, st_hg'.
      repeat split; try assumption; try (constructor; assumption).
      apply seq_multistep.
      left.
      exists c1_hg_m.
      split; try reflexivity.
      assumption.
    + clear IHH_remove_gvars1.
      apply remove_to_skip with (st := st_hg) in H_remove_gvars1.
      destruct H_remove_gvars1 as [st_hg_m [H_differ_m H_steps_m]].
      exists <{ skip ; c2_hg }>, st_hg_m, c2_hg, st_hg_m.
      repeat split; try assumption; try (apply Forall_forall; auto).
      * apply differ_trans with st_hg; try assumption.
        apply differ_symm.
        assumption.
      * apply seq_multistep.
        left.
        exists <{ skip }>.
        split; try reflexivity.
        assumption.
      * apply differ_trans with st_hg; try assumption.
        apply differ_symm.
        assumption.
      * constructor.
  - rename c1 into c1_hg.
    rename c2 into c2_hg.
    rename c2' into c2_dhg.
    clear IHH_remove_gvars1.
    apply remove_to_skip with (st := st_hg) in H_remove_gvars1.
    destruct H_remove_gvars1 as [st_hg_m1 [H_differ_m1_ H_steps_m1]].
    assert (H_differ_m1 : <<gvars>> st_hg_m1 ~ st_dhg). {
      apply differ_trans with st_hg; try assumption.
      apply differ_symm.
      assumption.
    }
    specialize (IHH_remove_gvars2 H_npia st_hg_m1 H_differ_m1 c_dhg' H_step_dhg).
    destruct IHH_remove_gvars2 as [c_hg_m [st_hg_m2 [c_hg' [st_hg' [H_differ_m2 [H_steps_m2 [H_remove_gvars' [H_differ' [H_step_hg H_eq_gvars]]]]]]]]].
    exists c_hg_m, st_hg_m2, c_hg', st_hg'.
    repeat split; try assumption.
    apply seq_multistep.
    right.
    exists st_hg_m1.
    split; assumption.
  - rename c1 into c1_hg.
    rename c1' into c1_dhg.
    rename c2 into c2_hg.
    rename c2' into c2_dhg.
    invert H_npia.
    specialize (IHH_remove_gvars1 H2).
    specialize (IHH_remove_gvars2 H4).
    clear H2 H4.
    exists <{ if b then c1_hg else c2_hg end }>, st_hg.
    invert H_step_dhg.
    + exists c1_hg, st_hg.
      repeat split; try assumption; try apply multi_refl; try (apply Forall_forall; auto).
      constructor.
      rewrite <- H1.
      apply bdhg_eval with gvars; assumption.
    + exists c2_hg, st_hg.
      repeat split; try assumption; try apply multi_refl; try (apply Forall_forall; auto).
      constructor.
      rewrite <- H1.
      apply bdhg_eval with gvars; assumption.
  - rename c into c_hg.
    rename c' into c_dhg.
    invert H_step_dhg.
    exists <{ while b do c_hg end }>, st_hg, <{ if b then c_hg ; while b do c_hg end else skip end }>, st_hg.
    repeat split; try assumption; try (constructor; assumption); try (apply Forall_forall; auto).
    repeat constructor; assumption.
  - rename c into c_hg.
    rename c' into c_dhg.
    invert H_step_dhg.
    invert H_npia.
    assert (exists c_hg' st_hg',
        <(gvars)> c_hg' ~> skip /\
        <<gvars>> st_hg' ~ st_dhg' /\
        c_hg / st_hg -->* c_hg' / st_hg' /\ 
        Forall (fun g => st_dhg g = st_dhg' g) gvars) as [c_hg' [st_hg' [H_remove_gvars_skip [H_differ' [H_steps_hg H_eq_gvars]]]]]. {
      apply multistep_add_gvars with c_dhg; assumption.
    }
    apply remove_to_skip with (st := st_hg') in H_remove_gvars_skip.
    destruct H_remove_gvars_skip as [st_hg'' [H_differ'' H_steps_hg']].
    exists <{ atomic c_hg end }>, st_hg, <{ skip }>, st_hg''.
    repeat split; try assumption; try (constructor; assumption).
    + apply differ_trans with st_hg'; try assumption.
      apply differ_symm.
      assumption.
    + constructor.
      apply multi_trans with (c_hg', st_hg'); assumption.
  - rename c into c_hg.
    specialize (IHH_remove_gvars H_npia st_hg H_differ c_dhg' H_step_dhg).
    destruct IHH_remove_gvars as [c_hg_m [st_hg_m [c_hg' [st_hg' [H_differ_m [H_steps_m [H_remove_gvars' [H_differ' [H_step_hg H_eq_gvars]]]]]]]]].
    invert H_step_dhg.
    apply remove_to_skip with (st := st_hg') in H_remove_gvars'.
    destruct H_remove_gvars' as [st_hg_m' [H_differ_m' H_steps_m']].
    exists <{ atomic c_hg end }>, st_hg, <{ skip }>, st_hg_m'.
    repeat split; try assumption; try (constructor; assumption).
    + apply differ_trans with st_hg'; try assumption.
      apply differ_symm.
      assumption.
    + constructor.
      apply multi_trans with (c_hg_m, st_hg_m); try assumption.
      apply multi_trans with (c_hg', st_hg'); try assumption.
      apply multi_R.
      assumption.
  - rename c1 into c1_hg.
    rename c1' into c1_dhg.
    rename c2 into c2_hg.
    rename c2' into c2_dhg.
    invert H_npia.
    specialize (IHH_remove_gvars1 H1).
    specialize (IHH_remove_gvars2 H2).
    clear H1 H2.
    invert H_step_dhg.
    + rename c1' into c1_dhg'.
      rename H0 into H_step_dhg.
      clear IHH_remove_gvars2.
      specialize (IHH_remove_gvars1 st_hg H_differ c1_dhg' H_step_dhg).
      destruct IHH_remove_gvars1 as [c1_hg_m [st_hg_m [c1_hg' [st_hg' [H_differ_m [H_steps_m [H_remove_gvars' [H_differ' [H_step_hg H_eq_gvars]]]]]]]]].
      exists <{ c1_hg_m || c2_hg }>, st_hg_m, <{ c1_hg' || c2_hg }>, st_hg'.
      repeat split; try assumption; try (constructor; assumption).
      apply par_multistep1.
      assumption.
    + rename c2' into c2_dhg'.
      rename H0 into H_step_dhg.
      clear IHH_remove_gvars1.
      specialize (IHH_remove_gvars2 st_hg H_differ c2_dhg' H_step_dhg).
      destruct IHH_remove_gvars2 as [c2_hg_m [st_hg_m [c2_hg' [st_hg' [H_differ_m [H_steps_m [H_remove_gvars' [H_differ' [H_step_hg H_eq_gvars]]]]]]]]].
      exists <{ c1_hg || c2_hg_m }>, st_hg_m, <{ c1_hg || c2_hg' }>, st_hg'.
      repeat split; try assumption; try (constructor; assumption).
      apply par_multistep2.
      assumption.
    + clear IHH_remove_gvars1.
      clear IHH_remove_gvars2.
      apply remove_to_skip with (st := st_hg) in H_remove_gvars1.
      destruct H_remove_gvars1 as [st_hg_m1 [H_differ_m1 H_steps_hg_m1]].
      apply remove_to_skip with (st := st_hg_m1) in H_remove_gvars2.
      destruct H_remove_gvars2 as [st_hg_m2 [H_differ_m2 H_steps_hg_m2]].
      exists <{ skip || skip }>, st_hg_m2, <{ skip }>, st_hg_m2.
      repeat split; try (apply differ_trans with st_hg; try assumption; apply differ_symm; apply differ_trans with st_hg_m1; assumption); try (constructor; assumption); try (apply Forall_forall; auto).
      apply multi_trans with (<{ skip || c2_hg }>, st_hg_m1).
      * apply par_multistep1.
        assumption.
      * apply par_multistep2.
        assumption.
Qed.


Lemma fcomp_app_steps
    c st c' st' c'' st'' P R
    (C : fcomp c st c' st')
    (H_steps : c' / st' -->* c'' / st'')
    (H_assumption : fcomp_assumption P R C) :
      exists (C' : fcomp c st c'' st''),
      fcomp_assumption P R C'.
Proof.
  remember (c', st') as p'.
  remember (c'', st'') as p''.
  generalize dependent c'.
  generalize dependent st'.
  induction H_steps; intros; subst.
  - invert Heqp'.
    exists C.
    assumption.
  - destruct y as [c_m st_m].
    apply IHH_steps with st_m c_m (fcomp_cmp c st c' st' c_m st_m H C); try reflexivity.
    simpl.
    assumption.
Qed.

Definition com_havoc_gvars
    (gvars : list string) (c : com) : Prop :=
  forall st1 st1' st2 st2',
    <<gvars>> st1 ~ st2 ->
    <<gvars>> st1' ~ st2' ->
    c / st1 -->* <{ skip }> / st1' ->
    c / st2 -->* <{ skip }> / st2'.

Definition guar_havoc_gvars
    (gvars : list string) (G : list (Assertion * com)) : Prop :=
  Forall (fun (g : Assertion * com) =>
    let (Q, c) := g in
    assertion_dhg gvars Q /\ com_havoc_gvars gvars c
  ) G.

Lemma fcomp_add_gvars
   gvars c_dhg st_dhg c_dhg' st_dhg' c_hg st_hg P_dhg P_hg R_dhg R_hg G Q
    (C_dhg : fcomp c_dhg st_dhg c_dhg' st_dhg')
    (H_npia : no_par_in_atomic c_dhg)
    (H_remove_gvars : <(gvars)> c_hg ~> c_dhg)
    (H_differ : <<gvars>> st_hg ~ st_dhg)
    (H_P_dhg : assertion_dhg gvars P_dhg)
    (H_P_hg : P_hg st_hg)
    (H_R_dhg : Forall (assertion_dhg gvars) R_dhg)
    (H_R_hg : rely_doesnt_restrict gvars R_hg)
    (H_G_havoc : guar_havoc_gvars gvars G)
    (H_valid_hg : f|= c_hg sat ({{ P_dhg /\ P_hg }}, R_dhg ++ R_hg, G, Q))
    (H_assumption_dhg : fcomp_assumption P_dhg R_dhg C_dhg) :
      exists c_hg' st_hg' (C_hg : fcomp c_hg st_hg c_hg' st_hg'),
        <(gvars)> c_hg' ~> c_dhg' /\
        <<gvars>> st_hg' ~ st_dhg' /\
        fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg /\
        fcomp_sat_guar G C_dhg.
Proof.
  unfold fcomp_conclusion.
  generalize dependent c_hg.
  induction C_dhg; intros; simpl in *.
  - rename c into c_dhg.
    rename st into st_dhg.
    set (C_hg := fcomp_empty c_hg st_hg).
    assert (H_P_dhg_st_hg : P_dhg st_hg). {
      eapply H_P_dhg; eassumption.
    }
    assert (H_assumption_hg : fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg). {
      simpl.
      split; assumption.
    }
    apply H_valid_hg in H_assumption_hg as H_conclusion_hg.
    destruct H_conclusion_hg as [H_postcondition_hg H_sat_guar_hg].
    exists c_hg, st_hg, C_hg.
    repeat split; assumption.
  - rename c into c_dhg.
    rename st into st_dhg.
    rename c' into c_dhg'.
    rename st' into st_dhg'.
    rename c'' into c_dhg''.
    rename st'' into st_dhg''.
    specialize (IHC_dhg H_npia H_differ H_assumption_dhg c_hg H_remove_gvars H_valid_hg).
    destruct IHC_dhg as [c_hg' [st_hg' [C_hg [H_remove_gvars' [H_differ' [H_assumption_hg H_sat_guar_dhg]]]]]].
    assert (exists c_hg_m st_hg_m c_hg'' st_hg'',
        <<gvars>> st_hg_m ~ st_dhg' /\
        c_hg' / st_hg' -->* c_hg_m / st_hg_m /\
        <(gvars)> c_hg'' ~> c_dhg'' /\
        << gvars>> st_hg'' ~ st_dhg'' /\
        c_hg_m / st_hg_m --> c_hg'' / st_hg'' /\
        Forall (fun g => st_dhg' g = st_dhg'' g) gvars) as [c_hg_m [st_hg_m [c_hg'' [st_hg'' [H_differ_m [H_steps_m [H_remove_gvars'' [H_differ'' [H_step_hg H_eq_gvars]]]]]]]]]. {
      apply step_add_gvars with c_dhg'; try assumption.
      eapply fcomp_npia.
      - exact C_dhg.
      - assumption.
    }
    assert (exists (C_hg_m : fcomp c_hg st_hg c_hg_m st_hg_m), fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg_m) as [C_hg_m H_assumption_hg_m]. {
      eapply fcomp_app_steps; eassumption.
    }
    set (C_hg' := fcomp_cmp c_hg st_hg c_hg_m st_hg_m c_hg'' st_hg'' H_step_hg C_hg_m).
    exists c_hg'', st_hg'', C_hg'.
    assert (H_assumption_hg' : fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg'). {
      simpl.
      assumption.
    }
    apply H_valid_hg in H_assumption_hg' as H_conclusion_hg'.
    destruct H_conclusion_hg' as [H_sat_guar_hg' H_postcondition_hg'].
    simpl in H_sat_guar_hg'.
    destruct H_sat_guar_hg' as [H_guar_step_hg' H_sat_guar_hg_m].
    repeat split; try assumption.
    destruct H_guar_step_hg' as [H_st_hg_m_st_hg'' | H_guar_step_hg'].
    + subst.
      left.
      apply functional_extensionality.
      intros x.
      rewrite Forall_forall in H_eq_gvars.
      specialize (H_eq_gvars x).
      destruct (H_differ_m x); try (apply H_eq_gvars; assumption).
      destruct (H_differ'' x); try (apply H_eq_gvars; assumption).
      transitivity (st_hg'' x); auto.
    + right.
      rewrite Exists_exists in *.
      destruct H_guar_step_hg' as [[A c] [H_In_G [H_A_st_hg_m H_steps]]].
      exists (A, c).
      split; try assumption.
      unfold guar_havoc_gvars in H_G_havoc.
      rewrite Forall_forall in H_G_havoc.
      specialize (H_G_havoc (A, c) H_In_G).
      simpl in H_G_havoc.
      destruct H_G_havoc as [H_A_dhg H_c_havoc].
      split.
      * apply H_A_dhg with st_hg_m; try assumption.
        apply differ_symm.
        assumption.
      * apply H_c_havoc with st_hg_m st_hg''; assumption.
  - rename c into c_dhg.
    rename st into st_dhg.
    rename c' into c_dhg'.
    rename st' into st_dhg'.
    rename st'' into st_dhg''.
    destruct H_assumption_dhg as [H_rely_step_dhg H_assumption_dhg].
    specialize (IHC_dhg H_npia H_differ H_assumption_dhg c_hg H_remove_gvars H_valid_hg).
    destruct IHC_dhg as [c_hg' [st_hg' [C_hg [H_remove_gvars' [H_differ' [H_assumption_hg H_sat_guar_dhg]]]]]].
    destruct (H_R_hg st_hg' st_dhg'') as [st_hg'' [H_differ'' H_R_st_hg'_st_hg'']].
    set (C_hg' := fcomp_env c_hg st_hg c_hg' st_hg' st_hg'' C_hg).
    exists c_hg', st_hg'', C_hg'.
    repeat split; try assumption.
    + apply differ_symm.
      assumption.
    + rewrite Forall_forall.
      intros r H_In_R H_r_st_hg'.
      apply in_app_or in H_In_R as [H_In_R_dhg | H_In_R_hg].
      * rewrite Forall_forall in H_R_dhg.
        specialize (H_R_dhg r H_In_R_dhg).
        apply H_R_dhg with st_dhg''. {
          apply differ_symm.
          assumption.
        }
        rewrite Forall_forall in H_rely_step_dhg.
        specialize (H_rely_step_dhg r H_In_R_dhg).
        apply H_rely_step_dhg.
        apply H_R_dhg with st_hg'; try assumption.
        apply differ_symm.
        assumption.
      * rewrite Forall_forall in H_R_st_hg'_st_hg''.
        specialize (H_R_st_hg'_st_hg'' r H_In_R_hg).
        apply H_R_st_hg'_st_hg''.
        assumption.
Qed.

Theorem ghost_variable_rule
    gvars c_hg c_dhg P_dhg P_hg R_dhg R_hg G Q
    (H_npia : no_par_in_atomic c_dhg)
    (H_P_dhg : assertion_dhg gvars P_dhg)
    (H_P_restrict : assertion_doesnt_restrict gvars P_hg)
    (H_R_dhg : Forall (fun r => assertion_dhg gvars r) R_dhg)
    (H_R_restrict : rely_doesnt_restrict gvars R_hg)
    (H_G_havoc : guar_havoc_gvars gvars G)
    (H_Q_dhg : assertion_dhg gvars Q)
    (H_remove_gvars : <(gvars)> c_hg ~> c_dhg)
    (H_valid : |= c_hg sat ({{ P_dhg /\ P_hg }}, R_dhg ++ R_hg, G, Q)) :
      |= c_dhg sat (P_dhg, R_dhg, G, Q).
Proof.
  rewrite bvalid_iff_fvalid in *.
  intros st_dhg c_dhg' st_dhg' C_dhg H_assumption_dhg.
  destruct (H_P_restrict st_dhg) as [st_hg [H_differ H_precondition_hg]].
  assert (exists c_hg' st_hg' (C_hg : fcomp c_hg st_hg c_hg' st_hg'),
        <(gvars)> c_hg' ~> c_dhg' /\
        <<gvars>> st_hg' ~ st_dhg' /\
        fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg /\
        fcomp_sat_guar G C_dhg) as [c_hg' [st_hg' [C_hg [H_remove_gvars' [H_differ' [H_assumption_hg H_sat_guar_dhg]]]]]]. {
    apply fcomp_add_gvars with Q; try assumption.
    apply differ_symm.
    assumption.
  }
  split; try assumption.
  intros. subst.
  apply H_Q_dhg with st_hg'. {
    apply differ_symm.
    assumption.
  }
  apply remove_to_skip with (st := st_hg') in H_remove_gvars'.
  destruct H_remove_gvars' as [st_hg_m [H_differ_m H_steps]].
  apply H_Q_dhg with st_hg_m; try assumption.
  assert (exists (C_hg' : fcomp c_hg st_hg <{ skip }> st_hg_m), fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg') as [C_hg' H_assumption_hg']. {
    eapply fcomp_app_steps; eassumption.
  }
  apply H_valid in H_assumption_hg' as H_conclusion_hg'.
  destruct H_conclusion_hg' as [H_sat_guar_hg' H_postcondition_hg'].
  apply H_postcondition_hg'.
  reflexivity.
Qed.


Lemma havoc_com_havoc_gvars
    gvars c :
      com_havoc_gvars gvars <{ havoc gvars ; c ; havoc gvars }>.
Proof.
  intros st1 st1' st2 st2' H_differ H_differ' H_steps.
  invert H_steps.
  rename H into H_step.
  rename H0 into H_steps.
  invert H_step.
  rename st' into st3.
  rename H3 into H_step.
  invert H_step.
  rename H0 into H_differ3.
  invert H_steps.
  rename H into H_step.
  rename H0 into H_steps.
  invert H_step.
  1: invert H3.
  apply seq_multistep in H_steps.
  destruct H_steps. {
    destruct H as [c' [H_discriminate_me H_steps]].
    discriminate.
  }
  destruct H as [st3' [H_steps H_havoc_steps]].
  invert H_havoc_steps.
  rename H into H_step.
  rename H0 into H_skip_steps.
  invert H_step.
  invert H_skip_steps.
  2: invert H.
  rename H2 into H_differ3'.
  apply seq_multistep.
  right.
  exists st3.
  split. {
    apply multi_R.
    constructor.
    eapply differ_trans.
    - apply differ_symm.
      eassumption.
    - eassumption.
  }
  apply seq_multistep.
  right.
  exists st3'.
  split; try assumption.
  apply multi_R.
  constructor.
  eapply differ_trans; eassumption.
Qed.

Lemma havoc_com_havoc_semantics
    gvars c :
      c =>> <{ havoc gvars ; c ; havoc gvars }>.
Proof.
  intros st st' H_steps.
  apply seq_multistep.
  right.
  exists st.
  split. {
    apply multi_R.
    constructor.
    apply differ_refl.
  }
  apply seq_multistep.
  right.
  exists st'.
  split; try assumption.
  apply multi_R.
  constructor.
  apply differ_refl.
Qed.
