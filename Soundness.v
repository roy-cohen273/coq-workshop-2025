Set Warnings "-notation-overridden".
From Coq Require Import List. Import ListNotations.
From PLF Require Import Smallstep.
From PLF Require Import Hoare.
From PLF Require Import Semantics.


Reserved Notation "'|-' '{{' P '}}' c '{{' Q '}}'"
                  (at level 2,
                   P custom assn at level 99,
                   c custom com at level 99,
                   Q custom assn at level 99).
Inductive hoare_derivable : Assertion -> com -> Assertion -> Prop :=
  | H_Skip : forall P,
      |- {{ P }} skip {{ P }}
  | H_Asgn : forall Q V a,
      |- {{ Q [V |-> a] }} V := a {{ Q }}
  | H_Atomic : forall P c Q,
      |- {{ P }} c {{ Q }} ->
      |- {{ P }} atomic c end {{ Q }}
  | H_Seq : forall P c Q d R,
      |- {{ Q }} d {{ R }} ->
      |- {{ P }} c {{ Q }} ->
      |- {{ P }} c; d {{ R }}
  | H_If : forall P Q (b : bexp) c1 c2,
    |- {{ P /\ b }} c1 {{ Q }} ->
    |- {{ P /\ ~b }} c2 {{ Q }} ->
    |- {{ P }} if b then c1 else c2 end {{ Q }}
  | H_While : forall P (b : bexp) c,
    |- {{ P /\ b }} c {{ P }} ->
    |- {{ P }} while b do c end {{ P /\ ~b }}
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    |- {{ P' }} c {{ Q' }} ->
    P ->> P' ->
    Q' ->> Q ->
    |- {{ P }} c {{ Q }}
  
  where "'|-' '{{' P '}}' c '{{' Q '}}'" := (hoare_derivable P c Q).

Theorem hoare_sound
    P c Q
    (H_derivable : |- {{ P }} c {{ Q }}) :
      |= {{ P }} c {{ Q }}.
Admitted.


(* Specification derivability *)

(* Before we define derivability, we will need some helpers for the
   parallel composition rule (non interference) and the consequence
   rule (rely strengthening, guar weakening) *)

Definition non_interfering
    (R : list Assertion)
    (G : list (Assertion * com))
    : Prop :=
  Forall (fun P =>
    Forall (fun (g : Assertion * com) =>
      let (Q, c) := g in
      |- {{ P /\ Q }} c {{ P }}
    ) G
  ) R.

Definition stronger_rely
    (R R' : list Assertion)
    : Prop :=
  Forall (fun P' =>
    forall st st',
    P' st ->
    (Forall (fun P => P st -> P st') R) ->
    P' st'
  ) R'.

Definition bigstep_semantics_incl
    (c c' : com) : Prop :=
  forall st st',
    c / st -->* <{ skip }> / st' ->
    c' / st -->* <{ skip }> / st'.

Notation " c '=>>' c' " := (bigstep_semantics_incl c c')
    (at level 80).

Hint Unfold bigstep_semantics_incl : core.

Definition weaker_guar
    (G G' : list (Assertion * com))
    : Prop :=
  Forall (fun (g' : Assertion * com) =>
    let (Q', x') := g' in
    Exists (fun (g : Assertion * com) =>
      let (Q, x) := g in
      x' =>> x /\ Q' ->> Q
    ) G
  ) G'.

Reserved Notation "'|-' c 'sat' '(' P ',' R ',' G ',' Q ')'"
                  (at level 2,
                   c custom com at level 99,
                   P at level 99,
                   R at level 99,
                   G at level 99,
                   Q at level 99).
Inductive phoare_derivable : com -> Assertion -> list Assertion -> list (Assertion * com) -> Assertion -> Prop :=
  | PH_Consequence : forall c P P' R R' G G' Q Q',
      P ->> P' ->
      stronger_rely R R' ->
      weaker_guar G G' ->
      Q' ->> Q ->
      |- c sat (P', R', G', Q') ->
      |- c sat (P, R, G, Q)
  | PH_Skip : forall P,
      |- skip sat (P, [P], [], P)
  | PH_Assgn : forall P Q x a,
      P ->> {{ Q [x |-> a] }} ->
      |- x := a sat (P, [P; Q], [(P, <{ x := a }>)], Q)
  | PH_Atomic : forall P Q c,
      |- {{ P }} c {{ Q }} ->
      |- atomic c end sat (P, [P; Q], [(P, c)], Q)
  | PH_Seq : forall (c1 c2 : com) P Q M R1 R2 G1 G2,
      |- c1 sat (P, R1, G1, M) ->
      |- c2 sat (M, R2, G2, Q) ->
      |- c1 ; c2 sat (P, R1 ++ R2, G1 ++ G2, Q)
  | PH_If : forall (b : bexp) (c1 c2 : com) P Q R1 R2 G1 G2,
      |- c1 sat ({{ P /\ b }}, R1, G1, Q) ->
      |- c2 sat ({{ P /\ ~b }}, R2, G2, Q) ->
      |- if b then c1 else c2 end sat (P, [P] ++ R1 ++ R2, G1 ++ G2, Q)
  | PH_While : forall (b : bexp) (c : com) P R G Q,
      {{ P /\ ~b }} ->> Q ->
      |- c sat ({{ P /\ b }}, R, G, P) ->
      |- while b do c end sat (P, [P; Q] ++ R, G, Q)
  | PH_Par : forall c1 c2 P P1 P2 R1 R2 G1 G2 Q Q1 Q2,
      |- c1 sat (P1, R1, G1, Q1) ->
      |- c2 sat (P2, R2, G2, Q2) ->
      P ->> {{ P1 /\ P2 }} ->
      {{ Q1 /\ Q2 }} ->> Q ->
      non_interfering R1 G2 ->
      non_interfering R2 G1 ->
      |- c1 || c2 sat (P, (Q :: R1 ++ R2), G1 ++ G2, Q)

  where "'|-' c 'sat' '(' P ',' R ',' G ',' Q ')'" := (phoare_derivable c P R G Q).


(* The proof for the consequence rule is split into 4 part:
   * precondition strengthening
   * rely strengthening
   * guar weakening
   * postcondition weakening *)

Lemma phoare_precondition_strengthening
    c P P' R G Q
    (H_P_P' : P ->> P')
    (H_valid : |= c sat (P', R, G, Q)) :
      |= c sat (P, R, G, Q).
Proof.
  unfold phoare_valid.
  intros st c' st' C [H_precondition H_sat_rely].
  apply H_valid.
  split; try assumption.
  auto.
Qed.

Lemma rely_strengthening
    c st c' st' R R' (C : bcomp c st c' st')
    (H_stronger_rely : stronger_rely R R')
    (H_sat_rely : bcomp_sat_rely R C) :
      bcomp_sat_rely R' C.
Proof.
  induction C; simpl in *; try auto.
  destruct H_sat_rely as [H_rely_step H_sat_rely].
  split; try auto.
  unfold stronger_rely in H_stronger_rely.
  eapply Forall_impl.
  2: exact H_stronger_rely.
  simpl.
  intros P H H_P_st.
  apply H with st; assumption.
Qed.

Lemma phoare_rely_strengthening
    c P R R' G Q
    (H_stronger_rely : stronger_rely R R')
    (H_valid : |= c sat (P, R', G, Q)) :
      |= c sat (P, R, G, Q).
Proof.
  unfold phoare_valid.
  intros st c' st' C [H_precondition H_sat_rely].
  apply H_valid.
  split; try assumption.
  apply rely_strengthening with R; assumption.  
Qed.

Lemma guar_weakening
    c st c' st' G G' Q (C : bcomp c st c' st')
    (H_weaker_guar : weaker_guar G G')
    (H_conclusion : bcomp_conclusion Q G' C) :
      bcomp_conclusion Q G C.
Proof.
  induction C; simpl in *; try auto.
  destruct H_conclusion as [H_guar_step H_conclusion].
  split; try auto.
  destruct H_guar_step as [H_st_st' | H_guar_step]; try (left; assumption).
  right.
  clear Q c c' c'' st'' H_step C H_conclusion IHC.
  unfold weaker_guar in H_weaker_guar.
  rewrite Exists_exists in *.
  destruct H_guar_step as [[Q' c'] [H_In_G' [H_Q_st H_step]]].
  rewrite Forall_forall in H_weaker_guar.
  apply H_weaker_guar in H_In_G' as H.
  rewrite Exists_exists in H.
  destruct H as [[Q c] [H_In_G [H_c'_c H_Q'_Q]]].
  exists (Q, c).
  repeat split; auto.
Qed.

Lemma phoare_guar_weakening
    c P R G G' Q
    (H_weaker_guar : weaker_guar G G')
    (H_valid : |= c sat (P, R, G', Q)) :
      |= c sat (P, R, G, Q).
Proof.
  unfold phoare_valid.
  intros st c'' st' C H_assumption.
  apply guar_weakening with G'; try assumption.
  apply H_valid.
  assumption.
Qed.

Lemma postcondition_weakening
    c st c' st' G Q Q' (C : bcomp c st c' st')
    (H_Q'_Q : Q' ->> Q)
    (H_conclusion : bcomp_conclusion Q' G C) :
      bcomp_conclusion Q G C.
Proof.
  induction C; simpl in *; try auto.
  destruct H_conclusion as [H_guar_step H_conclusion].
  auto.
Qed.

Lemma phoare_postcondition_weakening
    c P R G Q Q'
    (H_Q'_Q : Q' ->> Q)
    (H_valid : |= c sat (P, R, G, Q')) :
      |= c sat (P, R, G, Q).
Proof.
  unfold phoare_valid.
  intros st c' st' C H_assumption.
  apply postcondition_weakening with Q'; try assumption.
  apply H_valid.
  assumption.
Qed.

Lemma phoare_consequence
    c P P' R R' G G' Q Q'
    (H_P_P' : P ->> P')
    (H_stronger_rely : stronger_rely R R')
    (H_weaker_guar : weaker_guar G G')
    (H_Q'_Q : Q' ->> Q)
    (H_valid : |= c sat (P', R', G', Q')) :
      |= c sat (P, R, G, Q).
Proof.
  eapply phoare_precondition_strengthening; try eassumption.
  eapply phoare_rely_strengthening; try eassumption.
  eapply phoare_guar_weakening; try eassumption.
  eapply phoare_postcondition_weakening; try eassumption.
Qed.

(* While we're on the topic of rely strengthening / guar weakening,
   let's prove their relationship with incl. *)

Lemma incl_weaker_rely
    R R'
    (H_R'_R : incl R' R) :
      stronger_rely R R'.
Proof.
  unfold stronger_rely.
  rewrite Forall_forall.
  intros P H_In_R' st st' H_P_st H_rely_step.
  rewrite Forall_forall in H_rely_step.
  apply H_rely_step; try assumption.
  apply H_R'_R.
  assumption.
Qed.

Lemma incl_stronger_guar
    G G'
    (H_G'_G : incl G' G) :
      weaker_guar G G'.
Proof.
  unfold weaker_guar.
  rewrite Forall_forall.
  intros [Q' c'] H_In_G'.
  rewrite Exists_exists.
  exists (Q', c').
  repeat split; auto.
Qed.


Lemma phoare_skip
    P :
      |= skip sat (P, [P], [], P).
Proof.
  unfold phoare_valid.
  intros st c' st' C [H_precondition H_sat_rely].
  remember <{ skip }> as c.
  induction C; subst; simpl in *.
  - auto.
  - invert H_step.
  - destruct H_sat_rely as [H_rely_step H_sat_rely].
    apply IHC; try reflexivity.
    + invert H_rely_step.
      auto.
    + assumption.
Qed.

Lemma phoare_assgn
    P Q x a
    (H_P_Q : P ->> {{ Q [x |-> a] }}) :
      |= x := a sat (P, [P; Q], [(P, <{ x := a }>)], Q).
Proof.
  unfold phoare_valid.
  intros st c' st' C [H_precondition H_sat_rely].
  remember <{ x := a }> as c.
  induction C; subst; simpl in *.
  - discriminate.
  - invert H_step.
    clear IHC.
    split.
    + right.
      constructor.
      split; try assumption.
      econstructor.
      2: apply multi_refl.
      constructor.
    + apply guar_weakening with []. {
        apply incl_stronger_guar.
        apply incl_nil_l.
      }
      apply phoare_skip.
      split.
      * apply H_P_Q.
        assumption.
      * apply rely_strengthening with [P; Q]. {
          apply incl_weaker_rely.
          unfold incl.
          simpl.
          auto.
        }
        assumption.
  - destruct H_sat_rely as [H_rely_step H_sat_rely].
    apply IHC; try reflexivity; try assumption.
    invert H_rely_step.
    auto.
Qed.

Lemma phoare_atomic
    c0 P Q
    (H_derivable : |- {{ P }} c0 {{ Q }}) :
      |= atomic c0 end sat (P, [P; Q], [(P, c0)], Q).
Proof.
  unfold phoare_valid.
  intros st c' st' C [H_precondition H_sat_rely].
  remember <{ atomic c0 end }> as c.
  induction C; subst; simpl in *.
  - discriminate.
  - invert H_step.
    clear IHC.
    split.
    + right.
      constructor.
      split; assumption.
    + apply guar_weakening with []. {
        apply incl_stronger_guar.
        apply incl_nil_l.
      }
      apply phoare_skip.
      split.
      * apply hoare_sound in H_derivable as H_valid.
        apply H_valid with st; assumption.
      * apply rely_strengthening with [P; Q]. {
          apply incl_weaker_rely.
          unfold incl.
          simpl.
          auto.
        }
        assumption.
  - destruct H_sat_rely as [H_rely_step H_sat_rely].
    apply IHC; try reflexivity; try assumption.
    invert H_rely_step.
    auto.
Qed.

(* Soundness for sequencial composition *)

Lemma seq_lemma
    (c1 c2 : com) st (c' : com) st'
    P M Q R R1 R2 G G1 G2
    (C : fcomp <{ c1 ; c2 }> st c' st')
    (H_c1_valid : f|= c1 sat (P, R1, G1, M))
    (H_c2_valid : f|= c2 sat (M, R2, G2, Q))
    (H_R1_R : incl R1 R)
    (H_R2_R : incl R2 R)
    (H_G1_G : incl G1 G)
    (H_G2_G : incl G2 G)
    (H_assumption : fcomp_assumption P R C) :
      (
        exists (c1' : com) (C1 : fcomp c1 st c1' st'),
        c' = <{ c1' ; c2 }> /\
        fcomp_assumption P R1 C1 /\
        fcomp_conclusion Q G C
      ) \/
      (
        exists st'0 (C1 : fcomp c1 st <{ skip }> st'0),
        exists c2' (C2 : fcomp c2 st'0 c2' st'),
        c' = c2' /\
        fcomp_assumption P R1 C1 /\
        fcomp_assumption M R2 C2 /\
        fcomp_conclusion Q G C
      ).
Proof.
  unfold fcomp_conclusion.
  remember <{ c1 ; c2 }> as c.
  induction C; subst; simpl in *.
  - left.
    exists c1.
    exists (fcomp_empty c1 st).
    simpl.
    repeat split.
    + assumption.
    + discriminate.
  - specialize (IHC eq_refl H_assumption).
    destruct IHC as [IHC | IHC].
    + destruct IHC as [c1' [C1 [H_eq_c' [H_assumption1 [H_sat_guar H_postcondition]]]]].
      subst.
      clear H_postcondition.
      invert H_step.
      * rename c1'0 into c1''.
        rename H0 into H_step.
        left.
        exists c1''.
        remember (fcomp_cmp c1 st c1' st' c1'' st'' H_step C1) as C1'.
        exists C1'.
        split; try reflexivity.
        split; try (rewrite HeqC1'; assumption).
        assert (fcomp_assumption P R1 C1') as H_assumption1'. {
          rewrite HeqC1'.
          simpl.
          assumption.
        }
        apply H_c1_valid in H_assumption1' as H_conclusion1'.
        rewrite HeqC1' in H_conclusion1'.
        destruct H_conclusion1' as [H_sat_guar1' H_postcondition1'].
        simpl in H_sat_guar1'.
        destruct H_sat_guar1' as [H_guar_step1 H_sat_guar1].
        repeat split.
        -- destruct H_guar_step1; try (left; assumption).
           right.
           apply incl_Exists with G1; assumption.
        -- assumption.
        -- discriminate.
      * right.
        exists st''.
        exists C1.
        exists c''.
        exists (fcomp_empty c'' st'').
        simpl.
        split; try reflexivity.
        split; try assumption.
        apply H_c1_valid in H_assumption1 as [H_sat_guar1 H_postcondition1].
        specialize (H_postcondition1 eq_refl).
        split; try assumption.
        repeat split; try (left; reflexivity); try assumption.
        intros; subst.
        assert (fcomp_assumption M R2 (fcomp_empty <{ skip }> st'')) as H_assumption2. {
          simpl.
          assumption.
        }
        apply H_c2_valid in H_assumption2 as [H_sat_guar2 H_postcondition2].
        auto.
    + destruct IHC as [st'0 [C1 [c2' [C2 [H_c'_c2' [H_assumption1 [H_assumption2 [H_sat_guar H_postcondition]]]]]]]].
      subst.
      right.
      exists st'0.
      exists C1.
      exists c''.
      remember (fcomp_cmp c2 st'0 c2' st' c'' st'' H_step C2) as C2'.
      exists C2'.
      split; try reflexivity.
      split; try assumption.
      assert (fcomp_assumption M R2 C2') as H_assumption2'. {
        rewrite HeqC2'.
        simpl.
        assumption.
      }
      split; try assumption.
      apply H_c2_valid in H_assumption2' as [H_sat_guar2' H_postcondition2].
      rewrite HeqC2' in H_sat_guar2'.
      simpl in H_sat_guar2'.
      destruct H_sat_guar2' as [H_guar_step H_sat_guar2].
      repeat split; try assumption.
      destruct H_guar_step as [H_st'_st'' | H_guar_step]; try (left; assumption).
      right.
      apply incl_Exists with G2; assumption.
  - destruct H_assumption as [H_rely_step H_assumption].
    specialize (IHC eq_refl H_assumption).
    destruct IHC as [IHC | IHC].
    + destruct IHC as [c1' [C1 [H_eq_c' [H_assumption1 [H_sat_guar H_postcondition]]]]].
      subst.
      clear H_postcondition.
      left.
      exists c1'.
      remember (fcomp_env c1 st c1' st' st'' C1) as C1'.
      exists C1'.
      repeat split; try reflexivity; try assumption; try discriminate.
      rewrite HeqC1'.
      simpl.
      split; try assumption.
      apply incl_Forall with R; assumption.
    + destruct IHC as [st'0 [C1 [c2' [C2 [H_c'_c2' [H_assumption1 [H_assumption2 [H_sat_guar H_postcondition]]]]]]]].
      subst.
      right.
      exists st'0.
      exists C1.
      exists c2'.
      remember (fcomp_env c2 st'0 c2' st' st'' C2) as C2'.
      exists C2'.
      split; try reflexivity.
      split; try assumption.
      assert (fcomp_assumption M R2 C2') as H_assumption2'. {
        rewrite HeqC2'.
        simpl.
        split; try assumption.
        apply incl_Forall with R; assumption.
      }
      repeat split; try assumption.
      apply H_c2_valid in H_assumption2' as [H_sat_guar2' H_postcondition2].
      assumption.
Qed.

Lemma phoare_seq
    (c1 c2 : com) P Q M R1 R2 G1 G2
    (H_c1_valid : |= c1 sat (P, R1, G1, M))
    (H_c2_valid : |= c2 sat (M, R2, G2, Q)) :
      |= c1 ; c2 sat (P, R1 ++ R2, G1 ++ G2, Q).
Proof.
  rewrite bvalid_iff_fvalid in *.
  unfold phoare_valid_forward.
  intros st c' st' C H_assumption.
  set (lemma := seq_lemma).
  specialize (lemma c1 c2 st c' st' P M Q (R1 ++ R2) R1 R2 (G1 ++ G2) G1 G2 C H_c1_valid H_c2_valid).
  assert (incl R1 (R1 ++ R2)) as H_R1_R by (apply incl_appl; apply incl_refl).
  specialize (lemma H_R1_R).
  assert (incl R2 (R1 ++ R2)) as H_R2_R by (apply incl_appr; apply incl_refl).
  specialize (lemma H_R2_R).
  assert (incl G1 (G1 ++ G2)) as H_G1_G by (apply incl_appl; apply incl_refl).
  specialize (lemma H_G1_G).
  assert (incl G2 (G1 ++ G2)) as H_G2_G by (apply incl_appr; apply incl_refl).
  specialize (lemma H_G2_G H_assumption).
  destruct lemma.
  - destruct H as [_ [_ [_ [_]]]].
    assumption.
  - destruct H as [_ [_ [_ [_ [_ [_ [_]]]]]]].
    assumption.
Qed.

Lemma phoare_if
    (b : bexp) (c1 c2 : com) P Q R1 R2 G1 G2
    (H_c1_valid : |= c1 sat ({{ P /\ b }}, R1, G1, Q))
    (H_c2_valid : |= c2 sat ({{ P /\ ~b }}, R2, G2, Q)) :
      |= if b then c1 else c2 end sat (P, [P] ++ R1 ++ R2, G1 ++ G2, Q).
Proof.
  unfold phoare_valid.
  intros st c' st' C [H_precondition H_sat_rely].
  remember <{ if b then c1 else c2 end }> as c.
  induction C; subst; simpl in *.
  - discriminate.
  - invert H_step.
    + split; try (left; reflexivity).
      apply guar_weakening with G1. {
        apply incl_stronger_guar.
        apply incl_appl.
        apply incl_refl.
      }
      apply H_c1_valid.
      repeat split; try assumption.
      apply rely_strengthening with (P :: R1 ++ R2). {
        apply incl_weaker_rely.
        apply incl_tl.
        apply incl_appl.
        apply incl_refl.
      }
      assumption.
    + split; try (left; reflexivity).
      apply guar_weakening with G2. {
        apply incl_stronger_guar.
        apply incl_appr.
        apply incl_refl.
      }
      apply H_c2_valid.
      repeat split; try rewrite Bool.not_true_iff_false; try assumption.
      apply rely_strengthening with (P :: R1 ++ R2). {
        apply incl_weaker_rely.
        apply incl_tl.
        apply incl_appr.
        apply incl_refl.
      }
      assumption.
  - destruct H_sat_rely as [H_rely_step H_sat_rely].
    invert H_rely_step.
    apply IHC; try auto.
Qed.

Lemma while_lemma
    (b : bexp) (c0 : com) st c' st' P R R' G Q
    (C : fcomp <{ while b do c0 end }> st c' st')
    (H_valid : f|= c0 sat ({{ P /\ b }}, R', G, P))
    (H_P_b_Q : {{ P /\ ~b }} ->> Q)
    (H_R'_R : incl R' R)
    (H_P_R : In P R)
    (H_Q_R : In Q R)
    (H_assumption : fcomp_assumption P R C) :
      (
        c' = <{ while b do c0 end }> /\
        P st' /\
        fcomp_conclusion Q G C
      ) \/
      (
        c' = <{ if b then c0 ; while b do c0 end else skip end }> /\
        P st' /\
        fcomp_conclusion Q G C
      ) \/
      (
        c' = <{ skip }> /\
        fcomp_conclusion Q G C
      ) \/
      (
        exists st0 (c1 : com) (C' : fcomp c0 st0 c1 st'),
          c' = <{ c1 ; while b do c0 end }> /\
          P st0 /\
          fcomp_assumption ({{ P /\ b }}) R' C' /\
          fcomp_conclusion Q G C
      ).
Proof.
  unfold fcomp_conclusion.
  remember <{ while b do c0 end }> as c.
  induction C; subst; simpl in *.
  - left.
    repeat split.
    + assumption.
    + discriminate.
  - specialize (IHC eq_refl H_assumption).
    destruct IHC as [[H_eq_c' [H_P_st' [H_sat_guar H_postcondition]]] |
                    [[H_eq_c' [H_P_st' [H_sat_guar H_postcondition]]] |
                    [[H_eq_c' [H_sat_guar H_postcondition]] |
                     [st0 [c1 [C' [H_eq_c' [H_P_st0 [H_assumption' [H_sat_guar H_postcondition]]]]]]]]]].
    + subst.
      invert H_step.
      clear H_postcondition.
      right.
      left.
      repeat split; try assumption.
      * left.
        reflexivity.
      * discriminate.
    + subst.
      clear H_postcondition.
      invert H_step.
      * right.
        right.
        right.
        exists st''.
        exists c0.
        exists (fcomp_empty c0 st'').
        simpl.
        repeat split; try reflexivity; try assumption.
        -- left.
           reflexivity.
        -- discriminate.
      * right.
        right.
        left.
        split; try reflexivity.
        repeat split.
        -- left.
           reflexivity.
        -- assumption.
        -- intros _.
           apply H_P_b_Q.
           split; try assumption.
           rewrite Bool.not_true_iff_false.
           assumption.
    + subst.
      invert H_step.
    + subst.
      clear H_postcondition.
      invert H_step.
      * rename H0 into H_step.
        right.
        right.
        right.
        exists st0.
        exists c1'.
        remember (fcomp_cmp c0 st0 c1 st' c1' st'' H_step C') as C''.
        exists C''.
        split; try reflexivity.
        split; try assumption.
        assert (fcomp_assumption ({{ P /\ b }}) R' C'') as H_assumption''. {
          rewrite HeqC''.
          simpl.
          assumption.
        }
        split; try assumption.
        apply H_valid in H_assumption'' as H_conclusion''.
        subst.
        unfold fcomp_conclusion in H_conclusion''.
        destruct H_conclusion'' as [H_sat_guar' H_postcondition'].
        simpl in H_sat_guar'.
        destruct H_sat_guar' as [H_guar_step H_sat_guar'].
        repeat split; try assumption.
        discriminate.
      * left.
        split; try reflexivity.
        repeat split; try assumption.
        -- apply H_valid in H_assumption' as [H_sat_guar' H_postcondition'].
           apply H_postcondition'.
           reflexivity.
        -- left.
           reflexivity.
        -- discriminate.
  - destruct H_assumption as [H_rely_step H_assumption].
    specialize (IHC eq_refl H_assumption).
    rewrite Forall_forall in H_rely_step.
    assert (P st' -> P st'') as H_P_st'_st''. {
      apply H_rely_step.
      assumption.
    }
    assert (Q st' -> Q st'') as H_Q_st'_st''. {
      apply H_rely_step.
      assumption.
    }
    destruct IHC as [[H_eq_c' [H_P_st' [H_sat_guar H_postcondition]]] |
                    [[H_eq_c' [H_P_st' [H_sat_guar H_postcondition]]] |
                    [[H_eq_c' [H_sat_guar H_postcondition]] |
                     [st0 [c1 [C' [H_eq_c' [H_P_st0 [H_assumption' [H_sat_guar H_postcondition]]]]]]]]]].
    + left.
      subst.
      repeat split; auto.
    + right.
      left.
      subst.
      repeat split; auto.
    + right.
      right.
      left.
      subst.
      repeat split; auto.
    + right.
      right.
      right.
      subst.
      exists st0.
      exists c1.
      exists (fcomp_env c0 st0 c1 st' st'' C').
      simpl.
      repeat split; try reflexivity; try assumption.
      * apply incl_Forall with R; try assumption.
        rewrite Forall_forall.
        assumption.
      * discriminate.
Qed.

Lemma phoare_while
    (b : bexp) (c : com) P R G Q
    (H_P_b_Q : {{ P /\ ~b }} ->> Q)
    (H_valid : |= c sat ({{ P /\ b }}, R, G, P)) :
      |= while b do c end sat (P, [P; Q] ++ R, G, Q).
Proof.
  rewrite bvalid_iff_fvalid in *.
  unfold phoare_valid_forward.
  intros st c' st' C H_assumption.
  set (lemma := while_lemma).
  specialize (lemma b c st c' st' P ([P; Q] ++ R) R G Q C H_valid H_P_b_Q).
  assert (incl R ([P; Q] ++ R)) as H_R'_R by (apply incl_appr; apply incl_refl).
  specialize (lemma H_R'_R).
  assert (In P ([P; Q] ++ R)) as H_P_R. {
    apply in_or_app.
    simpl.
    auto.
  }
  specialize (lemma H_P_R).
  assert (In Q ([P; Q] ++ R)) as H_Q_R. {
    apply in_or_app.
    simpl.
    auto.
  }
  specialize (lemma H_Q_R H_assumption).
  destruct lemma as [[_ [_ H_conclusion]] |
                    [[_ [_ H_conclusion]] |
                    [[_ H_conclusion] |
                     [_ [_ [_ [_ [_ [_ H_conclusion]]]]]]]]];
  assumption.
Qed.

(* Soundness for parallel composition. *)
(* We will use "forwards" computations. *)
Lemma par_lemma
    c1 c2 P P1 P2 R R1 R2 G G1 G2 Q Q1 Q2
    (H_c1_valid : f|= c1 sat (P1, R1, G1, Q1))
    (H_c2_valid : f|= c2 sat (P2, R2, G2, Q2))
    (H_P_P1_P2 : P ->> {{ P1 /\ P2 }})
    (H_Q1_Q2_Q : {{ Q1 /\ Q2 }} ->> Q)
    (H_non_interfering1 : non_interfering R1 G2)
    (H_non_interfering2 : non_interfering R2 G1)
    (H_Q_R : In Q R)
    (H_R1_R : incl R1 R)
    (H_R2_R : incl R2 R)
    (H_G1_G : incl G1 G)
    (H_G2_G : incl G2 G)
    st c' st' (C : fcomp <{ c1 || c2 }> st c' st')
    (H_assumption : fcomp_assumption P R C) :
      exists c1' (C1 : fcomp c1 st c1' st'),
      exists c2' (C2 : fcomp c2 st c2' st'),
        (c' = <{ c1' || c2' }> \/ (c' = <{ skip }> /\ c1' = <{ skip }> /\ c2' = <{ skip }>)) /\
        fcomp_assumption P1 R1 C1 /\
        fcomp_assumption P2 R2 C2 /\
        fcomp_conclusion Q G C.
Proof.
  unfold fcomp_conclusion.
  remember <{ c1 || c2 }> as c.
  induction C; intros; subst; simpl in *.
  - exists c1.
    exists (fcomp_empty c1 st).
    exists c2.
    exists (fcomp_empty c2 st).
    repeat split.
    + left. reflexivity.
    + simpl.
      apply proj1 with (P2 st).
      auto.
    + simpl.
      apply proj2 with (P1 st).
      auto.
    + discriminate.
  - specialize (IHC eq_refl H_assumption).
    destruct IHC as [c1' [C1 [c2' [C2 [H_eq_c' [H_assumption1 [H_assumption2 [H_sat_guar H_postcondition]]]]]]]].
    destruct H_eq_c' as [H_eq_c' | [H_eq_c' [H_eq_c1' H_eq_c2']]]; subst.
    + clear H_postcondition.
      invert H_step.
      * rename c1'0 into c1''.
        exists c1''.
        remember (fcomp_cmp c1 st c1' st' c1'' st'' H0 C1) as C1'.
        exists C1'.
        exists c2'.
        remember (fcomp_env c2 st c2' st' st'' C2) as C2'.
        exists C2'.
        split; try (left; reflexivity).
        assert (fcomp_assumption P1 R1 C1') as H_assumption1'. {
          rewrite HeqC1'.
          simpl.
          assumption.
        }
        split; try assumption.
        apply H_c1_valid in H_assumption1' as H_conclusion1'.
        rewrite HeqC1' in H_conclusion1'.
        destruct H_conclusion1' as [H_sat_guar1' H_postcondition1].
        simpl in H_sat_guar1'.
        destruct H_sat_guar1' as [H_guar_step H_sat_guar1].
        assert (Forall (fun P0 : state -> Prop => P0 st' -> P0 st'') R2) as H_rely_step. {
          destruct H_guar_step as [H_st'_st'' | H_guar_step].
          - subst.
            rewrite Forall_forall.
            auto.
          - set (H := H_non_interfering2).
            unfold non_interfering in H.
            rewrite Exists_exists in H_guar_step.
            destruct H_guar_step as [[A x] [H_In_G1 [H_A_st' H_step]]].
            rewrite Forall_forall.
            intros p H_In_R2 H_p_st'.
            rewrite Forall_forall in H.
            specialize (H p H_In_R2).
            rewrite Forall_forall in H.
            specialize (H (A, x) H_In_G1).
            simpl in H.
            apply hoare_sound in H.
            unfold hoare_valid in H.
            apply H with st'; auto.
        }
        repeat split.
        -- rewrite HeqC2'.
           simpl.
           split; assumption.
        -- destruct H_guar_step as [H_st'_st'' | H_guar_step]; try (left; assumption).
           right.
           apply incl_Exists with G1; assumption.
        -- assumption.
        -- discriminate.
      * (* symmetric case to the first case above *)
        rename c2'0 into c2''.
        exists c1'.
        remember (fcomp_env c1 st c1' st' st'' C1) as C1'.
        exists C1'.
        exists c2''.
        remember (fcomp_cmp c2 st c2' st' c2'' st'' H0 C2) as C2'.
        exists C2'.
        split; try (left; reflexivity).
        assert (fcomp_assumption P2 R2 C2') as H_assumption2'. {
          rewrite HeqC2'.
          simpl.
          assumption.
        }
        apply H_c2_valid in H_assumption2' as H_conclusion2'.
        rewrite HeqC2' in H_conclusion2'.
        destruct H_conclusion2' as [H_sat_guar2' H_postcondition2].
        simpl in H_sat_guar2'.
        destruct H_sat_guar2' as [H_guar_step H_sat_guar2].
        assert (Forall (fun P0 : state -> Prop => P0 st' -> P0 st'') R1) as H_rely_step. {
          destruct H_guar_step as [H_st'_st'' | H_guar_step].
          - subst.
            rewrite Forall_forall.
            auto.
          - set (H := H_non_interfering1).
            unfold non_interfering in H.
            rewrite Exists_exists in H_guar_step.
            destruct H_guar_step as [[A x] [H_In_G2 [H_Q_st' H_step]]].
            rewrite Forall_forall.
            intros p H_In_R1 H_p_st'.
            rewrite Forall_forall in H.
            specialize (H p H_In_R1).
            rewrite Forall_forall in H.
            specialize (H (A, x) H_In_G2).
            simpl in H.
            apply hoare_sound in H.
            unfold hoare_valid in H.
            apply H with st'; auto.
        }
        repeat split.
        -- rewrite HeqC1'.
           simpl.
           split; assumption.
        -- rewrite HeqC2'.
           simpl.
           assumption.
        -- destruct H_guar_step as [H_st'_st'' | H_guar_step]; try (left; assumption).
           right.
           apply incl_Exists with G2; assumption.
        -- assumption.
        -- discriminate.
      * exists <{ skip }>.
        exists C1.
        exists <{ skip }>.
        exists C2.
        repeat split; try assumption.
        -- right.
           repeat split; reflexivity.
        -- left.
           reflexivity.
        -- intros _.
           apply H_Q1_Q2_Q.
           split.
           ++ apply H_c1_valid in H_assumption1 as [H_sat_guar1 H_postcondition1].
              auto.
           ++ apply H_c2_valid in H_assumption2 as [H_sat_guar2 H_postdoncition2].
              auto.
    + invert H_step.
  - destruct H_assumption as [H_rely_step H_assumption].
    specialize (IHC eq_refl H_assumption).
    destruct IHC as [c1' [C1 [c2' [C2 [H_eq_c' [H_assumption1 [H_assumption2 [H_sat_guar H_postcindition]]]]]]]].
    exists c1'.
    remember (fcomp_env c1 st c1' st' st'' C1) as C1'.
    exists C1'.
    exists c2'.
    remember (fcomp_env c2 st c2' st' st'' C2) as C2'.
    exists C2'.
    repeat split; try assumption.
    + rewrite HeqC1'.
      simpl.
      split; try assumption.
      apply incl_Forall with R; assumption.
    + rewrite HeqC2'.
      simpl.
      split; try assumption.
      apply incl_Forall with R; assumption.
    + intros; subst.
      destruct H_eq_c' as [H_discriminate | [_ [H_eq_c1' H_eq_c2']]]; try discriminate.
      subst.
      rewrite Forall_forall in H_rely_step.
      apply H_rely_step; auto.
Qed.

Lemma phoare_par
    c1 c2 P P1 P2 R1 R2 G1 G2 Q Q1 Q2
    (H_c1_valid : |= c1 sat (P1, R1, G1, Q1))
    (H_c2_valid : |= c2 sat (P2, R2, G2, Q2))
    (H_P_P1_P2 : P ->> {{ P1 /\ P2 }})
    (H_Q1_Q2_Q : {{ Q1 /\ Q2 }} ->> Q)
    (H_non_interfering1 : non_interfering R1 G2)
    (H_non_interfering2 : non_interfering R2 G1) :
      |= c1 || c2 sat (P, (Q :: R1 ++ R2), G1 ++ G2, Q).
Proof.
  rewrite bvalid_iff_fvalid in *.
  unfold phoare_valid_forward.
  intros st c' st' C H_assumption.
  set (lemma := par_lemma).
  specialize (lemma c1 c2 P P1 P2 (Q :: R1 ++ R2) R1 R2 (G1 ++ G2) G1 G2 Q Q1 Q2 H_c1_valid H_c2_valid H_P_P1_P2 H_Q1_Q2_Q H_non_interfering1 H_non_interfering2).
  assert (In Q (Q :: R1 ++ R2)) as H_Q_R. {
    apply in_eq.
  }
  specialize (lemma H_Q_R).
  assert (incl R1 (Q :: R1 ++ R2)) as H_R1_R. {
    apply incl_tl.
    apply incl_appl.
    apply incl_refl.
  }
  specialize (lemma H_R1_R).
  assert (incl R2 (Q :: R1 ++ R2)) as H_R2_R. {
    apply incl_tl.
    apply incl_appr.
    apply incl_refl.
  }
  specialize (lemma H_R2_R).
  assert (incl G1 (G1 ++ G2)) as H_G1_G. {
    apply incl_appl.
    apply incl_refl.
  }
  specialize (lemma H_G1_G).
  assert (incl G2 (G1 ++ G2)) as H_G2_G. {
    apply incl_appr.
    apply incl_refl.
  }
  specialize (lemma H_G2_G).
  specialize (lemma st c' st' C H_assumption).
  destruct lemma as [c1' [C1 [c2' [C2 [_ [_ [_ H_conclusion]]]]]]].
  assumption.
Qed.


Theorem phoare_sound
    c P R G Q
    (H_derivable : |- c sat (P, R, G, Q)) :
      |= c sat (P, R, G, Q).
Proof.
  induction H_derivable.
  - apply phoare_consequence with (P' := P') (R' := R') (G' := G') (Q' := Q');
    assumption.
  - apply phoare_skip.
  - apply phoare_assgn;
    assumption.
  - apply phoare_atomic;
    assumption.
  - apply phoare_seq with (M := M);
    assumption.
  - apply phoare_if;
    assumption.
  - apply phoare_while;
    assumption.
  - apply phoare_par with (P1 := P1) (P2 := P2) (Q1 := Q1) (Q2 := Q2);
    assumption.
Qed.
