Set Warnings "-notation-overridden".
From Coq Require Import List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Hoare.
From PLF Require Import Semantics.
From PLF Require Import Soundness.
From PLF Require Import GhostVar.

(* dcom represents a part of a decorated command.
   Specifically, it represents a command and its precondition. *)
Inductive dcom : Type :=
  | DCSkip (P : Assertion)
    (* {{ P }} skip *)
  | DCAsgn (P : Assertion) (X : string) (a : aexp)
    (* {{ P }} X := a *)
  | DCAtomic (P : Assertion) (d : dcom) (Q : Assertion)
    (* {{ P }} atomic d {{ Q }} end *)
  | DCSeq (d1 d2 : dcom)
    (* d1 ; d2 *)
  | DCIf (P : Assertion) (b : bexp) (d1 : dcom) (Q1 : Assertion) (d2 : dcom) (Q2 : Assertion)
    (* {{ P }} if b then d1 {{ Q1 }} else d2 {{ Q2 }} *)
  | DCWhile (P : Assertion) (b : bexp) (d : dcom) (Q : Assertion)
    (* {{ P }} while b do d {{ Q }} end *)
  | DCPar (P : Assertion) (d1 : dcom) (Q1 : Assertion) (d2 : dcom) (Q2 : Assertion).
    (* {{ P }} (d1 {{ Q1 }}) || (d2 {{ Q2 }}) *)

Inductive decorated : Type :=
  | Decorated : dcom -> Assertion -> decorated.

Declare Custom Entry dcom.
Declare Scope dcom_scope.
Declare Custom Entry dcom_aux.
Notation "<{{ d }}>" :=
  d
  (d custom dcom_aux)
  : dcom_scope.
Notation "d '{{' Q '}}'" :=
  (Decorated d Q)
  (in custom dcom_aux at level 0, d custom dcom, Q custom assn at level 99)
  : dcom_scope.
Notation "( d )" :=
  d
  (in custom dcom, d at level 99)
  : dcom_scope.
Notation "d" :=
  d
  (in custom dcom at level 0, d constr at level 0)
  : dcom_scope.

Notation "'s{{' P '}}' 'skip'" :=
  (DCSkip P)
  (in custom dcom at level 0, P custom assn at level 99)
  : dcom_scope.

Notation "'a{{' P '}}' X ':=' a" :=
  (DCAsgn P X a)
  (in custom dcom at level 10, X constr at level 0, a custom com at level 85, P custom assn at level 99, no associativity)
  : dcom_scope.

Notation "'at{{' P '}}' 'atomic' d '{{' Q '}}' 'end'" :=
  (DCAtomic P d Q)
  (in custom dcom at level 89, P custom assn at level 99, Q custom assn at level 99)
  : dcom_scope.

Notation "d1 ; d2" :=
  (DCSeq d1 d2)
  (in custom dcom at level 90, right associativity)
  : dcom_scope.

Notation "'i{{' P '}}' 'if' b 'then' d1 '{{' Q1 '}}' 'else' d2 '{{' Q2 '}}' 'end'" :=
  (DCIf P b d1 Q1 d2 Q2)
  (in custom dcom at level 89, b custom com at level 99, P custom assn at level 99, Q1 custom assn at level 99, Q2 custom assn at level 99)
  : dcom_scope.

Notation "'w{{' P '}}' 'while' b 'do' d '{{' Q '}}' 'end'" :=
  (DCWhile P b d Q)
  (in custom dcom at level 89, b custom com at level 99, P custom assn at level 99, Q custom assn at level 99)
  : dcom_scope.

Notation "'p{{' P '}}' d1 '{{' Q1 '}}' || d2 '{{' Q2 '}}'" :=
  (DCPar P d1 Q1 d2 Q2)
  (in custom dcom at level 90, right associativity, P custom assn at level 99, Q1 custom assn at level 99, Q2 custom assn at level 99)
  : dcom_scope.
  
Open Scope dcom_scope.

Fixpoint erase (d : dcom) : com :=
  match d with
  | DCSkip P => <{ skip }>
  | DCAsgn P X a => <{ X := a }>
  | DCSeq d1 d2 => <{ erase d1 ; erase d2 }>
  | DCIf P b d1 Q1 d2 Q2 => <{ if b then erase d1 else erase d2 end }>
  | DCAtomic P d Q => <{ atomic erase d end }>
  | DCWhile P b d Q => <{ while b do erase d end }>
  | DCPar P d1 Q1 d2 Q2 => <{ erase d1 || erase d2 }>
  end.

Definition erase_d (dec : decorated) : com :=
  match dec with
  | Decorated d Q => erase d
  end.

Fixpoint pre (d : dcom) : Assertion :=
  match d with
  | DCSkip P => P
  | DCAsgn P X a => P
  | DCSeq d1 d2 => pre d1
  | DCIf P b d1 Q1 d2 Q2 => P
  | DCAtomic P d Q => P
  | DCWhile P b d Q => P
  | DCPar P d1 Q1 d2 Q2 => P
  end.

Definition precondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated d Q => pre d
  end.

Fixpoint rely (d : dcom) (Q : Assertion) : list Assertion :=
  match d with
  | DCSkip P => [P]
  | DCAsgn P X a => [P; Q]
  | DCSeq d1 d2 => rely d1 (pre d2) ++ rely d2 Q
  | DCIf P b d1 Q1 d2 Q2 => P :: rely d1 Q1 ++ rely d2 Q2
  | DCAtomic P d Q' => [P; Q]
  | DCWhile P b d Q' => Q' :: Q :: rely d Q'
  | DCPar P d1 Q1 d2 Q2 => P :: Q :: rely d1 Q1 ++ rely d2 Q2
  end.

Definition rely_from (dec : decorated) : list Assertion :=
  match dec with
  | Decorated d Q => rely d Q
  end.

Fixpoint guar (d : dcom) : list (Assertion * com) :=
  match d with
  | DCSkip P => []
  | DCAsgn P X a => [(P, <{ X := a }>)]
  | DCSeq d1 d2 => guar d1 ++ guar d2
  | DCIf P b d1 Q1 d2 Q2 => guar d1 ++ guar d2
  | DCAtomic P d Q => [(P, erase d)]
  | DCWhile P b d Q => guar d
  | DCPar P d1 Q1 d2 Q2 => guar d1 ++ guar d2
  end.

Definition guar_from (dec : decorated) : list (Assertion * com) :=
  match dec with
  | Decorated d Q => guar d
  end.

Definition postcondition_from (dec : decorated) : Assertion :=
  match dec with
  | Decorated d Q => Q
  end.

Definition decoration_derivable (dec : decorated) : Prop :=
  |- erase_d dec sat (precondition_from dec, rely_from dec, guar_from dec, postcondition_from dec).

Fixpoint verification_conditions (d : dcom) (Q : Assertion) : Prop :=
  match d with
  | DCSkip P => P ->> Q
  | DCAsgn P X a => P ->> {{ Q [ X |-> a] }}
  | DCSeq d1 d2 => (verification_conditions d1 (pre d2)) /\ (verification_conditions d2 Q)
  | DCIf P b d1 Q1 d2 Q2 => ({{ P /\ b }} ->> pre d1) /\ ({{ P /\ ~b }} ->> pre d2) /\ Q1 ->> Q /\ Q2 ->> Q /\ (verification_conditions d1 Q1) /\ (verification_conditions d2 Q2)
  | DCAtomic P d Q' => (P ->> pre d) /\ (Q' ->> Q) /\ (verification_conditions d Q')
  | DCWhile P b d Q' => (P ->> Q') /\ ({{ Q' /\ b }} ->> pre d) /\ ({{ Q' /\ ~b }} ->> Q) /\ (verification_conditions d Q')
  | DCPar P d1 Q1 d2 Q2 => (P ->> {{ $(pre d1) /\ $(pre d2) }}) /\ ({{ Q1 /\ Q2 }} ->> Q) /\ (non_interfering (rely d1 Q1) (guar d2)) /\ (non_interfering (rely d2 Q2) (guar d1)) /\ (verification_conditions d1 Q1) /\ (verification_conditions d2 Q2)
  end.

Lemma PH_Consequence_pre_post
    c P P' R G Q Q'
    (H_P_P' : P ->> P')
    (H_Q'_Q : Q' ->> Q)
    (H_derivable : |- c sat (P', R, G, Q')) :
      |- c sat (P, R, G, Q).
Proof.
  apply PH_Consequence with P' R G Q'; auto.
  - apply incl_weaker_rely.
    apply incl_refl.
  - apply incl_stronger_guar.
    apply incl_refl.
Qed.

Lemma phoare_derivable_to_hoare_derivable
    c P R G Q
    (H_np : no_par c)
    (H_derivable : |- c sat (P, R, G, Q)) :
      |- {{ P }} c {{ Q }}.
Proof.
  induction H_derivable; try (econstructor; eauto; invert H_np; eauto; fail).
  - apply H_Consequence with ({{ Q [x |-> a] }}) Q; try assumption; auto.
    constructor.
  - apply H_Consequence with P ({{ P /\ ~b }}); try assumption; auto.
    constructor.
    invert H_np.
    auto.
Qed.

Lemma np_imlies_npia
    c
    (H_np : no_par c) :
      no_par_in_atomic c.
Proof.
  induction H_np; constructor; auto.
Qed.

Theorem verification_correct
    d Q
    (H_npia : no_par_in_atomic (erase d))
    (H_vc : verification_conditions d Q) :
      |- erase d sat (pre d, rely d Q, guar d, Q).
Proof.
  generalize dependent Q.
  induction d; intros; simpl in *.
  - (* {{ P }} skip {{ Q }} *)
    eapply PH_Consequence_pre_post.
    + intros st H_P_st.
      apply H_P_st.
    + apply H_vc.
    + apply PH_Skip.
  - (* {{ P }} X := a {{ Q }} *)
    apply PH_Assgn.
    assumption.
  - (* {{ P }} atomic d {{ Q }} end {{ Q' }}*)
    rename Q0 into Q'.
    destruct H_vc as [H_P [H_Q_Q' H_vc]].
    invert H_npia.
    rename H0 into H_np.
    assert (H_npia : no_par_in_atomic (erase d)). {
      apply np_imlies_npia.
      assumption.
    }
    specialize (IHd H_npia Q H_vc).
    apply PH_Atomic.
    apply H_Consequence with (pre d) Q; try assumption.
    eapply phoare_derivable_to_hoare_derivable; eassumption.
  - (* d1 ; d2 {{ Q }} *)
    destruct H_vc as [H_vc1 H_vc2].
    invert H_npia.
    rename H1 into H_npia1.
    rename H2 into H_npia2.
    specialize (IHd1 H_npia1 (pre d2) H_vc1).
    specialize (IHd2 H_npia2 Q H_vc2).
    eapply PH_Seq.
    + apply IHd1.
    + apply IHd2.
  - (* {{ P }} if b then d1 {{ Q1 }} else d2 {{ Q2 }} end {{ Q }} *)
    destruct H_vc as [H_P1 [H_P2 [H_Q1 [H_Q2 [H_vc1 H_vc2]]]]].
    invert H_npia.
    rename H1 into H_npia1.
    rename H3 into H_npia2.
    specialize (IHd1 H_npia1 Q1 H_vc1).
    specialize (IHd2 H_npia2 Q2 H_vc2).
    eapply PH_If.
    + eapply PH_Consequence_pre_post.
      * apply H_P1.
      * apply H_Q1.
      * apply IHd1.
    + eapply PH_Consequence_pre_post.
      * apply H_P2.
      * apply H_Q2.
      * apply IHd2.
  - (* {{ P }} while b do d {{ Q }} end {{ Q' }} *)
    rename Q0 into Q'.
    destruct H_vc as [H_init [H_step [H_fin H_vc]]].
    invert H_npia.
    rename H0 into H_npia.
    specialize (IHd H_npia Q H_vc).
    apply PH_Consequence_pre_post with Q Q'; try assumption; auto.
    apply PH_While; try assumption.
    apply PH_Consequence_pre_post with (pre d) Q; try assumption; auto.
  - (* {{ P }} (d1 {{ Q1 }}) || (d2 {{ Q2 }}) {{ Q }} *)
    destruct H_vc as [H_P [H_Q [H_non_interfering1 [H_non_interfering2 [H_vc1 H_vc2]]]]].
    invert H_npia.
    rename H1 into H_npia1.
    rename H2 into H_npia2.
    specialize (IHd1 H_npia1 Q1 H_vc1).
    specialize (IHd2 H_npia2 Q2 H_vc2).
    apply PH_Par with (pre d1) (pre d2) Q1 Q2; assumption.
Qed.

Definition verification_conditions_from (dec : decorated) : Prop :=
  match dec with
  | Decorated d Q => verification_conditions d Q
  end.

Corollary verification_conditions_correct
    dec
    (H_npia : no_par_in_atomic (erase_d dec))
    (H_vc : verification_conditions_from dec) :
      decoration_derivable dec.
Proof.
  destruct dec as [d Q].
  unfold decoration_derivable.
  simpl in *.
  apply verification_correct; assumption.
Qed.