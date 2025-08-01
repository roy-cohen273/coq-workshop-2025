(*
  In this file, we'll provide tactics that solve most verification
  conditions obtained from decorated commands.

  The tactics we define are taken from PLF.Hoare2, with some modification
  to fit our use cases.
*)

Set Warnings "-notation-overridden".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From PLF Require Import Imp.
From PLF Require Import Hoare.
From PLF Require Import Semantics.
From PLF Require Import Decorated.

(* Helper lemma for later.
   Strengthening the precondition of a Hoare tripplet. *)
Lemma H_Consequence_pre
    c P P' Q
    (H_P_P' : P ->> P')
    (H_derivable : Soundness.hoare_derivable P' c Q) :
      Soundness.hoare_derivable P c Q.
Proof.
  apply Soundness.H_Consequence with P' Q; auto.
Qed.

(* Automatically solve most verification conditions.

  Differences from [PLF.Hoare2.verify_assertion]:
  - Unfolds [Soundness.non_interfering].
  - Handles [Forall] similarly to conjunction.
  - Handles [andb] similarly to [negb]:
    * simplifies [b1 && b2 = true] to [b1 = true /\ b2 = true].
    * simplifies [b1 && b2 = false] to [b1 = false \/ b2 = false].
  - Handles [orb] similarly to [negb]:
    * simplifies [b1 || b2 = true] to [b1 = true \/ b2 = true].
    * simplifies [b1 || b2 = false] to [b1 = false /\ b2 = false].
  - Tries to solve using [exfalso; eauto], since there are cases where
    [eauto] is able to find the contradiction in the assumptions, but
    doesn't realize it unless we explicitly ask it to do so (by using
    [exfalso]).
*)
Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  unfold Soundness.non_interfering;
  repeat (simpl in *;
          rewrite t_update_eq in * ||
          (try rewrite t_update_neq in *;
          try (intro X; inversion X; fail)));
  simpl in *;
  repeat
    match goal with
    | [H : _ /\ _ |- _] =>
        destruct H
    | [H : Forall _ (_ :: _) |- _] =>
        apply Forall_cons_iff in H
    end;
  repeat
    match goal with
    | [|- Forall _ (_ :: _)] =>
        apply Forall_cons
    end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat (
    rewrite andb_true_iff in * ||
    rewrite andb_false_iff in * ||
    rewrite orb_true_iff in * ||
    rewrite orb_false_iff in * ||
    rewrite negb_true_iff in * ||
    rewrite negb_false_iff in *
  );
  repeat rewrite eqb_eq in *;
  repeat rewrite eqb_neq in *;
  repeat rewrite leb_iff in *;
  repeat rewrite leb_iff_conv in *;
  try subst;
  simpl in *;
  repeat
    match goal with
      [st : state |- _] =>
        match goal with
        | [H : st _ = _ |- _] =>
            rewrite -> H in *; clear H
        | [H : _ = st _ |- _] =>
            rewrite <- H in *; clear H
        end
    end;
  repeat
    match goal with
      | [|- Forall _ (_ :: _)] =>
          apply Forall_cons
    end;
  try eauto;
  (* eauto sometimes fails to see that the goal is false *)
  try (exfalso; eauto; fail);
  try lia.

(* Try to solve goals of type |- {{ P }} c {{ Q }}, without decorations.

  This is usefull for solving non-interference checks. We can't provide
  decorations in this case because the same command is used multiple times
  with different preconditions and postconditions.

  The only supported command types are skip, assignment, atomic block,
  if statement, and sequencial composition. While statements are not
  supported because we don't know how to automatically find the loop
  invariant. Parallel composition is not supported because it is impossible
  to prove a Hoare tripplet for it.
*)
Ltac solve_hoare_tripple :=
  repeat (
    (* make sure the goal only contains supported commands, to avoid an infinite loop. *)
    match goal with
    | [|- Soundness.hoare_derivable _ (CSkip) _] => idtac
    | [|- Soundness.hoare_derivable _ (CAsgn _ _) _] => idtac
    | [|- Soundness.hoare_derivable _ (CSeq _ _) _] => idtac
    | [|- Soundness.hoare_derivable _ (CIf _ _ _) _] => idtac
    | [|- Soundness.hoare_derivable _ (CAtomic _) _] => idtac
    end;
    (* Actually do something. *)
    match goal with
    | [|- Soundness.hoare_derivable _ (CSkip) _] =>
        apply Soundness.H_Skip
    | [|- Soundness.hoare_derivable _ (CAsgn _ _) _] =>
        apply Soundness.H_Asgn
    | [|- Soundness.hoare_derivable _ (CSeq _ _) _] =>
        eapply Soundness.H_Seq
    | [|- Soundness.hoare_derivable _ (CIf _ _ _) _] =>
        apply Soundness.H_If
    | [|- Soundness.hoare_derivable _ (CAtomic _) _] =>
        apply Soundness.H_Atomic
    | [|- Soundness.hoare_derivable _ _ _] =>
        eapply H_Consequence_pre
    end
  ).

(* Automatically solve a goal of type: [decoration_derivable <{{ ... }}>]. *)
Ltac verify :=
  intros;
  apply verification_conditions_correct;
  [repeat constructor |]; (* To solve the NPIA requirement *)
  verify_assertion;
  try (solve_hoare_tripple; try solve [verify_assertion]). (* To solve simple non-interference checks *)
