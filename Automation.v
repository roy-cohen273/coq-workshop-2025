Set Warnings "-notation-overridden".
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From PLF Require Export Imp.
From PLF Require Import Hoare.
From PLF Require Import Semantics.
From PLF Require Import Decorated.

Lemma H_Consequence_pre
    c P P' Q
    (H_derivable : Soundness.hoare_derivable P' c Q)
    (H_P_P' : P ->> P') :
      Soundness.hoare_derivable P c Q.
Proof.
  apply Soundness.H_Consequence with P' Q; auto.
Qed.


Ltac verify_assertion :=
  repeat split;
  simpl;
  unfold assert_implies;
  unfold bassertion in *; unfold beval in *; unfold aeval in *;
  unfold assertion_sub; intros;
  (* <my-addition> *)
  unfold Soundness.non_interfering;
  (* </my-addition> *)
  repeat (simpl in *;
          rewrite t_update_eq ||
          (try rewrite t_update_neq;
          [| (intro X; inversion X; fail)]));
  simpl in *;
  repeat match goal with [H : _ /\ _ |- _] =>
                         destruct H end;
  repeat rewrite not_true_iff_false in *;
  repeat rewrite not_false_iff_true in *;
  repeat rewrite negb_true_iff in *;
  repeat rewrite negb_false_iff in *;
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
  (* <my-addition> *)
  repeat
    match goal with
      | [|- Forall _ (_ :: _)] =>
          apply Forall_cons
    end;
  (* </my-addition> *)
  try eauto;
  try lia.

(* Solve goals of type:
      |- {{ P }} X1 := a1 ; ... ; Xn := an {{ Q }} *)
Ltac solve_assignments :=
  eapply H_Consequence_pre; [
  repeat
    match goal with
    | [|- Soundness.hoare_derivable _ (CSeq _ _) _] =>
        eapply Soundness.H_Seq
    end;
  apply Soundness.H_Asgn |
  verify_assertion].


Ltac verify :=
  intros;
  apply verification_conditions_correct;
  try solve [repeat constructor]; (* To solve the NPIA requirement *)
  verify_assertion;
  try (solve_assignments; verify_assertion). (* To solve simple non-interference checks *)


(* Examples *)
(* TODO: move examples to Examples.v *)

Example skip_example : decoration_derivable <{{
  s{{ X = 12 }}
  skip
  {{ X = 12 }}
}}>.
Proof.
  verify.
Qed.

Example asgn_example : decoration_derivable <{{
  a{{ X = 0 }}
  X := X + 1
  {{ X = 1 }}
}}>.
Proof.
  verify.
Qed.

Example atomic_example : decoration_derivable <{{
  at{{ X = 0 /\ Y = 0 }}
  atomic
    a{{ X = 0 /\ Y = 0 }}
    X := X + 1 ;
    a{{ X = 1 /\ Y = 0 }}
    Y := Y + 1
    {{ X = 1 /\ Y = 1 }}
  end
  {{ X = 1 /\ Y = 1 }}
}}>.
Proof.
  verify.
Qed.

Example seq_example : decoration_derivable <{{
  a{{ X = 0 }}
  X := X + 1 ;
  a{{ X = 1 }}
  X := X + 1
  {{ X = 2 }}
}}>.
Proof.
  verify.
Qed.

Example if_example : decoration_derivable <{{
  i{{ X = 0 }}
  if X = 0 then
    a{{ X = 0 }}
    Y := 1
    {{ Y = 1 }}
  else
    a{{ False }}
    Y := 2
    {{ False }}
  end
  {{ Y = 1 }}
}}>.
Proof.
  verify.
Qed.

Example while_example (n : nat) : decoration_derivable <{{
  w{{ X = n /\ Y = 0 }}
  while X <> 0 do
    a{{ X > 0 /\ X + Y = n }}
    X := X - 1 ;
    a{{ X + Y + 1 = n }}
    Y := Y + 1
    {{ X + Y = n }}
  end
  {{ X = 0 /\ Y = n }}
}}>.
Proof.
  verify.
Qed.

Definition a : string := "a".
Definition b : string := "b".

Example par_example : decoration_derivable <{{
  p{{ X = 0 /\ b = 2 }}
    a{{ True }}
    X := 1 ;
    a{{ X = 1 }}
    a := Y
    {{ X = 1 /\ (Y = 1 -> a = 1 \/ b = 1 \/ b = 2)}}
  ||
    a{{ b = 2 /\ X <> 2 }}
    Y := 1 ;
    a{{ Y = 1 /\ X <> 2 }}
    b := X
    {{ Y = 1 /\ b <> 2}}
  {{ a = 1 \/ b = 1 }}
}}>.
Proof.
  verify.
Qed.

Example message_passing (n : nat) : decoration_derivable <{{
  p{{ Y = 0 }}
    a{{ True }}
    X := n ;
    a{{ X = n }}
    Y := 1
    {{ True }}
  ||
    w{{ Y <> 0 -> X = n }}
    while Y = 0 do
      s{{ Y <> 0 -> X = n }}
      skip
      {{ Y <> 0 -> X = n }}
    end ;
    a{{ X = n }}
    a := X
    {{ a = n }}
  {{ a = n }}
}}>.
Proof.
  verify.
Qed.
