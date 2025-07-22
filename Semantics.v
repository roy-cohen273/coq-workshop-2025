(*
  In this file, we will define the programming language we're working with,
  along with its smallstep semantics.

  We will also define what is a specification, and what is means,
  semantically, for a command to satisfy a specification.
*)

Set Warnings "-notation-overridden".
From Coq Require Import List. Import ListNotations.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Hoare.


Ltac invert H := inversion H; subst; clear H.

(*
  Our programming language will be similar to the Imp language defined in
  PLF, except with 3 new types of commands:
  - Atomic blocks.
  - Parallel composition.
  - Havoc commands.
    (Not intended for actual use, only as an auxiliary to the ghost variable
    rule).
  
  The semantics will also be very similar to PLF's Imp, but with instant
  expression evaluation. That is, we'll use bigstep semantics ([aeval],
  [beval]) instead of smallstep semantics ([-->a, -->b]) when evaluating
  expression.
  Also, our 3 new command types will have the following semantics:
  - For atomic blocks [<{ atomic c end }>], it will progress to <{ skip }>
    in a single step, and have the same effect on the state as multiple
    steps done by the inner command [c].
  - For parallel composition [<{ c1 || c2 }>], it will progress either by
    taking a step in the inner left command [c1] or by taking a step in the
    inner right command [c2].
  - For a havoc command [<{ havoc vars }>], it will progress to <{ skip }>
    in a single step, and its effect on the state would be to chage the
    values of [vars] indeterministically.
*)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CAtomic : com -> com
  | CPar : com -> com -> com
  | CHavoc : list string -> com.


Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
           (in custom com at level 89, x at level 99,
            y at level 99) : com_scope.
Notation "x || y" :=
         (CPar x y)
           (in custom com at level 90, right associativity).
Notation "'atomic' x 'end'" :=
         (CAtomic x)
           (in custom com at level 89, x at level 99).
Notation "'havoc' vars" :=
         (CHavoc vars)
           (in custom com at level 89).

Definition differ_only_vars
    (vars : list string) (st st' : state) : Prop :=
  forall x, In x vars \/ st x = st' x.

Notation "'<<' vars '>>' st '~' st'" := (differ_only_vars vars st st')
    (at level 2).


Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).
Inductive cstep : (com * state)  -> (com * state) -> Prop :=
  | CS_Asgn : forall st i a,
      <{ i := a }> / st --> <{ skip }> / (i !-> aeval st a ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfTrue : forall st b c1 c2,
      beval st b = true ->
      <{ if b then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st b c1 c2,
      beval st b = false ->
      <{ if b then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
  | CS_Atomic : forall st st' c,
      (* c / st -->* <{ skip }> / st' -> *)
      multi cstep (c, st) (<{ skip }>, st') ->
      <{ atomic c end }> / st --> <{ skip }> / st'
  | CS_Par1 : forall st st' c1 c1' c2,
      c1 / st --> c1' / st' ->
      <{ c1 || c2 }> / st --> <{ c1' || c2 }> / st'
  | CS_Par2 : forall st st' c1 c2 c2',
      c2 / st --> c2' / st' ->
      <{ c1 || c2 }> / st --> <{ c1 || c2' }> / st'
  | CS_ParDone : forall st,
      <{ skip || skip }> / st --> <{ skip }> / st
  | CS_Havoc : forall st st' vars,
      <<vars>> st ~ st' ->
      <{ havoc vars }> / st --> <{ skip }> / st'

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Notation " t '/' st '-->*' t' '/' st' " :=
  (multi cstep  (t,st) (t',st'))
  (at level 40, st at level 39, t' at level 39).


(* Redo standard Hoare logic semntics with the new smallstep semantics. *)

Definition hoare_valid (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
    P st ->
    c / st -->* <{ skip }> / st' ->
    Q st'.

Notation "'|=' '{{' P '}}' c '{{' Q '}}'" :=
         (hoare_valid P c Q)
         (at level 2,
          P custom assn at level 99,
          c custom com at level 99,
          Q custom assn at level 99).


(*
  Next up is to define a computation.
  A computation is a series of transitions, each of which is either a
  component transition or an enviroment transition.

  Component transitions behave like the smallstep semantics (defined above).

  Enviroment transitions can do whatever they want to the state of the
  variables, but cannot change the command.
*)
(* There are 2 ways to define a computation, "backwards" and "forwards".
   The "backwards" definition is generally easier to work with,
   but for some proofs (notably the soundness of the parallel rule)
   we will need the "forwards" definition. *)

Inductive bcomp : com -> state -> com -> state -> Type :=
  (* The empty path *)
  | bcomp_empty : forall
      c st,
        bcomp c st c st
  (* Component transition c / st --> c' / st' *)
  | bcomp_cmp : forall
      c st c' st' c'' st''
      (H_step : c / st --> c' / st')
      (C : bcomp c' st' c'' st''),
        bcomp c st c'' st''
  (* Enviroment transition c / st --> c / st' *)
  | bcomp_env : forall
      c st st' c'' st''
      (C : bcomp c st' c'' st''),
        bcomp c st c'' st''.

Inductive fcomp : com -> state -> com -> state -> Type :=
  (* The empty path *)
  | fcomp_empty : forall
      c st,
        fcomp c st c st
  (* Component transition c' / st' --> c'' / st'' *)
  | fcomp_cmp : forall
      c st c' st' c'' st''
      (H_step : c' / st' --> c'' / st'')
      (C : fcomp c st c' st'),
        fcomp c st c'' st''
  (* Enviroment transition c' / st' --> c' / st'' *)
  | fcomp_env : forall
      c st c' st' st''
      (C : fcomp c st c' st'),
        fcomp c st c' st''.


(* Specification validity *)

(* We will define 2 ways for a specification to be valid,
   one with "backwards" computations and one with "farwards" computations.
   We will later show these 2 notions of specification validity are equivalent.
   
   For each direction, we will seperately define the assumption induced from
   the precondition and rely, and the conclusion induced from the postcondition
   and guarantee. Specification validity, then, is defined to mean that every
   computation that satisfies the assumption must also satisfy the conclusion. *)

Fixpoint bcomp_sat_rely
    {c st c' st'}
    (R : list Assertion)
    (C : bcomp c st c' st')
    : Prop :=
  match C with
  | bcomp_empty c st => True
  | bcomp_cmp c st c' st' c'' st'' step rest =>
      bcomp_sat_rely R rest
  | bcomp_env c st st' c'' st'' rest =>
      Forall (fun P => P st -> P st') R /\
      bcomp_sat_rely R rest
  end.

Definition bcomp_assumption
    {c st c' st'}
    (P : Assertion)
    (R : list Assertion)
    (C : bcomp c st c' st')
    : Prop :=
  P st /\ bcomp_sat_rely R C.

Fixpoint bcomp_conclusion
    {c st c' st'}
    (Q : Assertion)
    (G : list (Assertion * com))
    (C : bcomp c st c' st')
    : Prop :=
  match C with
  | bcomp_empty c st =>
      c = <{ skip }> -> Q st
  | bcomp_cmp c st c' st' c'' st'' step rest =>
      (
        st = st' \/
        Exists (fun (g : Assertion * com) =>
          let (Q, c) := g in
          Q st /\ c / st -->* <{ skip }> / st'
        ) G
      ) /\
      bcomp_conclusion Q G rest
  | bcomp_env c st st' c'' st'' rest =>
      bcomp_conclusion Q G rest
  end.

Definition phoare_valid (c : com) (P : Assertion) (R : list Assertion) (G : list (Assertion * com)) (Q : Assertion) : Prop :=
  forall st c' st' (C : bcomp c st c' st'),
    bcomp_assumption P R C ->
    bcomp_conclusion Q G C.

Notation "'|=' c 'sat' '(' P ',' R ',' G ',' Q ')'" :=
    (phoare_valid c P R G Q)
    (at level 2,
     c custom com at level 99,
     P at level 99,
     R at level 99,
     G at level 99,
     Q at level 99).

Fixpoint fcomp_assumption
    { c st c' st' }
    (P : Assertion)
    (R : list Assertion)
    (C : fcomp c st c' st')
    : Prop :=
  match C with
  | fcomp_empty c st => P st
  | fcomp_cmp c st c' st' c'' st'' step C' =>
      fcomp_assumption P R C'
  | fcomp_env c st c' st' st'' C' =>
      Forall (fun P => P st' -> P st'') R /\
      fcomp_assumption P R C'
  end.

Fixpoint fcomp_sat_guar
    {c st c' st'}
    (G : list (Assertion * com))
    (C : fcomp c st c' st')
    : Prop :=
  match C with
  | fcomp_empty c st => True
  | fcomp_cmp c st c' st' c'' st'' step C' =>
      (
        st' = st'' \/
        Exists (fun (g : Assertion * com) =>
          let (Q, c) := g in
          Q st' /\ c / st' -->* <{ skip }> / st''
        ) G
      ) /\
      fcomp_sat_guar G C'
  | fcomp_env c st c' st' st'' C' =>
      fcomp_sat_guar G C'
  end.

Definition fcomp_conclusion
    {c st c' st'}
    (Q : Assertion)
    (G : list (Assertion * com))
    (C : fcomp c st c' st')
    : Prop :=
  fcomp_sat_guar G C /\
  (c' = <{ skip }> -> Q st').

Definition phoare_valid_forward (c : com) (P : Assertion) (R : list Assertion) (G : list (Assertion * com)) (Q : Assertion) : Prop :=
  forall st c' st' (C : fcomp c st c' st'),
    fcomp_assumption P R C ->
    fcomp_conclusion Q G C.

Notation "'f|=' c 'sat' '(' P ',' R ',' G ',' Q ')'" :=
    (phoare_valid_forward c P R G Q)
    (at level 2,
     c custom com at level 99,
     P at level 99,
     R at level 99,
     G at level 99,
     Q at level 99).


(* "backwards" and "forwards" equivalency *)

(* This function takes a "backwards" computation and a "forwards" computation
   and appends them. It returns the result as a "backwards" computation. *)
Fixpoint bapp
    {c st c' st' c'' st''}
    (fC : fcomp c st c' st')
    (bC : bcomp c' st' c'' st'')
    : bcomp c st c'' st''.
  invert fC.
  - exact bC.
  - eapply bapp.
    + exact C.
    + eapply bcomp_cmp.
      * exact H_step.
      * exact bC.
  - eapply bapp.
    + exact C.
    + eapply bcomp_env.
      exact bC.
Defined.

Lemma bapp_assumption
    c st c' st' c'' st''
    (fC : fcomp c st c' st') (bC : bcomp c' st' c'' st'')
    P R
    (H_assumption : fcomp_assumption P R fC)
    (H_sat_rely : bcomp_sat_rely R bC) :
      bcomp_assumption P R (bapp fC bC).
Proof.
  unfold bcomp_assumption.
  induction fC; simpl in *.
  - split; assumption.
  - apply IHfC; assumption.
  - destruct H_assumption.
    apply IHfC; try assumption.
    simpl.
    split; assumption.
Qed.

Lemma bapp_conclusion
    c st c' st' c'' st''
    (fC : fcomp c st c' st') (bC : bcomp c' st' c'' st'')
    Q G
    (H_conclusion : bcomp_conclusion Q G (bapp fC bC)) :
      fcomp_sat_guar G fC /\
      bcomp_conclusion Q G bC.
Proof.
  induction fC; simpl in *.
  - split; auto.
  - specialize (IHfC _ H_conclusion).
    clear H_conclusion.
    simpl in IHfC.
    destruct IHfC as [H_sat_guar [H_guar_step H_conclusion]].
    repeat split; assumption.
  - specialize (IHfC _ H_conclusion).
    clear H_conclusion.
    simpl in IHfC.
    assumption.
Qed.

Lemma bvalid_imp_fvalid
    c P R G Q
    (H_valid : |= c sat (P, R, G, Q)) :
      f|= c sat (P, R, G, Q).
Proof.
  unfold phoare_valid_forward.
  intros st c' st' fC H_fassumption.
  remember (bapp fC (bcomp_empty c' st')) as bC.
  assert (bcomp_assumption P R bC) as H_bassumption. {
    subst.
    apply bapp_assumption; try assumption.
    simpl.
    exact I.
  }
  apply H_valid in H_bassumption as H_bconclusion.
  subst.
  apply bapp_conclusion in H_bconclusion as [H_sat_guar H_bconclusion].
  simpl in H_bconclusion.
  split; assumption.
Qed.

(* This function takes a "backwards" computation and a "forwards" computation
   and appends them. It returns the result as a "forwards" computation. *)
Fixpoint fapp
    {c st c' st' c'' st''}
    (fC : fcomp c st c' st')
    (bC : bcomp c' st' c'' st'')
    : fcomp c st c'' st''.
  invert bC.
  - exact fC.
  - eapply fapp.
    2: exact C.
    eapply fcomp_cmp.
    + exact H_step.
    + exact fC.
  - eapply fapp.
    2: exact C.
    eapply fcomp_env.
    exact fC.
Defined.

Lemma fapp_assumption
    c st c' st' c'' st''
    (fC : fcomp c st c' st') (bC : bcomp c' st' c'' st'')
    P R
    (H_assumption : fcomp_assumption P R fC)
    (H_sat_rely : bcomp_sat_rely R bC) :
      fcomp_assumption P R (fapp fC bC).
Proof.
  induction bC; simpl in *.
  - assumption.
  - apply IHbC; assumption.
  - destruct H_sat_rely as [H_sat_step H_sat_rely].
    apply IHbC; try assumption.
    simpl.
    split; assumption.
Qed.

Lemma fapp_conclusion
    c st c' st' c'' st''
    (fC : fcomp c st c' st') (bC : bcomp c' st' c'' st'')
    Q G
    (H_conclusion : fcomp_conclusion Q G (fapp fC bC)) :
      fcomp_sat_guar G fC /\
      bcomp_conclusion Q G bC.
Proof.
  destruct H_conclusion as [H_sat_guar H_postcondition].
  induction bC; simpl in *.
  - split; assumption.
  - specialize (IHbC _ H_sat_guar H_postcondition).
    clear H_sat_guar H_postcondition.
    simpl in IHbC.
    destruct IHbC as [[H_guar_step H_sat_guar] H_conclusion].
    repeat split; assumption.
  - specialize (IHbC _ H_sat_guar H_postcondition).
    clear H_sat_guar H_postcondition.
    simpl in IHbC.
    assumption.
Qed.

Lemma fvalid_imp_bvalid
    c P R G Q
    (H_valid : f|= c sat (P, R, G, Q)) :
      |= c sat (P, R, G, Q).
Proof.
  unfold phoare_valid.
  intros st c' st' bC H_bassumption.
  remember (fapp (fcomp_empty c st) bC) as fC.
  destruct H_bassumption as [H_precondition H_sat_rely].
  assert (fcomp_assumption P R fC) as H_fassumption. {
    subst.
    apply fapp_assumption; assumption.
  }
  apply H_valid in H_fassumption as H_conclusion.
  subst.
  apply fapp_conclusion in H_conclusion as [H_sat_guar H_conclusion].
  assumption.
Qed.

Theorem bvalid_iff_fvalid
    c P R G Q :
      |= c sat (P, R, G, Q)
      <->
      f|= c sat (P, R, G, Q).
Proof.
  split.
  - apply bvalid_imp_fvalid.
  - apply fvalid_imp_bvalid.
Qed.
