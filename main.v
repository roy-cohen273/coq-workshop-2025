Set Warnings "-notation-overridden".
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Import Maps.
From PLF Require Import Imp.
From PLF Require Import Smallstep.
From PLF Require Import Hoare.


Ltac invert H := inversion H; subst; clear H.


(* Add atomic blocks and parallel composition to the language,
   and redefine the smallstep semantics.
   In the new semantics, expression evaluation is instantanuous. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CAtomic : com -> com
  | CPar : com -> com -> com.


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

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

Notation " t '/' st '-->*' t' '/' st' " :=
  (multi cstep  (t,st) (t',st'))
  (at level 40, st at level 39, t' at level 39).

(* Redo standard Hoare logic with the new smallstep semantics. *)
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

(* Now to the fun part: parallelism! *)

(* Semantics *)

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
   We will later show these 2 notions of specification validity are equivalent. *)

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
      |- c1 || c2 sat (P, ([P; Q] ++ R1 ++ R2), G1 ++ G2, Q)

  where "'|-' c 'sat' '(' P ',' R ',' G ',' Q ')'" := (phoare_derivable c P R G Q).

(* Soundness *)

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
    (H_P_R : In P R)
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
      |= c1 || c2 sat (P, ([P; Q] ++ R1 ++ R2), G1 ++ G2, Q).
Proof.
  rewrite bvalid_iff_fvalid in *.
  unfold phoare_valid_forward.
  intros st c' st' C H_assumption.
  set (lemma := par_lemma).
  specialize (lemma c1 c2 P P1 P2 ([P; Q] ++ R1 ++ R2) R1 R2 (G1 ++ G2) G1 G2 Q Q1 Q2 H_c1_valid H_c2_valid H_P_P1_P2 H_Q1_Q2_Q H_non_interfering1 H_non_interfering2).
  assert (In P ([P; Q] ++ R1 ++ R2)) as H_P_R. {
    apply in_or_app.
    simpl.
    auto.
  }
  specialize (lemma H_P_R).
  assert (In Q ([P; Q] ++ R1 ++ R2)) as H_Q_R. {
    apply in_or_app.
    simpl.
    auto.
  }
  specialize (lemma H_Q_R).
  assert (incl R1 ([P; Q] ++ R1 ++ R2)) as H_R1_R. {
    apply incl_appr.
    apply incl_appl.
    apply incl_refl.
  }
  specialize (lemma H_R1_R).
  assert (incl R2 ([P; Q] ++ R1 ++ R2)) as H_R2_R. {
    apply incl_appr.
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

(* Ghost variable rule *)

(* Before we talk about the ghost variable rule itself,
   we need 2 preliminaries:
   1. An equivalence relation on states that doesn't care
      about the values of ghost variables.
   2. We need to define what it means for a variable to
      not appear in an expression, and prove the basic property:
      If a variable doesn't appear in an expression, its value
      cannot impact the evaluation of the expression.
   
   We'll use the shorthand DHG to mean "doesn't have ghosts". *)

Definition differ_only_ghosts (gvars : list string) (st st' : state) : Prop :=
  forall x, In x gvars \/ st x = st' x.

Notation " '<<' gvars '>>' st '~' st' " := (differ_only_ghosts gvars st st')
                                       (at level 2).

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
    (H_differ : differ_only_ghosts gvars st st') :
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
    (H_differ : differ_only_ghosts gvars st st') :
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
    differ_only_ghosts gvars st st' ->
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
Inductive remove_ghost_variables : list string -> com -> com -> Prop :=
  | GSkip : forall gvars,
      <(gvars)> skip ~> skip
  | GAssnNonGhost : forall x a gvars,
      ~ In x gvars ->
      aexp_dhg gvars a ->
      <(gvars)> x := a ~> x := a
  | GAssnGhost : forall g a gvars (H_In_gvars : In g gvars),
      <(gvars)> g := a ~> skip
  | GSeq : forall c1 c1' c2 c2' gvars,
      <(gvars)> c1 ~> c1' ->
      <(gvars)> c2 ~> c2' ->
      <(gvars)> <{ c1 ; c2 }> ~> <{ c1' ; c2' }>
  | GIf : forall b c1 c1' c2 c2' gvars,
      <(gvars)> c1 ~> c1' ->
      <(gvars)> c2 ~> c2' ->
      bexp_dhg gvars b ->
      <(gvars)> if b then c1 else c2 end ~> if b then c1' else c2' end
  | GWhile : forall b c c' gvars,
      <(gvars)> c ~> c' ->
      bexp_dhg gvars b ->
      <(gvars)> while b do c end ~> while b do c' end
  | GAtomic : forall c c' gvars,
      <(gvars)> c ~> c' ->
      <(gvars)> atomic c end ~> atomic c' end
  | GPar : forall c1 c1' c2 c2' gvars,
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
        -- destruct H as [cl3 [H_eq_c3 H_step'] ].
           left.
           exists cl3.
           split; try assumption.
           apply multi_step with (c1', st2); assumption.
        -- destruct H as [st2' [H_step' H_step''] ].
           right.
           exists st2'.
           split; try assumption.
           apply multi_step with (c1', st2); assumption.
      * right.
        exists st2.
        split; [constructor | assumption].
  - intros [ [cl3 [H_eq_c3 H_step] ] | [st2 [H_step1 H_step2] ] ].
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
    differ_only_ghosts gvars st st' /\
    P st'.

Definition rely_doesnt_restrict
    (gvars : list string) (R : list Assertion) : Prop :=
  forall st, exists st',
    differ_only_ghosts gvars st st' /\
    Forall (fun r => (exists st'', r st'') -> r st') R.

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
    destruct H_steps_dhg as [ [c1_dhg' [H_eq_c_dhg' H_steps_1dhg] ] | [st_dhg_m [H_steps_1dhg H_steps_2dhg] ] ].
    + clear IHH_remove_gvars2.
      specialize (IHH_remove_gvars1 st_hg st_dhg H_differ st_dhg' c1_dhg' H_steps_1dhg).
      destruct IHH_remove_gvars1 as [c1_hg' [st_hg' [H_remove_gvars1' [H_differ' [H_steps_1hg H_eq_gvars] ] ] ] ].
      subst.
      exists <{ c1_hg' ; c2_hg }>, st_hg'.
      repeat split; try (constructor; assumption); try assumption.
      apply seq_multistep.
      left.
      exists c1_hg'.
      split; auto.
    + specialize (IHH_remove_gvars1 st_hg st_dhg H_differ st_dhg_m <{ skip }> H_steps_1dhg).
      destruct IHH_remove_gvars1 as [skip' [st_hg_m [H_remove_gvars_skip [H_differ_m [H_steps_1hg H_eq_gvars1] ] ] ] ].
      invert H_remove_gvars_skip.
      * specialize (IHH_remove_gvars2 st_hg_m st_dhg_m H_differ_m st_dhg' c_dhg' H_steps_2dhg).
        destruct IHH_remove_gvars2 as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps_2hg H_eq_gvars2] ] ] ] ].
        exists c_hg', st_hg'.
        repeat split; try assumption.
        -- apply seq_multistep.
           right.
           exists st_hg_m.
           split; assumption.
        -- rewrite Forall_forall in *.
           intros g H_In_gvars.
           transitivity (st_dhg_m g).
           ++ apply H_eq_gvars1.
              assumption.
           ++ apply H_eq_gvars2.
              assumption.
      * set (st_dhg_m' := (g !-> aeval st_dhg_m a ; st_dhg_m)).
        set (st_hg_m' := (g !-> aeval st_hg_m a ; st_hg_m)).
        assert (H_differ_m' : <<gvars>> st_hg_m' ~ st_dhg_m). {
          apply differ_trans with st_dhg_m'.
          - intros x.
            destruct (string_dec g x).
            + subst.
              left.
              assumption.
            + subst st_hg_m'.
              subst st_dhg_m'.
              rewrite t_update_neq; try assumption.
              rewrite t_update_neq; try assumption.
              apply H_differ_m.
          - subst st_dhg_m'.
            apply differ_symm.
            apply t_update_gvar.
            assumption.
        }
        specialize (IHH_remove_gvars2 st_hg_m' st_dhg_m H_differ_m' st_dhg' c_dhg' H_steps_2dhg).
        destruct IHH_remove_gvars2 as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps_2hg H_eq_gvars2] ] ] ] ].
        exists c_hg', st_hg'.
        repeat split; try assumption.
        -- apply seq_multistep.
           right.
           exists st_hg_m'.
           split; try assumption.
           apply multi_trans with (<{ g := a }>, st_hg_m); try assumption.
           apply multi_R.
           constructor.
        -- rewrite Forall_forall in *.
           intros g' H_In_gvars'.
           transitivity (st_dhg_m g').
           ++ apply H_eq_gvars1.
              assumption.
           ++ apply H_eq_gvars2.
              assumption.
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
        destruct IHH_remove_gvars1 as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [H_steps_hg H_eq_gvars'] ] ] ] ].
        exists c_hg'', st_hg''.
        repeat split; try assumption.
        econstructor.
        -- apply CS_IfTrue.
           rewrite <- H1.
           apply bdhg_eval with gvars; assumption.
        -- assumption.
      * clear IHH_remove_gvars1.
        specialize (IHH_remove_gvars2 st_hg st_dhg' H_differ st_dhg'' c_dhg'' H_steps_dhg).
        destruct IHH_remove_gvars2 as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [H_steps_hg H_eq_gvars'] ] ] ] ].
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
      destruct IHH_remove_gvars as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps H_eq_gvars] ] ] ] ].
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
      destruct IHH_remove_gvars as [skip' [st_hg' [H_remove_gvars_skip [H_differ' [H_steps H_eq_gvars] ] ] ] ].
      invert H_remove_gvars_skip.
      * specialize (IHH_steps_dhg st_hg' H_differ').
        destruct IHH_steps_dhg as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [H_steps' H_eq_gvars'] ] ] ] ].
        exists c_hg'', st_hg''.
        repeat split; try assumption.
        -- econstructor.
           1: constructor.
           econstructor.
           1: constructor. {
             rewrite <- H0.
             apply bdhg_eval with gvars; assumption.
           }
           apply seq_multistep.
           right.
           exists st_hg'.
           split; assumption.
        -- rewrite Forall_forall in *.
           intros g H_In_gvars.
           transitivity (st' g).
           ++ apply H_eq_gvars.
              assumption.
           ++ apply H_eq_gvars'.
              assumption.
      * set (st_hg'_ := (g !-> aeval st_hg' a ; st_hg')).
        assert (H_differ'_ : <<gvars>> st_hg'_ ~ st'). {
          apply differ_trans with st_hg'; try assumption.
          subst st_hg'_.
          apply differ_symm.
          apply t_update_gvar.
          assumption.
        }
        specialize (IHH_steps_dhg st_hg'_ H_differ'_).
        destruct IHH_steps_dhg as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [H_steps' H_eq_gvars'] ] ] ] ].
        exists c_hg'', st_hg''.
        repeat split; try assumption.
        -- econstructor.
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
           apply multi_trans with (<{ g := a }>, st_hg'); try assumption.
           apply multi_R.
           constructor.
        -- rewrite Forall_forall in *.
           intros g' H_In_gvars'.
           transitivity (st' g').
           ++ apply H_eq_gvars.
              assumption.
           ++ apply H_eq_gvars'.
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
      destruct IHH_remove_gvars as [skip' [st_hg'' [H_remove_gvars_skip [H_differ'' [H_steps H_eq_gvars] ] ] ] ].
      invert H_remove_gvars_skip.
      * exists <{ skip }>, st_hg''.
        repeat split; try (constructor; assumption); try assumption.
        apply multi_R.
        constructor.
        assumption.
      * exists <{ skip }>, (g !-> aeval st_hg'' a ; st_hg'').
        repeat split; try (constructor; assumption); try assumption.
        -- apply differ_trans with st_hg''; try assumption.
           apply differ_symm.
           apply t_update_gvar.
           assumption.
        -- apply multi_R.
           constructor.
           apply multi_trans with (<{ g := a }>, st_hg''); try assumption.
           apply multi_R.
           constructor.
  - invert H_np.
Qed.



Lemma step_add_gvars
    gvars c_dhg st_dhg c_dhg' st_dhg' c_hg st_hg
    (H_npia : no_par_in_atomic c_dhg)
    (H_remove_gvars : <(gvars)> c_hg ~> c_dhg)
    (H_differ : <<gvars>> st_hg ~ st_dhg)
    (H_step_dhg : c_dhg / st_dhg --> c_dhg' / st_dhg') :
      exists c_hg' st_hg',
        <(gvars)> c_hg' ~> c_dhg' /\
        <<gvars>> st_hg' ~ st_dhg' /\
        (
          (c_hg / st_hg --> c_hg' / st_hg' /\ (st_hg = st_hg' -> st_dhg = st_dhg')) \/
          (c_hg / st_hg -->* c_hg' / st_hg' /\ st_dhg = st_dhg')
        ).
Proof.
  generalize dependent c_dhg'.
  induction H_remove_gvars; intros.
  - invert H_step_dhg.
  - invert H_step_dhg.
    exists <{ skip }>, (x !-> aeval st_hg a ; st_hg).
    repeat split.
    + constructor.
    + intros x'.
      destruct (string_dec x x').
      * subst.
        rewrite t_update_eq.
        rewrite t_update_eq.
        right.
        apply adhg_eval with gvars; assumption.
      * rewrite t_update_neq; try assumption.
        rewrite t_update_neq; try assumption.
        apply H_differ.
    + left.
      split; try solve [constructor].
      intros H_eq_st_hg.
      symmetry.
      replace (aeval st_dhg a) with (st_dhg x). {
        apply t_update_same.
      }
      transitivity (st_hg x). {
        destruct (H_differ x); auto.
        exfalso.
        auto.
      }
      transitivity (aeval st_hg a). {
        rewrite H_eq_st_hg.
        rewrite t_update_eq.
        rewrite <- H_eq_st_hg.
        reflexivity.
      }
      apply adhg_eval with gvars; assumption.
  - invert H_step_dhg.
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
      rename H0 into H_step_1dhg.
      specialize (IHH_remove_gvars1 H_differ c1_dhg' H_step_1dhg).
      destruct IHH_remove_gvars1 as [c1_hg' [st_hg' [H_remove_gvars1' [ H_differ' [ [H_step_1hg H_eq_down] | [H_step_1hg H_st_dhg_st_dhg'] ] ] ] ] ].
      * exists <{ c1_hg' ; c2_hg }>, st_hg'.
        repeat split; try (constructor; assumption); try assumption.
        left.
        split; try assumption.
        constructor.
        assumption.
      * exists <{ c1_hg' ; c2_hg }>, st_hg'.
        repeat split; try (constructor; assumption); try assumption.
        right.
        split; try assumption.
        clear dependent st_dhg.
        clear dependent st_dhg'.
        clear dependent c1_dhg.
        clear dependent c2_dhg.
        clear dependent gvars.
        clear dependent c1_dhg'.
        remember (c1_hg, st_hg) as p.
        remember (c1_hg', st_hg') as p'.
        generalize dependent c1_hg.
        generalize dependent st_hg.
        induction H_step_1hg; intros; subst.
        -- invert Heqp.
           constructor.
        -- destruct y as [c1_hg_m st_hg_m].
           specialize (IHH_step_1hg eq_refl st_hg_m c1_hg_m eq_refl).
           econstructor; try eassumption.
           constructor.
           assumption.
    + clear IHH_remove_gvars1.
      invert H_remove_gvars1.
      * exists c2_hg, st_hg.
        repeat split; try assumption.
        left.
        split; constructor.
      * exists c2_hg, (g !-> aeval st_hg a ; st_hg).
        repeat split; try assumption.
        -- apply differ_trans with st_hg; try assumption.
           apply differ_symm.
           apply t_update_gvar.
           assumption.
        -- right.
           split; try reflexivity.
           econstructor.
           ++ constructor.
              constructor.
           ++ econstructor; constructor.
  - invert H_npia.
    specialize (IHH_remove_gvars1 H2).
    specialize (IHH_remove_gvars2 H4).
    clear H2 H4.
    invert H_step_dhg.
    + exists c1, st_hg.
      repeat split; try assumption.
      left.
      split; constructor.
      rewrite <- H1.
      apply bdhg_eval with gvars; assumption.
    + exists c2, st_hg.
      repeat split; try assumption.
      left.
      split; constructor.
      rewrite <- H1.
      apply bdhg_eval with gvars; assumption.
  - invert H_npia.
    specialize (IHH_remove_gvars H1).
    clear H1.
    invert H_step_dhg.
    exists <{ if b then c; while b do c end else skip end }>, st_hg.
    repeat split; try assumption.
    + constructor; try assumption; constructor; try assumption.
      constructor; assumption.
    + left.
      split; constructor.
  - rename c into c_hg.
    rename c' into c_dhg.
    invert H_npia.
    invert H_step_dhg.
    assert (exists c_hg' st_hg',
        <(gvars)> c_hg' ~> <{ skip }> /\
        <<gvars>> st_hg' ~ st_dhg' /\
        c_hg / st_hg -->* c_hg' / st_hg' /\ 
        Forall (fun g => st_dhg g = st_dhg' g) gvars) as [c_hg' [st_hg' [H_remove_gvars' [H_differ' [H_steps_hg H_eq_gvars] ] ] ] ]. {
      apply multistep_add_gvars with c_dhg; assumption.
    }
    invert H_remove_gvars'.
    + exists <{ skip }>, st_hg'.
      repeat split; try (constructor; assumption); try assumption.
      left.
      split.
      * constructor.
        assumption.
      * intros. subst.
        apply functional_extensionality.
        intros x.
        rewrite Forall_forall in H_eq_gvars.
        specialize (H_eq_gvars x).
        destruct (H_differ x); auto.
        destruct (H_differ' x); auto.
        transitivity (st_hg' x); auto.
    + exists <{ skip }>, (g !-> aeval st_hg' a ; st_hg').
      repeat split; try (constructor; assumption).
      * apply differ_trans with st_hg'; try assumption.
        apply differ_symm.
        apply t_update_gvar.
        assumption.
      * left.
        split.
        -- constructor.
           apply multi_trans with (<{ g := a }>, st_hg'); try assumption.
           apply multi_R.
           constructor.
        -- intros.
           apply functional_extensionality.
           intros x.
           rewrite Forall_forall in H_eq_gvars.
           specialize (H_eq_gvars x).
           destruct (H_differ x); auto.
           destruct (H_differ' x); auto.
           subst.
           destruct (string_dec g x).
           ++ subst.
              auto.
           ++ rewrite t_update_neq in H2; try assumption.
              transitivity (st_hg' x); auto.
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
      rename H0 into H_step_1dhg.
      specialize (IHH_remove_gvars1 H_differ c1_dhg' H_step_1dhg).
      destruct IHH_remove_gvars1 as [c1_hg' [st_hg' [H_remove_gvars1' [H_differ' [ [H_step_1hg H_eq_down] | [H_step_1hg H_st_dhg_st_dhg'] ] ] ] ] ].
      * exists <{ c1_hg' || c2_hg }>, st_hg'.
        repeat split; try (constructor; assumption); try assumption.
        left.
        split; try assumption.
        constructor.
        assumption.
      * exists <{ c1_hg' || c2_hg }>, st_hg'.
        repeat split; try (constructor; assumption); try assumption.
        right.
        split; try assumption.
        clear dependent st_dhg.
        clear dependent st_dhg'.
        clear dependent c1_dhg.
        clear dependent c2_dhg.
        clear dependent gvars.
        clear dependent c1_dhg'.
        remember (c1_hg, st_hg) as p.
        remember (c1_hg', st_hg') as p'.
        generalize dependent c1_hg.
        generalize dependent st_hg.
        induction H_step_1hg; intros; subst.
        -- invert Heqp.
           constructor.
        -- destruct y as [c1_hg_m st_hg_m].
           specialize (IHH_step_1hg eq_refl st_hg_m c1_hg_m eq_refl).
           econstructor.
           ++ constructor.
              eassumption.
           ++ assumption.
    + rename c2' into c2_dhg'.
      rename H0 into H_step_2dhg.
      specialize (IHH_remove_gvars2 H_differ c2_dhg' H_step_2dhg).
      destruct IHH_remove_gvars2 as [c2_hg' [st_hg' [H_remove_gvars2' [H_differ' [ [H_step_2hg H_eq_down] | [H_step_2hg H_st_dhg_st_dhg'] ] ] ] ] ].
      * exists <{ c1_hg || c2_hg' }>, st_hg'.
        repeat split; try (constructor; assumption); try assumption.
        left.
        split; try assumption.
        constructor.
        assumption.
      * exists <{ c1_hg || c2_hg' }>, st_hg'.
        repeat split; try (constructor; assumption); try assumption.
        right.
        split; try assumption.
        clear dependent st_dhg.
        clear dependent st_dhg'.
        clear dependent c1_dhg.
        clear dependent c2_dhg.
        clear dependent gvars.
        clear dependent c2_dhg'.
        remember (c2_hg, st_hg) as p.
        remember (c2_hg', st_hg') as p'.
        generalize dependent c2_hg.
        generalize dependent st_hg.
        induction H_step_2hg; intros; subst.
        -- invert Heqp.
           constructor.
        -- destruct y as [c2_hg_m st_hg_m].
           specialize (IHH_step_2hg eq_refl st_hg_m c2_hg_m eq_refl).
           econstructor.
           ++ apply CS_Par2.
              eassumption.
           ++ assumption.
    + clear IHH_remove_gvars1 IHH_remove_gvars2.
      invert H_remove_gvars1; invert H_remove_gvars2.
      * exists <{ skip }>, st_hg.
        repeat split; try solve [constructor]; try assumption.
        right.
        split; try reflexivity.
        apply multi_R.
        constructor.
      * exists <{ skip }>, (g !-> aeval st_hg a ; st_hg).
        repeat split; try solve [constructor].
        -- apply differ_trans with st_hg; try assumption.
           apply differ_symm.
           apply t_update_gvar.
           assumption.
        -- right.
           split; try reflexivity.
           econstructor.
           ++ apply CS_Par2.
              constructor.
           ++ apply multi_R.
              constructor.
      * exists <{ skip }>, (g !-> aeval st_hg a ; st_hg).
        repeat split; try solve [constructor].
        -- apply differ_trans with st_hg; try assumption.
           apply differ_symm.
           apply t_update_gvar.
           assumption.
        -- right.
           split; try reflexivity.
           econstructor.
           ++ apply CS_Par1.
              constructor.
           ++ apply multi_R.
              constructor.
      * exists <{ skip }>, (g0 !-> aeval (g !-> aeval st_hg a ; st_hg) a0 ; (g !-> aeval st_hg a ; st_hg)).
        repeat split; try solve [constructor].
        -- apply differ_trans with st_hg; try assumption.
           apply differ_trans with (g !-> aeval st_hg a ; st_hg).
           ++ apply differ_symm.
              apply t_update_gvar.
              assumption.
           ++ apply differ_symm.
              apply t_update_gvar.
              assumption.
        -- right.
           split; try reflexivity.
           econstructor. {
             apply CS_Par1.
             constructor.
           }
           econstructor. {
             apply CS_Par2.
             constructor.
           }
           apply multi_R.
           constructor.
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
    destruct IHC_dhg as [c_hg' [st_hg' [C_hg [H_remove_gvars' [H_differ' [H_assumption_hg H_sat_guar_dhg ] ] ] ] ] ].
    assert (exists c_hg'' st_hg'',
        <(gvars)> c_hg'' ~> c_dhg'' /\
        <<gvars>> st_hg'' ~ st_dhg'' /\
        (
          (c_hg' / st_hg' --> c_hg'' / st_hg'' /\ (st_hg' = st_hg'' -> st_dhg' = st_dhg'')) \/
          (c_hg' / st_hg' -->* c_hg'' / st_hg'' /\ st_dhg' = st_dhg'')
        )) as [c_hg'' [st_hg'' [H_remove_gvars'' [H_differ'' [ [H_step_hg H_eq_down] | [H_step_hg H_st_dhg'_st_dhg''] ] ] ] ] ]. {
      apply step_add_gvars with c_dhg'; try assumption.
      eapply fcomp_npia.
      - apply C_dhg.
      - assumption.
    }
    + set (C_hg' := fcomp_cmp c_hg st_hg c_hg' st_hg' c_hg'' st_hg'' H_step_hg C_hg).
      exists c_hg'', st_hg'', C_hg'.
      assert (H_assumption_hg' : fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg'). {
        simpl.
        assumption.
      }
      apply H_valid_hg in H_assumption_hg' as H_conclusion_hg'.
      destruct H_conclusion_hg' as [H_sat_guar_hg' H_postcondition_hg'].
      simpl in H_sat_guar_hg'.
      destruct H_sat_guar_hg' as [H_guar_step_hg' H_sat_guar_hg].
      repeat split; try assumption.
      destruct H_guar_step_hg' as [H_st_hg'_st_hg'' | H_guar_step_hg']; try (left; apply H_eq_down; assumption).
      right.
      rewrite Exists_exists in *.
      destruct H_guar_step_hg' as [ [A c] [H_In_G [H_A_st_hg' H_steps] ] ].
      exists (A, c).
      unfold guar_havoc_gvars in H_G_havoc.
      rewrite Forall_forall in H_G_havoc.
      specialize (H_G_havoc (A, c) H_In_G).
      destruct H_G_havoc as [H_A_dhg H_c_havoc].
      repeat split; try assumption.
      * apply H_A_dhg with st_hg'; try assumption.
        apply differ_symm.
        assumption.
      * unfold com_havoc_gvars in H_c_havoc.
        apply H_c_havoc with st_hg' st_hg''; assumption.
    + assert (exists (C_hg' : fcomp c_hg st_hg c_hg'' st_hg''), fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg') as [C_hg' H_assumption_hg']. {
        eapply fcomp_app_steps; eassumption.
      }
      exists c_hg'', st_hg'', C_hg'.
      apply H_valid_hg in H_assumption_hg' as H_conclusion_hg'.
      destruct H_conclusion_hg' as [H_sat_guar_hg' H_postcondition_hg'].
      repeat split; try assumption.
      left.
      assumption.
  - rename c into c_dhg.
    rename st into st_dhg.
    rename c' into c_dhg'.
    rename st' into st_dhg'.
    rename st'' into st_dhg''.
    destruct H_assumption_dhg as [H_rely_step_dhg H_assumption_dhg].
    specialize (IHC_dhg H_npia H_differ H_assumption_dhg c_hg H_remove_gvars H_valid_hg).
    destruct IHC_dhg as [c_hg' [st_hg' [C_hg [H_remove_gvars' [H_differ' [H_assumption_hg H_sat_guar_dhg] ] ] ] ] ].
    destruct (H_R_hg st_dhg'') as [st_hg'' [H_differ'' H_R_hg_st_hg''] ].
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
      * rewrite Forall_forall in H_R_hg_st_hg''.
        specialize (H_R_hg_st_hg'' r H_In_R_hg).
        apply H_R_hg_st_hg''.
        exists st_hg'.
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
  destruct (H_P_restrict st_dhg) as [st_hg [H_differ H_precondition_hg] ].
  assert (exists c_hg' st_hg' (C_hg : fcomp c_hg st_hg c_hg' st_hg'),
        <(gvars)> c_hg' ~> c_dhg' /\
        <<gvars>> st_hg' ~ st_dhg' /\
        fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg /\
        fcomp_sat_guar G C_dhg) as [c_hg' [st_hg' [C_hg [H_remove_gvars' [H_differ' [H_assumption_hg H_sat_guar_dhg] ] ] ] ] ]. {
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
  invert H_remove_gvars'.
  - apply H_valid in H_assumption_hg as H_conclusion_hg.
    destruct H_conclusion_hg as [H_sat_guar_hg H_postcondition_hg].
    apply H_postcondition_hg.
    reflexivity.
  - set (C_hg' := fcomp_cmp c_hg st_hg <{ g := a }> st_hg' <{ skip }> (g !-> aeval st_hg' a ; st_hg') (CS_Asgn st_hg' g a) C_hg).
    assert (H_assumption_hg' : fcomp_assumption ({{ P_dhg /\ P_hg }}) (R_dhg ++ R_hg) C_hg'). {
      simpl.
      assumption.
    }
    apply H_valid in H_assumption_hg' as H_conclusion_hg'.
    destruct H_conclusion_hg' as [H_sat_guar_hg' H_postcondition_hg'].
    specialize (H_postcondition_hg' eq_refl).
    apply H_Q_dhg with (g !-> aeval st_hg' a ; st_hg'); try assumption.
    apply t_update_gvar.
    assumption.
Qed.


(* Examples *)

Definition a : string := "a".
Definition b : string := "b".

Example example1 :
  |= 
    (
      X := 1;
      a := Y
    ) ||
    (
      Y := 1;
      b := X
    )
  sat (
    {{ ~(a = 0) }},
    [
      {{ ~(a = 0) }};
      {{ ~(X = 0) }};
      {{ True }};
      {{ ~(Y = 0) }};
      {{ ~(Y = 0) /\ (~(a = 0) \/ (b = X))}};
      {{ ~(a = 0) \/ ~(b = 0) }}
    ],
    [
      ({{ ~(a = 0) }}, <{ X := 1 }>);
      ({{ ~(X = 0) }}, <{ a := Y }>);
      ({{ True }}, <{ Y := 1 }>);
      ({{ ~(Y = 0) }}, <{ b := X }>)
    ],
    {{ ~(a = 0) \/ ~(b = 0) }}).
Proof.
  apply phoare_sound.
  apply PH_Consequence with
    (P' := {{ ~(a = 0) }})
    (R' :=
      [
        {{ ~(a = 0) }};
        {{ ~(a = 0) \/ ~(b = 0) }}
      ] ++
      [
        {{ ~(a = 0) }};
        {{ ~(X = 0) }};
        {{ ~(X = 0) }};
        {{ ~(X = 0) }}
      ] ++
      [
        {{ True }};
        {{ ~(Y = 0) }};
        {{ ~(Y = 0) }};
        {{ ~(Y = 0) /\ (~(a = 0) \/ (b = X))}}
      ]
    )
    (G' := 
      [
        ({{ ~(a = 0) }}, <{ X := 1 }>);
        ({{ ~(X = 0) }}, <{ a := Y }>)
      ] ++
      [
        ({{ True }}, <{ Y := 1 }>);
        ({{ ~(Y = 0) }}, <{ b := X }>)
      ]
    )
    (Q' := {{ ~(a = 0) \/ ~(b = 0) }});
    try auto.
  - apply incl_weaker_rely.
    unfold incl.
    intros P H_In.
    simpl in *.
    repeat (destruct H_In as [H_eq_P | H_In]; try auto 7).
  - repeat (constructor; try auto 8).
  - apply PH_Par with
      (P1 := {{ ~(a = 0) }})
      (P2 := {{ True }})
      (Q1 := {{ ~(X = 0) }})
      (Q2 := {{ ~(Y = 0) /\ (~(a = 0) \/ (b = X))}});
      try auto.
    + replace ([
        {{ ~(a = 0) }};
        {{ ~(X = 0) }};
        {{ ~(X = 0) }};
        {{ ~(X = 0)}}
      ]) with (
        [{{ ~(a = 0) }}; {{ ~(X = 0) }}] ++
        [{{ ~(X = 0) }}; {{ ~(X = 0) }}]
      ) by reflexivity.
      replace ([
        ({{ ~(a = 0) }}, <{ X := 1 }>);
        ({{ ~(X = 0) }}, <{ a := Y }>)
      ]) with (
        [({{ ~(a = 0) }}, <{ X := 1 }>)] ++
        [({{ ~(X = 0) }}, <{ a := Y }>)]
      ) by reflexivity.
      apply PH_Seq with (M := {{ ~(X = 0) }}).
      * apply PH_Assgn.
        auto.
      * apply PH_Assgn.
        auto.
    + replace ([
        {{ True }};
        {{ ~(Y = 0) }};
        {{ ~(Y = 0) }};
        {{ ~(Y = 0) /\ (~(a = 0) \/ (b = X))}}
      ]) with (
        [{{ True }}; {{ ~(Y = 0) }}] ++
        [{{ ~(Y = 0)}}; {{ ~(Y = 0) /\ (~(a = 0) \/ (b = X))}}]
      ) by reflexivity.
      replace ([
        ({{ True }}, <{ Y := 1 }>);
        ({{ ~(Y = 0) }}, <{ b := X }>)
      ]) with (
        [({{ True }}, <{ Y := 1 }>)] ++
        [({{ ~(Y = 0) }}, <{ b := X }>)]
      ) by reflexivity.
      apply PH_Seq with (M := {{ ~(Y = 0) }}).
      * apply PH_Assgn.
        auto.
      * apply PH_Assgn.
        auto.
    + simpl.
      intros st [H_X_neq_0 [H_Y_neq_0 H_a_b]].
      destruct H_a_b as [H_a_neq_0 | H_b_X]; try (left; assumption).
      right.
      rewrite H_b_X.
      assumption.
    + admit.
    + admit.
Admitted.
