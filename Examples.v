Set Warnings "-notation-overridden".
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From PLF Require Import Maps.
From PLF Require Import Hoare.
From PLF Require Import Hoare2.
From PLF Require Import Semantics.
From PLF Require Import Soundness.
From PLF Require Import GhostVar.


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
    {{ a <> 0 }},
    [
      {{ a <> 0 }};
      {{ X <> 0 }};
      {{ True }};
      {{ Y <> 0 }};
      {{ Y <> 0 /\ (a <> 0 \/ b = X)}};
      {{ a <> 0 \/ b <> 0 }}
    ],
    [
      ({{ a <> 0 }}, <{ X := 1 }>);
      ({{ X <> 0 }}, <{ a := Y }>);
      ({{ True }}, <{ Y := 1 }>);
      ({{ Y <> 0 }}, <{ b := X }>)
    ],
    {{ a <> 0 \/ b <> 0 }}).
Proof.
  apply phoare_sound.
  apply PH_Consequence with
    (P' := {{ a <> 0 }})
    (R' :=
      [
        {{ a <> 0 }};
        {{ a <> 0 \/ b <> 0 }}
      ] ++
      [
        {{ a <> 0 }};
        {{ X <> 0 }};
        {{ X <> 0 }};
        {{ X <> 0 }}
      ] ++
      [
        {{ True }};
        {{ Y <> 0 }};
        {{ Y <> 0 }};
        {{ Y <> 0 /\ (a <> 0 \/ b = X)}}
      ]
    )
    (G' := 
      [
        ({{ a <> 0 }}, <{ X := 1 }>);
        ({{ X <> 0 }}, <{ a := Y }>)
      ] ++
      [
        ({{ True }}, <{ Y := 1 }>);
        ({{ Y <> 0 }}, <{ b := X }>)
      ]
    )
    (Q' := {{ a <> 0 \/ b <> 0 }});
    try auto.
  - apply incl_weaker_rely.
    unfold incl.
    intros P H_In.
    simpl in *.
    repeat (destruct H_In as [H_eq_P | H_In]; try auto 7).
  - repeat (constructor; try auto 8).
  - apply PH_Par with
      (P1 := {{ a <> 0 }})
      (P2 := {{ True }})
      (Q1 := {{ X <> 0 }})
      (Q2 := {{ Y <> 0 /\ (a <> 0 \/ b = X)}});
      try auto.
    + replace ([
        {{ a <> 0 }};
        {{ X <> 0 }};
        {{ X <> 0 }};
        {{ X <> 0}}
      ]) with (
        [{{ a <> 0 }}; {{ X <> 0 }}] ++
        [{{ X <> 0 }}; {{ X <> 0 }}]
      ) by reflexivity.
      replace ([
        ({{ a <> 0 }}, <{ X := 1 }>);
        ({{ X <> 0 }}, <{ a := Y }>)
      ]) with (
        [({{ a <> 0 }}, <{ X := 1 }>)] ++
        [({{ X <> 0 }}, <{ a := Y }>)]
      ) by reflexivity.
      apply PH_Seq with (M := {{ X <> 0 }}).
      * apply PH_Assgn.
        auto.
      * apply PH_Assgn.
        auto.
    + replace ([
        {{ True }};
        {{ Y <> 0 }};
        {{ Y <> 0 }};
        {{ Y <> 0 /\ (a <> 0 \/ b = X)}}
      ]) with (
        [{{ True }}; {{ Y <> 0 }}] ++
        [{{ Y <> 0 }}; {{ Y <> 0 /\ (a <> 0 \/ b = X)}}]
      ) by reflexivity.
      replace ([
        ({{ True }}, <{ Y := 1 }>);
        ({{ Y <> 0 }}, <{ b := X }>)
      ]) with (
        [({{ True }}, <{ Y := 1 }>)] ++
        [({{ Y <> 0 }}, <{ b := X }>)]
      ) by reflexivity.
      apply PH_Seq with (M := {{ Y <> 0 }}).
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

Lemma H_Consequence_pre
    P P' Q c
    (H_valid : |- {{ P' }} c {{ Q }})
    (H_implies : P ->> P') :
      |- {{ P }} c {{ Q }}.
Proof.
  eapply H_Consequence.
  - eassumption.
  - assumption.
  - auto.
Qed.

(* Example is taken from the paper "Owicki-Gries Reasoning for Weak Memory Models" by Ori Lahav and Viktor Vafeiadis, Fig. 11 (page 11). *)
Example example2 :
  exists R G,
  |= X := X + 1 || X := X + 1 sat ({{ X = 0 }}, R, G, {{ X = 2 }}).
Proof.
  assert (H_X_not_gvar : ~ In X [Y]). {
    intros []; try assumption.
    discriminate.
  }
  assert (H_Y_neq_X : Y <> X). {
    intros C.
    discriminate.
  }
  assert (H_X_neq_Y : X <> Y). {
    intros C.
    discriminate.
  }

  eexists.
  eexists.
  eapply ghost_variable_rule with
    (gvars := [Y])
    (P_hg := {{ Y = 0 }})
    (R_dhg := [{{ X = 0 }}; {{ X = 1 }}; {{ X = 2 }}])
    (R_hg := [{{ Y = 0 }}; {{ Y = 1 }}; {{ Y = 2 }}; {{ Y = 3 }}])
    (G := [
      ({{ True }}, <{ havoc [Y] ; (Y := Y + 1 ; X := X + 1) ; havoc [Y] }>);
      ({{ True }}, <{ havoc [Y] ; (Y := Y + 2 ; X := X + 1) ; havoc [Y] }>)
    ]).
  - repeat constructor.
  - unfold assertion_dhg.
    intros st st' H_differ.
    specialize (H_differ X).
    destruct H_differ; try solve [exfalso; auto].
    verify_assertion.
  - unfold assertion_doesnt_restrict.
    intros st.
    exists (Y !-> 0 ; st).
    verify_assertion.
    apply t_update_gvar.
    left.
    reflexivity.
  - simpl.
    repeat (constructor; try solve [
      intros st st' H_differ;
      specialize (H_differ X);
      destruct H_differ; try solve [exfalso; auto];
      rewrite H;
      reflexivity
    ]).
  - unfold rely_doesnt_restrict.
    intros st st'.
    exists (Y !-> st Y ; st').
    split; try (apply t_update_gvar; left; reflexivity).
    simpl.
    repeat (constructor; try solve [
      rewrite t_update_eq;
      auto
    ]).
  - unfold guar_havoc_gvars.
    repeat (constructor; try solve [
      unfold assertion_dhg;
      split; try (intros; reflexivity);
      apply havoc_com_havoc_gvars
    ]).
  - unfold assertion_dhg.
    intros st st' H_differ.
    specialize (H_differ X).
    destruct H_differ; try solve [exfalso; auto].
    verify_assertion.
  - eapply GPar; eapply GAtomicAsgn; eapply GSeqSkip1.
    + apply GAsgnGhost.
      left.
      reflexivity.
    + constructor; try assumption.
      constructor; constructor.
      assumption.
    + apply GAsgnGhost.
      left.
      reflexivity.
    + constructor; try assumption.
      constructor; constructor.
      assumption.
  - apply phoare_sound.
    apply PH_Consequence with
      (P' := {{ X = 0 /\ Y = 0 }})
      (R' := [
        {{ X = 0 /\ Y = 0 }};
        {{ X = 2 }}
      ] ++ [
        {{ (X = 0 /\ Y = 0) \/ (X = 1 /\ Y = 2) }};
        {{ (X = 1 /\ Y = 1) \/ (X = 2 /\ Y = 3) }}
      ] ++ [
        {{ (X = 0 /\ Y = 0) \/ (X = 1 /\ Y = 1) }};
        {{ (X = 1 /\ Y = 2) \/ (X = 2 /\ Y = 3) }}
      ])
      (G' :=
        [({{ (X = 0 /\ Y = 0) \/ (X = 1 /\ Y = 2) }}, <{ Y := Y + 1 ; X := X + 1 }>)] ++
        [({{ (X = 0 /\ Y = 0) \/ (X = 1 /\ Y = 1) }}, <{ Y := Y + 2 ; X := X + 1 }>)]
      )
      (Q' := {{ X = 2 }}).
    + auto.
    + unfold stronger_rely.
      simpl.
      repeat (constructor; try solve [
        intros st st' H_st H;
        invert H;
        invert H3;
        invert H4;
        invert H5;
        invert H6;
        invert H7;
        invert H8;
        invert H9;
        lia
      ]).
    + unfold weaker_guar.
      simpl.
      constructor. {
        constructor.
        split.
        - apply havoc_com_havoc_semantics.
        - auto.
      }
      constructor. {
        apply Exists_cons_tl.
        constructor.
        split.
        - apply havoc_com_havoc_semantics.
        - auto.
      }
      constructor.
    + auto.
    + apply PH_Par with
        (P1 := {{ (X = 0 /\ Y = 0) \/ (X = 1 /\ Y = 2)}})
        (P2 := {{ (X = 0 /\ Y = 0) \/ (X = 1 /\ Y = 1)}})
        (Q1 := {{ (X = 1 /\ Y = 1) \/ (X = 2 /\ Y = 3)}})
        (Q2 := {{ (X = 1 /\ Y = 2) \/ (X = 2 /\ Y = 3)}}); simpl.
      * apply PH_Atomic.
        eapply H_Seq.
        -- apply H_Asgn.
        -- eapply H_Consequence_pre; try apply H_Asgn.
           verify_assertion.
      * apply PH_Atomic.
        eapply H_Seq.
        -- apply H_Asgn.
        -- eapply H_Consequence_pre; try apply H_Asgn.
           verify_assertion.
      * verify_assertion.
      * verify_assertion.
      * unfold non_interfering.
        repeat (constructor; try solve [
          constructor; try solve [constructor];
          eapply H_Seq;
          try apply H_Asgn;
          eapply H_Consequence_pre;
          try apply H_Asgn;
          verify_assertion
        ]).
      * unfold non_interfering.
        repeat (constructor; try solve [
          constructor; try solve [constructor];
          eapply H_Seq;
          try apply H_Asgn;
          eapply H_Consequence_pre;
          try apply H_Asgn;
          verify_assertion
        ]).
Qed.
