Require Import Ring.
Require Import Field.
Require Import Setoid.
Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.


Module Export DEFINITIONS.
  Variable (F V : Type) (r0 r1 : F) (radd rmul rsub : F -> F -> F) (ropp : F -> F).
  (*Variable (req : F -> F -> Prop).*)
  Variable (rdiv : F -> F -> F) (rinv : F -> F).

  Declare Scope field_scope.
  Delimit Scope field_scope with fieldsc.
  Open Scope field_scope.

  Global Notation "0" := r0 : field_scope.
  Global Notation "1" := r1 : field_scope.
  (*Global Infix "==r" := req (at level 90) : field_scope.*)
  Global Infix "+r" := radd (at level 50) : field_scope.
  Global Infix "*r" := rmul (at level 40) : field_scope.
  Global Infix "-r" := rsub (at level 50) : field_scope.
  Global Notation "-r" := ropp (at level 30) : field_scope.
  Global Infix "/r" := rdiv (at level 40) : field_scope.
  Global Notation "/r" := rinv (at level 30) : field_scope.

  Variable (vadd : V -> V -> V) (vsmult : F -> V -> V) (v0 : V).
  (*Variable (veq : V -> V -> Prop).*)

  Declare Scope vectorspace_scope.
  Delimit Scope vectorspace_scope with vecsc.
  Open Scope vectorspace_scope.

  Notation "0" := v0 : vectorspace_scope.
  (*Infix "==v" := veq (at level 90) : vectorspace_scope.*)
  Infix "+v" := vadd (at level 50) : vectorspace_scope.
  Infix "*v" := vsmult (at level 40) : vectorspace_scope.
  Definition vopp (x : V) : V := (-r 1) *v x.
  Notation "-v" := vopp (at level 30) : vectorspace_scope.

  (*1.19*)
  Record vectorspace_theory
    : Prop
    := mk_vst
         {
           vadd_comm : forall (x y : V), x +v y = y +v x;
           vadd_assoc : forall (x y z : V), (x +v y) +v z = x +v (y +v z);
           vadd_ident : forall (x : V), x +v 0 = x;
           vadd_inv : forall (x : V), exists (y : V), x +v y = 0;
           vsmult_ident : forall (x : V), 1 *v x = x;
           vdistr1 : forall (a : F) (x y : V), a *v (x +v y) = (a *v x) +v (a *v y);
           vdistr2 : forall (a b : F) (x : V), (a +r b) *v x = (a *v x) +v (b *v x);
         }.

  Record vec_eq_ext : Prop
    :=
      mk_veqe {
          vadd_ext : Proper (eq ==> eq ==> eq) vadd;
          vsmult_ext : Proper (eq ==> eq ==> eq) vsmult;
        }.

  Section MORPHISM.
    Variable (W G : Type) (w0 : W) (wadd : W -> W -> W) (wsmult : G -> W -> W).
    Variable (weqb : W -> W -> bool) (phi__W : W -> V) (phi__G : G -> F).
    Infix "+!" := wadd (at level 50).
    Infix "*!" := wsmult (at level 40).
    Infix "?=!" := weqb (at level 90).

    Record vectorspace_morph : Prop
      :=
        mk_vmorph {
            morph_v0 : phi__W w0 = 0;
            morph_vadd : forall u v, phi__W (u +! v) = phi__W u +v phi__W v;
            morph_vsmult : forall a v, phi__W (a *! v) = phi__G a *v phi__W v;
            morph_veq : forall u v, (u ?=! v) = true -> phi__W u = phi__W v;
          }.
  End MORPHISM.

  (*Identity is a morphism*)
  Variable Vsth : Equivalence (@eq V).
  Variable veqb : V -> V -> bool.

  Hypothesis morph_veq' : forall x y, (veqb x y) = true -> x = y.
  Definition IDphi__V (x : V) := x.
  Definition IDphi__F (x : F) := x.

  Lemma IDmorph : vectorspace_morph V F 0 vadd vsmult veqb IDphi__V IDphi__F.
  Proof.
    split; intros; compute; try reflexivity.
    apply morph_veq'; assumption.
  Qed.

End DEFINITIONS.

Module Type VECTORSPACE.
  Include DEFINITIONS.

  (*Delimit Scope field_scope with fieldsc.*)

  Variable Fth : field_theory 0%fieldsc 1 radd rmul rsub ropp rdiv rinv eq.
  Definition Rth := F_R Fth.

  Lemma Eqfsth : Equivalence (@eq F).
  Proof.
    split; compute; intros.
    - reflexivity.
    - rewrite H; reflexivity.
    - rewrite <- H in H0.
      apply H0.
    Qed.

  Lemma REq_ext : ring_eq_ext radd rmul ropp (@eq F).
  Proof.
    split; compute; intros; rewrite H; try (rewrite H0); reflexivity.
  Qed.

  Add Ring FRing : Rth.
  Add Field FField : Fth.

  (*Leibniz equality leads to a setoid theory and is extensional*)
  Lemma Eqvsth : Equivalence (@eq V).
  Proof.
    split; compute; intros.
    - reflexivity.
    - rewrite H.
      reflexivity.
    - rewrite <- H in H0.
      apply H0.
    Qed.

  Add Morphism vadd with signature (eq ==> eq ==> eq) as vadd_ext1.
  Proof.
    intros; reflexivity.
  Qed.

  Add Morphism vsmult with signature (eq ==> eq ==> eq) as vsmult_ext1.
  Proof.
    intros; reflexivity.
  Qed.

  Variable Vth : vectorspace_theory.

  Lemma radd_inv_zero (x : F) : x +r (-r x) = 0%fieldsc.
  Proof.
    destruct Rth.
    specialize (Ropp_def x).
    rewrite <- Ropp_def.
    reflexivity.
  Qed.

  Lemma ropp_zero_zero : -r 0%fieldsc = 0%fieldsc.
  Proof.
    ring.
  Qed.

  Lemma add_both_sides (u v w : V) : u = v -> w +v u = w +v v.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma subtract_both_sides (u v w : V) : w +v u = w +v v -> u = v.
  Proof.
    intros.
  Admitted.

  (*1.29*)
  Theorem zero_times_vector (x : V) :
    0%fieldsc *v x = 0.
  Proof.
    destruct Rth.
    rewrite <- (Radd_0_l 0%fieldsc).
    destruct Vth.
    rewrite (vdistr4 0%fieldsc 0%fieldsc x).
    specialize (vadd_inv0 (0%fieldsc *v x)).
    destruct vadd_inv0 as [y vadd_inv0].
    rewrite <- vadd_inv0.
    apply (add_both_sides _ _ (0%fieldsc *v x)).

  Admitted.

  (*1.30*)
  Theorem number_times_zero (a : F) :
    a *v 0 = 0.
  Proof.
    destruct Vth.

  Admitted.

  Theorem vsmult_distr (a b : F) (x : V) : a *v (b *v x) = (a *r b) *v x.
  Proof.
  Admitted.

  Lemma minus_one_squared : -r 1 *r -r 1 = 1.
  Proof.
    ring.
  Qed.

  (*exercise 1.B.1*)
  Theorem vopp_involutive (x : V) : -v (-v x) = x.
  Proof.
    unfold vopp.
    rewrite vsmult_distr.
    rewrite minus_one_squared.
    destruct Vth.
    apply vsmult_ident0.
  Qed.

End VECTORSPACE.
