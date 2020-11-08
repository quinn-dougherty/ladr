Require Import Ring.
Require Import Field.
Require Import Setoid.
Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.
Require Import Ensembles.
Require Import Vector.

Section DEFINITIONS.
  Variable (F V : Type) (r0 r1 : F) (radd rmul rsub : F -> F -> F) (ropp : F -> F) (req : F -> F -> Prop).
  Variable (rdiv : F -> F -> F) (rinv : F -> F).

  Declare Scope field_scope.
  Delimit Scope field_scope with fieldsc.
  Open Scope field_scope.

  Notation "0" := r0 : field_scope.
  Notation "1" := r1 : field_scope.
  Infix "==r" := req (at level 90) : field_scope.
  Infix "+r" := radd (at level 50) : field_scope.
  Infix "*r" := rmul (at level 40) : field_scope.
  Infix "-r" := rsub (at level 50) : field_scope.
  Notation "-r" := ropp (at level 30) : field_scope.
  Infix "/r" := rdiv (at level 40) : field_scope.
  Notation "/r" := rinv (at level 30) : field_scope.

  Variable (vadd : V -> V -> V) (vsmult : F -> V -> V) (v0 : V) (veq : V -> V -> Prop).

  Declare Scope vectorspace_scope.
  Delimit Scope vectorspace_scope with vecsc.
  Open Scope vectorspace_scope.

  Notation "0" := v0 : vectorspace_scope.
  Infix "==v" := veq (at level 90) : vectorspace_scope.
  Infix "+v" := vadd (at level 50) : vectorspace_scope.
  Infix "*v" := vsmult (at level 40) : vectorspace_scope.

  (*1.19*)
  Record vectorspace_theory
    : Prop
    := mk_vst
         {
           vadd_comm : forall (x y : V), x +v y ==v y +v x;
           vadd_assoc : forall (x y z : V), (x +v y) +v z ==v x +v (y +v z);
           vadd_ident : forall (x : V), x +v 0 ==v x;
           vadd_inv : forall (x : V), exists (y : V), x +v y ==v 0;
           vsmult_ident : forall (x : V), r1 *v x ==v x;
           vdistr1 : forall (a : F) (x y : V), a *v (x +v y) ==v (a *v x) +v (a *v y);
           vdistr2 : forall (a b : F) (x : V), (a +r b) *v x ==v (a *v x) +v (b *v x);
         }.

  Record vec_eq_ext : Prop
    :=
      mk_veqe {
          vadd_ext : Proper (veq ==> veq ==> veq) vadd;
          vsmult_ext : Proper (req ==> veq ==> veq) vsmult;
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
            morph_vadd : forall u v, phi__W (u +! v) ==v phi__W u +v phi__W v;
            morph_vsmult : forall a v, phi__W (a *! v) ==v phi__G a *v phi__W v;
            morph_veq : forall u v, (u ?=! v) = true -> phi__W u ==v phi__W v;
          }.
  End MORPHISM.

  (*Identity is a morphism*)
  Variable Vsth : Equivalence veq.
  Variable veqb : V -> V -> bool.
  Hypothesis morph_veq : forall x y, (veqb x y) = true -> x ==v y.
  Definition IDphi__V (x : V) := x.
  Definition IDphi__F (x : F) := x.

  Lemma IDmorph : vectorspace_morph V F 0 vadd vsmult veqb IDphi__V IDphi__F.
  Proof.
    destruct Vsth.
    compute in Equivalence_Reflexive.
    split; intros; compute.
    - reflexivity.
    - apply Equivalence_Reflexive.
    - apply Equivalence_Reflexive.
    - apply morph_veq.
      apply H.
  Qed.

End DEFINITIONS.

Section VECTORSPACE.
  Variable (F V : Type).
  Variable (r0 r1 : F) (radd rmul rsub : F -> F -> F) (ropp : F -> F) (req : F -> F -> Prop).
  Variable (rdiv : F -> F -> F) (rinv : F -> F).

  Declare Scope field_scope.
  Delimit Scope field_scope with fieldsc.
  Open Scope field_scope.

  Notation "0" := r0 : field_scope.
  Notation "1" := r1 : field_scope.
  Infix "==r" := req (at level 90) : field_scope.
  Infix "+r" := radd (at level 50) : field_scope.
  Infix "*r" := rmul (at level 40) : field_scope.
  Infix "-r" := rsub (at level 50) : field_scope.
  Notation "-r" := ropp (at level 30) : field_scope.
  Infix "/r" := rdiv (at level 40) : field_scope.
  Notation "/r" := rinv (at level 30) : field_scope.

  Variable Rth : ring_theory 0 1 radd rmul rsub ropp req.
  Variable Fth : field_theory 0 1 radd rmul rsub ropp rdiv rinv req.
 
  Variable (vadd : V -> V -> V) (vsmult : F -> V -> V) (v0 : V) (veq : V -> V -> Prop).

  Declare Scope vectorspace_scope.
  Delimit Scope vectorspace_scope with vecsc.
  Open Scope vectorspace_scope.

  Notation "0" := v0 : vectorspace_scope.
  Infix "==v" := veq (at level 90) : vectorspace_scope.
  Infix "+v" := vadd (at level 50) : vectorspace_scope.
  Infix "*v" := vsmult (at level 40) : vectorspace_scope.

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

  Lemma Eq_ext : vec_eq_ext F V (@eq F) vadd vsmult (@eq V).
  Proof.
    split; compute; intros; rewrite H; rewrite H0; reflexivity.
  Qed.

  Variable Vsth : Equivalence veq.
  Variable Rsth : Equivalence req.

  Variable veqe : vec_eq_ext F V req vadd vsmult veq.

  Add Morphism vadd with signature (veq ==> veq ==> veq) as vadd_ext1.
  Proof.
    intros.
    destruct veqe.
    compute in vadd_ext0.
    specialize (vadd_ext0 x y H x0 y0 H0).
    apply vadd_ext0.
  Qed.

  Add Morphism vsmult with signature (req ==> veq ==> veq) as vsmult_ext1.
  Proof.
    intros.
    destruct veqe.
    compute in vsmult_ext0.
    specialize (vsmult_ext0 x y H x0 y0 H0).
    apply vsmult_ext0.
  Qed.

  Variable Vth : vectorspace_theory F V r0 radd vadd vsmult 0 veq.


  Lemma radd_inv_zero (x : F) : x +r (-r x) ==r 0%fieldsc.
  Proof.
    destruct Rth.
    specialize (Ropp_def x).
    rewrite <- Ropp_def.
    reflexivity.
  Qed.

  Lemma ropp_zero_zero : -r 0%fieldsc ==r 0%fieldsc.
  Proof.
    simpl.
  Admitted.

  (*1.29*)
  Theorem zero_times_vector (x : V) :
    0%fieldsc *v x ==v 0.
  Proof.
    destruct Rth.
    rewrite <- (Radd_0_l 0%fieldsc).
    destruct Vth.
    rewrite (vdistr4 0%fieldsc 0%fieldsc x).
    Admitted.
