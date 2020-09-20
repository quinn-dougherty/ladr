Require Import Ring.
Require Import Field.
Require Import Setoid.
Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.

Section VS.

(*Variable (A : Type).*)

Class Ring A :=
  {
  r0 : A;
  r1 : A;
  radd : A -> A -> A;
  rmult : A -> A -> A;
  rainv : A -> A;
  rminus : A -> A -> A;
  isring : ring_theory r0 r1 radd rmult rminus rainv eq;
  }.
(*
Context `{Ring A}.
*)
Class Field A `{Ring A} :=
  {
  fdiv : A -> A -> A;
  finv : A -> A;
  isfield : field_theory r0 r1 radd rmult rminus rainv fdiv finv eq;
  }.

Declare Scope field_scope.
Delimit Scope field_scope with fieldsc.
Open Scope field_scope.
Bind Scope field_scope with Field.
Infix "+" := radd : field_scope.
Infix "*" := rmult : field_scope.
Notation "- k" := rainv : field_scope.
Notation "/ k" := finv : field_scope.
Infix "/" := fdiv : field_scope.
(*
Definition vectorspace_theory' {F V : Type}
           (vscalar_mult : F -> V -> V)
           (vaddition : V -> V -> V)
           (v0 : V) : Prop :=
  (forall (x y : V), vaddition x y = vaddition y x) /\
  (forall (x y z : V), vaddition (vaddition x y) z = vaddition x (vaddition y z)) /\
  (forall (x : V), vaddition x v0 = x) /\
  (forall (x : V), exists (w : V), vaddition x w = v0) /\
  (forall (x : V), vscalar_mult r1 x = x) /\
  (forall (a : F) (x y : V), vscalar_mult a (vaddition x y) = vaddition (vscalar_mult a x) (vscalar_mult a y)) /\
  (forall (a b : F) (x : V), vscalar_mult (radd a b) x = vaddition (vscalar_mult a x) (vscalar_mult b x))
.
 *)

(*
Variable (F : Type).
Context `{Field F}.
*)

(*
Variable (v0' : V) (vadd : V -> V -> V) (vsmult : F -> V -> V) (veq : V -> V -> Prop).
Infix "⨥" := vadd (at level 50).
Infix "*" := vsmult.
Infix "==" := veq (at level 90).
 *)

Record vectorspace_theory {F V : Type} `{Field F}
       (vadd : V -> V -> V) (vsmult : F -> V -> V) (v0 : V) (veq : V -> V -> Prop)
  : Prop
  := mk_vst
       {
         vadd_comm : forall (x y : V), veq (vadd x y) (vadd y x);
         vadd_assoc : forall (x y z : V), veq (vadd (vadd x y) z) (vadd x (vadd y z));
         vadd_ident : forall (x : V), veq (vadd x v0) x;
         vadd_inv : forall (x : V), exists (w : V), veq (vadd x w) v0;
         vsmult_ident : forall (x : V), veq (vsmult r1 x) x;
         vdistr1 : forall (a : F) (x y : V), veq (vsmult a (vadd x y)) (vadd (vsmult a x) (vsmult a y));
         vdistr2 : forall (a b : F) (x : V), veq (vsmult (radd a b) x) (vadd (vsmult a x) (vsmult b x));
       }.


Class VectorSpace F `{Field F} V :=
  {
  vaddition : V -> V -> V;
  vscalar_mult : F -> V -> V;
  v0 : V;
  veq : V -> V -> Prop;
  isvectorspace : vectorspace_theory vaddition vscalar_mult v0 veq;
  }.


Declare Scope vectorspace_scope.
Delimit Scope vectorspace_scope with vecsc.
Open Scope vectorspace_scope.
Bind Scope vectorspace_scope with VectorSpace.
Variable (F V : Type).
Context `{VectorSpace F V}.

Definition vainv (v : V) :=
  vscalar_mult (rainv r1) v.

Definition vminus (u v : V) :=
  vaddition u (vainv v).

Infix "⨥" := vaddition (at level 50) : vectorspace_scope.
Infix "*" := vscalar_mult : vectorspace_scope.
Notation "⨪" := vainv : vectorspace_scope.
Infix "⨪" := vminus (at level 50) : vectorspace_scope.
Infix "==" := veq (at level 90) : vectorspace_scope.

Record vectorspace_eq_ext : Prop := mk_vseqe {
   vadd_ext : Proper (veq ==> veq ==> veq) vaddition;
   (*vsmult_ext : Proper (veq ==> veq) vscalar_mult;*)
   v0_ext : Proper veq v0;
 }.


Theorem veq_equiv_refl : forall (v : V), v == v.
  Admitted.

Theorem veq_equiv_symm : forall (u v : V), u == v -> v == u.
  Admitted.

Theorem veq_equiv_trans : forall (u v w : V), u == v -> v == w -> u == w.
  Admitted.

Instance VEqReflexive : Reflexive veq :=
  {
  reflexivity := veq_equiv_refl;
  }.

Instance VEqSymmetric : Symmetric veq :=
  {
  symmetry := veq_equiv_symm;
  }.

Instance VEqTransitive : Transitive veq :=
  {
  transitivity := veq_equiv_trans
  }.

Instance VEqEquiv : Equivalence veq :=
  {
  Equivalence_Reflexive := VEqReflexive;
  Equivalence_Symmetric := VEqSymmetric;
  Equivalence_Transitive := VEqTransitive;
  }.

Theorem veq_refl : forall (v : V), v == v.
Proof.
  intros.
  reflexivity.
Qed.

Theorem veq_symm : forall (u v : V), u == v -> v == u.
Proof.
  intros u v H2.
  rewrite H2.
  reflexivity.
Qed.

Theorem veq_trans : forall (u v w : V), u == v -> v == w -> u == w.
Proof.
  intros u v w H2 H3.
  rewrite H2.
  rewrite <- H3.
  reflexivity.
Qed.


Add Parametric Relation : V veq
  reflexivity proved by veq_refl
  symmetry proved by veq_symm
  transitivity proved by veq_trans
    as veq_equiv_rel.


Add Morphism vaddition with signature (veq ==> veq ==> veq) as vadd_ext1.
  intros.
  Admitted.




Ltac unpack_vectorspace H :=
  destruct H;
  inversion isvectorspace0.

Ltac unpack_ring H :=
  destruct H; inversion isring0.

Ltac vby_definition H :=
  destruct H;
  inversion isvectorspace0;
  simpl;
  easy.

Lemma vaddition_assoc (u v w : V) : (u ⨥ v) ⨥ w == u ⨥ (v ⨥ w).
Proof.
  vby_definition H1.
Qed.

Lemma vaddition_commu (u v : V) : u ⨥ v == v ⨥ u.
Proof.
  vby_definition H1.
Qed.

Lemma vaddition_ident (v : V) : v ⨥ v0 == v.
Proof.
  vby_definition H1.
Qed.

Lemma vaddition_inverse (v : V) : exists (w : V), v ⨥ w == v0.
Proof.
  unpack_vectorspace H1.
  specialize (vadd_inv0 v).
  destruct vadd_inv0 as [w vadd_inv0].
  exists w.
  apply vadd_inv0.
Qed.

Lemma vmultiplicative_identity (v : V) : r1 * v == v.
Proof.
  vby_definition H1.
Qed.

Lemma vdistributive1 (a : F) (u v : V) : a * (u ⨥ v) == a * u ⨥ a * v.
Proof.
  vby_definition H1.
Qed.

Lemma vdistributive2 (a b : F) (v : V) : (a + b) * v == a * v ⨥ b * v.
Proof.
  vby_definition H1.
Qed.

Lemma radd_inv_zero (x : F) : x + rainv x = r0.
Proof.
  unpack_ring H.
  simpl.
  rewrite (Ropp_def x).
  reflexivity.
Qed.

Theorem zero_times_vector (v : V) :
  r0 * v == v0.
Proof.
  unpack_ring H.
  rewrite <- (Radd_0_l r0).
  simpl.

Admitted.

Lemma vadd_inverse_zero (v : V) : v ⨥ ⨪ v == v0.
Proof.
  unfold vainv.
  rewrite <- vmultiplicative_identity at 1.
  rewrite vdistributive1.
  rewrite (vmultiplicative_identity (rainv r1 * v)).
  rewrite <- vdistributive2.
  rewrite radd_inv_zero.
  apply zero_times_vector.
Qed.

Lemma cancel_vadditive1 (u v : V) : u == v -> u ⨥ (⨪ u) == v ⨥ (⨪ u).
Proof.
  intros H2.
  rewrite vadd_inverse_zero.
 
Admitted.

Lemma add_to_both_sides1 (u v : V) : forall w, u == v -> w ⨥ u == w ⨥ v.
Proof.
  intros.
  rewrite H2.
  reflexivity.
Qed.

Lemma add_to_both_sides2 (u v : V) : forall w, w ⨥ u == w ⨥ v -> u == v.
Proof.
  intros.
  apply add_to_both_sides1 with (w:= ⨪ w) in H2.
  rewrite <- vaddition_assoc in H2; rewrite <- vaddition_assoc in H2 at 1.
  rewrite vaddition_commu with (u:=⨪ w) in H2.
  rewrite vadd_inverse_zero in H2.
  rewrite vaddition_commu in H2; rewrite vaddition_ident in H2.
  rewrite vaddition_commu in H2; rewrite vaddition_ident in H2.
  apply H2.
Qed.

Lemma add_to_both_sides (u v : V) : forall w, u == v <-> w ⨥ u == w ⨥ v.
Proof.
  split.
  - apply add_to_both_sides1.
  - apply add_to_both_sides2.
Qed.

Lemma vaddition_injective (v : V) : forall u w : V, v ⨥ u == v ⨥ w -> u == w.
Proof.
  intros u w H2.
  rewrite (add_to_both_sides2 u w v); easy.
Qed.

Theorem unique_vadditive_identity (v v0' : V) (H2 : forall u, u ⨥ v0' == u) : v0' == v0.
Proof.
  specialize (H2 v0).
  rewrite <- H2.
  rewrite vaddition_commu.
  rewrite vaddition_ident.
  reflexivity.
Qed.

Lemma unique_vadditive_identity' (v v0' : V) : v ⨥ (⨪ v) == v0' -> v0' == v0.
Proof.
  intros H2.
  subst.
  rewrite vadd_inverse_zero in H2.
  symmetry.
  apply H2.
Qed.

Theorem unique_vadditive_inverse
        (*        (v z' : V) : v ⨥ ((- r1) * v) = z' -> v0 = z'. *)
        (v : V) : forall (w w' : V) (H__w : v ⨥ w == v0) (H__w' : v ⨥ w' == v0),
    w == w'.
Proof.
  intros.
  rewrite <- H__w' in H__w.
  apply vaddition_injective in H__w.
  apply H__w.
Qed.


Theorem number_times_zero (a : F) :
  a * v0 = v0.
Proof.
  simpl.

Admitted.

Theorem minusone_times_vector (v : V) :
  (rainv r1) * v = ⨪ v.
Proof.
  unfold vainv.
  reflexivity.
Qed.

Theorem vainv_involutive (v : V) :
  ⨪ (⨪ v) = v.
Proof.
  unfold vainv.
Admitted.

Theorem zero_or (a : F) (u : V) :
  a * u = v0 -> a = r0 \/ u = v0.
Proof.
Admitted.

End VS.

Require Import Ensembles.

Section Subspaces.


Class Subspace {F V : Type} `{Field F} `{VectorSpace V} :=
  {
  additive_ident :
  }
