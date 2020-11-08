Require Import Ring.
Require Import Field.
Require Import Setoid.
Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.
Require Import Ensembles.
Require Import Vector.

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


Variable (F V : Type).
Context `{Field F}.
Variable vadd : V -> V -> V.
Variable vsmult : F -> V -> V.
Variable v0 : V.
Variable veq : V -> V -> Prop.

Infix "⨥" := vadd (at level 50).
Infix "*" := vsmult.
Notation "0" := v0.
Infix "==" := veq (at level 90).

(*1.19*)
Record vectorspace_theory
       (*(vadd : V -> V -> V) (vsmult : F -> V -> V) (v0 : V) (veq : V -> V -> Prop)*)
  : Prop
  := mk_vst
       {
         vadd_comm : forall (x y : V), x ⨥ y == y ⨥ x;
         vadd_assoc : forall (x y z : V), (x ⨥ y) ⨥ z == x ⨥ (y ⨥ z);
         vadd_ident : forall (x : V), x ⨥ 0 == x;
         vadd_inv : forall (x : V), exists (w : V), x ⨥ w == 0;
         vsmult_ident : forall (x : V), r1 * x == x;
         vdistr1 : forall (a : F) (x y : V), a * (x ⨥ y) == (a * x) ⨥ (a * y);
         vdistr2 : forall (a b : F) (x : V), (a + b) * x == (a * x) ⨥ (b * x);
       }.

(*vector equality is extensional*)
Record vec_eq_ext : Prop
  :=
    mk_veqe {
        vadd_ext : Proper (veq ==> veq ==> veq) vadd;
        vsmult_ext : Proper (eq ==> veq ==> veq) vsmult;
      }.

(*1.18*)
Class VectorSpace F `{Field F} V :=
  {
  vaddition : V -> V -> V;
  vscalar_mult : F -> V -> V;
  v0 : V;
  veq : relation V;
  isvectorspace : vectorspace_theory vaddition vscalar_mult v0 veq;
  }.

Declare Scope vectorspace_scope.
Delimit Scope vectorspace_scope with vecsc.
Open Scope vectorspace_scope.
Bind Scope vectorspace_scope with VectorSpace.

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

Record vectorspace_eq_ext : Prop
  :=
    mk_vseqe
      {
        vadd_ext : Proper ((fun u => fun v => u == v) ==> (fun u => fun v => u == v) ==> (fun u => fun v => u == v))
                          (fun u => fun v => u ⨥ v);
        vsmult_ext : Proper ((fun x => fun y => x = y) ==> (fun u => fun v => u == v) ==> (fun u => fun v => u == v))
                            (fun (a : F) => fun (v : V) => a * v);
        v0_ext : Proper (fun u => fun v => u == v) v0;
}.
Compute relation V.
Instance vadd_Proper (u v : V) :
  Proper (veq ==> veq ==> veq) vaddition.
Proof.
  unfold Proper.


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

Add Morphism vscalar_mult with signature (eq ==> veq ==> veq) as vsmult_ext1.
  intros.
  Admitted.


Ltac unpack_vectorspace H :=
  destruct H;
  inversion isvectorspace0.

Ltac unpack_ring H :=
  destruct H; inversion isring0.

Ltac unpack_field H :=
  destruct H; inversion isfield0.

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

(*1.29*)
Theorem zero_times_vector (v : V) :
  r0 * v == v0.
Proof.
  unpack_field H0.
  inversion F_R.
  rewrite <- (Radd_0_l r0).
  destruct H1; inversion isvectorspace0.
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

(*1.25*)
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

(*1.26*)
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

(*1.30*)
Theorem number_times_zero (a : F) :
  a * v0 == v0.
Proof.
  unpack_vectorspace H1.
  simpl.

Admitted.

(*1.31*)
Theorem minusone_times_vector (v : V) :
  (rainv r1) * v = ⨪ v.
Proof.
  unfold vainv.
  reflexivity.
Qed.

(*exercise 1.B.1*)
Theorem vainv_involutive (v : V) :
  ⨪ (⨪ v) = v.
Proof.
  unfold vainv.
  simpl.

Admitted.

(*exercise 1.B.2*)
Theorem zero_or (a : F) (u : V) :
  a * u = v0 -> a = r0 \/ u = v0.
Proof.
Admitted.

(*End VS.

Section Subspaces.
*)
Record Subspace :=
  {
    set__subspace : Ensemble V;
    additive_ident__subspace : set__subspace v0;
    closed_addition__subspace :
      forall (u w : V), set__subspace u -> set__subspace w -> set__subspace (u ⨥ w);
    closed_smult__subspace :
      forall (a : F) (u : V), set__subspace u -> set__subspace (a * u);
  }.

Definition biplus__subset (U W : Ensemble V) : Ensemble V :=
  fun v => exists (u w : V), U u -> W w -> v == u ⨥ w.

Definition empty_set : Ensemble V :=
  fun u => False.

Definition plus__subset {n : nat} (Un : t (Ensemble V) n) : Ensemble V :=
  fold_left biplus__subset empty_set Un.

Context (U W : Subspace).



Infix "∔" := (fun U1 => fun U2 => biplus__subset (set__subspace U1) (set__subspace U2)) (at level 50).



Definition bi_smallest_containing_subspace (U W : Subspace) : Prop :=
  Included V (set__subspace U) (U ∔ W) /\
  Included V (set__subspace W) (U ∔ W) /\
  (forall (X : Subspace),
      Included V (set__subspace U) (set__subspace X) ->
      Included V (set__subspace W) (set__subspace X) ->
      Included V (U ∔ W) (set__subspace X)).

Theorem smallest_containing_subspace2 : bi_smallest_containing_subspace U W.
Proof.
  unfold bi_smallest_containing_subspace, Included, Ensembles.In in *;
    intros;
    split;
    try split;
    intros.
  - unfold biplus__subset.
    exists x. exists v0.
    intros.
    rewrite vaddition_ident.
    reflexivity.
  - unfold biplus__subset.
    exists v0. exists x.
    intros.
    rewrite vaddition_commu.
    rewrite vaddition_ident.
    reflexivity.
  - unfold biplus__subset in H4; destruct H4 as [u [w H4]].
    inversion X as [X' zero_in_X X_closed_addition _].
    simpl.
Admitted.

Theorem singleton_zero_closed_addition (u w : V) : u == v0 -> w == v0 -> u ⨥ w == v0.
Proof.
  intros.
  rewrite H2.
  rewrite H3.
  rewrite vaddition_ident.
  reflexivity.
Qed.

Theorem singleton_zero_closed_smult (a : F) (u : V) : u == v0 -> a * u == v0.
Proof.
  intros.
Admitted.

Definition singleton_zero : Subspace :=
  {|
  set__subspace := fun v => v == v0 ;
  additive_ident__subspace := (veq_refl v0) ;
  closed_addition__subspace := singleton_zero_closed_addition ;
  closed_smult__subspace := singleton_zero_closed_smult
  |}.

Definition Directsum2'
           (U1 U2 : Subspace)
           (H : (forall (u1 u2 : V), set__subspace U1 u1 -> set__subspace U2 u2 ->
                                u1 ⨥ u2 = v0 -> (u1 == v0) /\ (u2 == v0)))
  : Subspace
  :=

    (*
      function subspace -> subspace -> subspace
      Proposition: subspace -> subspaces -> (a belief that zero can be written uniquely)
     *)

Record Directsum2 :=
  {
  U1 : Subspace;
  U2 : Subspace;
  zero_unique2 :
    forall (u1 u2 : V), set__subspace U1 u1 -> set__subspace U2 u2 ->
                   u1 ⨥ u2 = v0 -> (u1 == v0) /\ (u2 == v0)
  }.

(*1.45*)

Theorem direct_sum_of_two_subspaces (U W : Subspace) :
  Build_Directsum2 U W <-> Intersection V (set__subspace U) (set__subspace W) = singleton_zero.

Inductive even (n : nat) : Prop :=
| ev0 : even 0
| ev__SS (n : nat) : even n.


Record Directsum :=
  {
  n : nat;
  Un : t Subspace n;
  vn : t V n;
  zero_unique :

  }



    End VS.
