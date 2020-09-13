Require Import Ring.
Require Import Field.

Section VS.
Class Ring A :=
  {
  r0 : A;
  r1 : A;
  radd : A -> A -> A;
  rmult : A -> A -> A;
  rainv : A -> A;
  rminus : A -> A -> A;
  req : A -> A -> Prop;
  isring : ring_theory r0 r1 radd rmult rminus rainv req;
  }.

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

Definition vectorspace_theory {F V : Type} `{Field F}
           (vscalar_mult : F -> V -> V)
           (vaddition : V -> V -> V)
           (v0 : V) : Prop :=
  (forall (x y : V), vaddition x y = vaddition y x) /\
  (forall (x y z : V), vaddition (vaddition x y) z = vaddition x (vaddition y z)) /\
  (exists z : V, forall (x : V), vaddition z x = x) /\
  (forall (x : V), exists (w : V), vaddition x w = v0) /\
  (forall (x : V), vscalar_mult r1 x = x) /\
  (forall (a : F) (x y : V), vscalar_mult a (vaddition x y) = vaddition (vscalar_mult a x) (vscalar_mult a y)) /\
  (forall (a b : F) (x : V), vscalar_mult (radd a b) x = vaddition (vscalar_mult a x) (vscalar_mult b x))
.

Class VectorSpace F `{Field F} V :=
  {
  vscalar_mult : F -> V -> V;
  vaddition : V -> V -> V;
  v0 : V;
  isvectorspace : vectorspace_theory vscalar_mult vaddition v0;
  }.

Declare Scope vectorspace_scope.
Delimit Scope vectorspace_scope with vecs.
Open Scope vectorspace_scope.
Bind Scope vectorspace_scope with VectorSpace.
Context {F V : Type}.
Context `{VectorSpace F V}.

Definition vainv (v : V) :=
  vscalar_mult (rainv r1) v.

Infix "⨥" := vaddition (at level 50) : vectorspace_scope.
Infix "*" := vscalar_mult : vectorspace_scope.
Notation "⨪" := vainv : vectorspace_scope.

Lemma cancel_vadditive1 (u v : V) : u = v -> u ⨥ (⨪ u) = v ⨥ (⨪ u).
Proof.
  intros H2.
  subst.
  reflexivity.
Qed.


Lemma cancel_vadditive2 (u v w : V) : u ⨥ v = w -> u = w ⨥ (⨪ v).
Proof.
  intros H2.
  subst.
  destruct H1.
  simpl.
  inversion isvectorspace0 as [H21 [H22 [H23 [H24 [H25 [H26 H27]]]]]].
  rewrite (H22 u v (⨪ v)).
  specialize (H24 v).
  destruct H24 as [minus_v' H24].

  destruct (H24 (⨪ v)) as [w H24].

  specialize (H24 (rainv r1 * v)).
  destruct H24 as [w H24].
  rewrite (H21 v (rainv r1 * v)).


  rewrite H24.



Admitted.




Lemma addition_injective (v : V) : forall u w : V, v ⨥ u = v ⨥ w -> u = w.
Proof.
  intros u w H2.
  apply cancel_vadditive1 in H2.
  Admitted.

Theorem unique_vadditive_identity (v z' : V) : v ⨥ (⨪ v) = z' -> z' = v0.
Proof.
  intros H2.
  subst.
  destruct H1.
  inversion isvectorspace0 as [H21 [H22 [H23 [H24 [H25 [H26 H27]]]]]].
  destruct H23 as [v0' H23].

Admitted.



Theorem unique_vadditive_inverse
        (*        (v z' : V) : v ⨥ ((- r1) * v) = z' -> v0 = z'. *)
        (v : V) : forall (w w' : V) (H__w : v ⨥ w = v0) (H__w' : v ⨥ w' = v0),
    w = w'.
Proof.
  intros.
  rewrite <- H__w' in H__w.
  apply addition_injective in H__w.
  apply H__w.
Qed.


Theorem zero_times_vector (v : V) :
  r0 * v = v0.
Proof.
Admitted.

Theorem number_times_zero (a : F) :
  a * v0 = v0.
Proof.
Admitted.

Theorem minusone_times_vector (v : V) :
  vscalar_mult (rainv r1) v = ⨪ v.
Proof. Admitted.

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
