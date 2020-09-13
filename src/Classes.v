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
  isring : ring_theory r0 r1 radd rmult rminus rainv eq;
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
  (forall (x : V), vaddition x v0 = x) /\
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

Ltac unpack_vectorspace H1 :=
  destruct H1;
  inversion isvectorspace0 as [H21 [H22 [H23 [H24 [H25 [H26 H27]]]]]].

Ltac unpack_ring H :=
  destruct H; inversion isring0.

Ltac vby_definition H1 :=
  unpack_vectorspace H1;
  simpl;
  easy.

Lemma vaddition_assoc (u v w : V) : (u ⨥ v) ⨥ w = u ⨥ (v ⨥ w).
Proof.
  vby_definition H1.
Qed.

Lemma vaddition_commu (u v : V) : u ⨥ v = v ⨥ u.
Proof.
  vby_definition H1.
Qed.

Lemma vaddition_ident (v : V) : v ⨥ v0 = v.
Proof.
  vby_definition H1.
Qed.

Lemma vaddition_inverse (v : V) : exists (w : V), v ⨥ w = v0.
Proof.
  unpack_vectorspace H1.
  specialize (H24 v).
  destruct H24 as [w H24].
  exists w.
  easy.
Qed.

Lemma vmultiplicative_identity (v : V) : r1 * v = v.
Proof.
  vby_definition H1.
Qed.

Lemma vdistributive1 (a : F) (u v : V) : a * (u ⨥ v) = a * u ⨥ a * v.
Proof.
  vby_definition H1.
Qed.

Lemma vdistributive2 (a b : F) (v : V) : (a + b) * v = a * v ⨥ b * v.
Proof.
  vby_definition H1.
Qed.

Lemma radd_inv_zero (x : F) : x + rainv x = r0.
Proof.
  destruct H.
  destruct isring0.
  simpl.
  rewrite (Ropp_def x).
  reflexivity.
Qed.

Theorem zero_times_vector (v : V) :
  r0 * v = v0.
Proof.
  simpl.
  unpack_ring H.
  rewrite <- (Radd_0_l r0).
  simpl.
Admitted.

Lemma vadd_inverse_zero (v : V) : v ⨥ ⨪ v = v0.
Proof.
  unfold vainv.
  rewrite <- vmultiplicative_identity with (v:=v) at 1.
  rewrite <- vdistributive2 with (b:=rainv r1).
  rewrite radd_inv_zero.
  apply zero_times_vector.
Qed.

Lemma cancel_vadditive1 (u v : V) : u = v -> u ⨥ (⨪ u) = v ⨥ (⨪ u).
Proof.
  intros H2.
  subst.
  reflexivity.
Qed.

Lemma add_v_to_both_sides1 (u v : V) : forall w, u = v -> w ⨥ u = w ⨥ v.
Proof.
  intros; subst; reflexivity.
Qed.

Lemma add_v_to_both_sides2 (u v : V) : forall w, w ⨥ u = w ⨥ v -> u = v.
Proof.
  intros.
  apply add_v_to_both_sides1 with (w:= ⨪ w) in H2.
  rewrite <- vaddition_assoc in H2.
  rewrite vaddition_commu with (u:= ⨪ w)in H2.
  simpl.
Admitted.


(*
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
  assert (G : minus_v' = ⨪ v). give_up.
  rewrite <- G.
  rewrite H24.
  destruct H23 as [v0' H23].
  specialize (H23 u).
  rewrite (H21 u v1).
  assert (G' : v0' = v1). give_up.
  rewrite <- G'.
  rewrite H23.
  reflexivity.
Admitted.
*)


Lemma vaddition_injective (v : V) : forall u w : V, v ⨥ u = v ⨥ w -> u = w.
Proof.
  intros u w H2.
  rewrite (add_v_to_both_sides2 u w v); easy.
Qed.

Theorem unique_vadditive_identity (v v0' : V) (H2 : forall u, u ⨥ v0' = u) : v0' = v0.
Proof.
  specialize (H2 v0).
  rewrite <- H2.
  rewrite vaddition_commu.
  rewrite vaddition_ident.
  reflexivity.
Qed.

Lemma unique_vadditive_identity' (v v0' : V) : v ⨥ (⨪ v) = v0' -> v0' = v0.
Proof.
  intros H2.
  subst.
Admitted.

Theorem unique_vadditive_inverse
        (*        (v z' : V) : v ⨥ ((- r1) * v) = z' -> v0 = z'. *)
        (v : V) : forall (w w' : V) (H__w : v ⨥ w = v0) (H__w' : v ⨥ w' = v0),
    w = w'.
Proof.
  intros.
  rewrite <- H__w' in H__w.
  apply vaddition_injective in H__w.
  apply H__w.
Qed.


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
