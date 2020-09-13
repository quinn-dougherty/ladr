Require Import Reals.
Require Import Lra.
Local Open Scope R_scope.
Require Import Vector.
Require Import utils.


Theorem R_isring : ring_theory 0 1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  (* addition *)
  (* left identity *) apply Rplus_0_l.
  (* commutativity *) apply Rplus_comm.
  (* associativity *) intros; rewrite Rplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Rmult_1_l.
  (* commutativity *) apply Rmult_comm.
  (* associativity *) intros; rewrite Rmult_assoc; easy.
  (* distributivity *) apply Rmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Rplus_opp_r.
Qed.

Instance Rring : Ring R :=
  {
  r0 := 0;
  r1 := 1;
  radd := Rplus;
  rmult := Rmult;
  rainv := Ropp;
  rminus := Rminus;
  req := eq;
  isring := R_isring;
  }.



Theorem R_isfield : field_theory R0 R1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof.
  constructor.
  (* ring axioms *) apply R_isring.
  (* 0 <> 1 *) apply R1_neq_R0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Rinv_l.
Qed.

Instance Rfield : Field R :=
  {
  fdiv := Rdiv;
  finv := Rinv;
  isfield := R_isfield;
  }.

Definition Rscalar_mult {A : Type} `{Field A} {n : nat}
           (k : R) (xs : t R n) :=
  map (fun x => rmult k x) xs.

Definition Raddition {A : Type} `{Field A} {n : nat}
           (xs ys : t R n) :=
  zipwith radd xs ys.


Theorem Raddition_commu {n : nat}
        (xs ys : t R n) : Raddition xs ys = Raddition ys xs.
Proof.
  unfold Raddition; apply zipwith_commu.
  intros a b; simpl; lra.
Qed.

Definition additive_inverse {A : Type} `{Field A} {n : nat} (x : t A n) : t A n :=
  map rainv x.


Fixpoint Vzero {F : Type} `{Ring F} (n : nat) : t F n :=
  match n with
  | 0 => nil F
  | S n' => cons F r0 n' (Vzero n')
  end.


Theorem R2_isvectorspace : vectorspace_theory Rscalar_mult Raddition (@Vzero R Rring 2).
Proof.
  split; intros.
  - apply Raddition_commu.
  - split; intros.
Admitted.


Instance R2 : VectorSpace R (t R 2) :=
  {
  vscalar_mult := Rscalar_mult;
  vaddition := Raddition;
  v0 := Vzero 2;
  isvectorspace := R2_isvectorspace;
  }.
