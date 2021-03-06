Require Import Ring.
Require Import Field.
Require Import Setoid.
Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.
Require Import Ensembles.
Require Import Vector.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.

Fixpoint zipwith {A B C : Type} {n : nat}
         (f : A -> B -> C) (v1 : t A n) (v2 : t B n) : t C n
  := match v1 in t _ n return t B n -> t C n with
     | nil _ => fun _ => nil C
     | cons _ x1 _ v1' =>
       fun v2 =>
         cons _ (f x1 (hd v2)) _ (zipwith f v1' (tl v2))
     end v2.

Definition zip {A B C : Type} {n : nat} := @zipwith A B (A*B) n pair.

Lemma nil_unique {A : Type} : forall (xs : t A 0), xs = nil A.
Proof.
  apply case0.
  reflexivity.
Qed.

Module Export DEFINITIONS.
  Variable (F V : Type) (r0 r1 : F) (radd rmul rsub : F -> F -> F) (ropp : F -> F) (req : F -> F -> Prop).
  Variable (rdiv : F -> F -> F) (rinv : F -> F).

  Declare Scope field_scope.
  Delimit Scope field_scope with fieldsc.
  Open Scope field_scope.

  Global Notation "0" := r0 : field_scope.
  Global Notation "1" := r1 : field_scope.
  Global Infix "==r" := req (at level 90) : field_scope.
  Global Infix "+r" := radd (at level 50) : field_scope.
  Global Infix "*r" := rmul (at level 40) : field_scope.
  Global Infix "-r" := rsub (at level 50) : field_scope.
  Global Notation "-r" := ropp (at level 30) : field_scope.
  Global Infix "/r" := rdiv (at level 40) : field_scope.
  Global Notation "/r" := rinv (at level 30) : field_scope.

  Variable (vadd : V -> V -> V) (vsmult : F -> V -> V) (v0 : V) (veq : V -> V -> Prop).

  Declare Scope vectorspace_scope.
  Delimit Scope vectorspace_scope with vecsc.
  Open Scope vectorspace_scope.

  Notation "0" := v0 : vectorspace_scope.
  Infix "==v" := veq (at level 90) : vectorspace_scope.
  Infix "+v" := vadd (at level 50) : vectorspace_scope.
  Infix "*v" := vsmult (at level 40) : vectorspace_scope.
  Definition vopp (x : V) : V := (-r 1) *v x.
  Notation "-v" := vopp (at level 30) : vectorspace_scope.

  (*1.19*)
  Record vectorspace_theory
    : Prop
    := mk_vst
         {
           vadd_comm : forall (x y : V), x +v y ==v y +v x;
           vadd_assoc : forall (x y z : V), (x +v y) +v z ==v x +v (y +v z);
           vadd_ident : forall (x : V), x +v 0 ==v x;
           vadd_inv : forall (x : V), exists (y : V), x +v y ==v 0;
           vsmult_ident : forall (x : V), 1 *v x ==v x;
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

  Hypothesis morph_veq' : forall x y, (veqb x y) = true -> x ==v y.
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
    - apply morph_veq'.
      apply H.
  Qed.

(*End DEFINITIONS.*)

(*Module VECTORSPACE.*)
  (*Include DEFINITIONS.*)

  (*Delimit Scope field_scope with fieldsc.*)
  Open Scope field_scope.

  Variable Fth : field_theory 0 1 radd rmul rsub ropp rdiv rinv req.
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

  Variable Rsth : Equivalence req.
  Variable reqe : ring_eq_ext radd rmul ropp req.

  Add Morphism radd with signature (req ==> req ==> req) as radd_ext1.
  Proof.
    intros.
    destruct reqe.
    compute in Radd_ext.
    specialize (Radd_ext x y H x0 y0 H0).
    apply Radd_ext.
  Qed.

  Add Morphism rmul with signature (req ==> req ==> req) as rmul_ext1.
  Proof.
    intros.
    destruct reqe.
    compute in Rmul_ext.
    specialize (Rmul_ext x y H x0 y0 H0).
    apply Rmul_ext.
  Qed.

  Add Morphism ropp with signature (req ==> req) as ropp_ext1.
  Proof.
    intros.
    destruct reqe.
    compute in Ropp_ext.
    specialize (Ropp_ext x y H).
    apply Ropp_ext.
  Qed.

  Add Morphism rinv with signature (req ==> req) as finv_ext1.
  Proof.
    intros.
    destruct reqe.

  Admitted.

  Add Ring FRing : Rth.
  Add Field FField : Fth.

  Variable (vadd : V -> V -> V) (vsmult : F -> V -> V) (v0 : V) (veq : V -> V -> Prop).

  (*Delimit Scope vectorspace_scope with vecsc.*)
  Open Scope vectorspace_scope.

  Notation "0" := v0 : vectorspace_scope.
  Infix "==v" := veq (at level 90) : vectorspace_scope.
  Infix "+v" := vadd (at level 50) : vectorspace_scope.
  Infix "*v" := vsmult (at level 40) : vectorspace_scope.
  (*Definition vopp (x : V) : V := (-r 1) *v x.*)
  Notation "-v" := (@vopp F V 1 ropp vsmult) (at level 30) : vectorspace_scope.

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


  Lemma VEq_ext : vec_eq_ext F V (@eq F) vadd vsmult (@eq V).
  Proof.
    split; compute; intros; rewrite H; rewrite H0; reflexivity.
  Qed.

  Variable Vsth : Equivalence veq.

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
    ring.
  Qed.

  Lemma add_both_sides (u v w : V) : u ==v v -> w +v u ==v w +v v.
  Proof.
    intros.
    rewrite H.
    reflexivity.
  Qed.

  Lemma subtract_both_sides (u v w : V) : w +v u ==v w +v v -> u ==v v.
  Proof.
    intros.
  Admitted.

  (*1.29*)
  Theorem zero_times_vector (x : V) :
    0%fieldsc *v x ==v 0.
  Proof.
    destruct Rth.
    rewrite <- (Radd_0_l 0%fieldsc).
    destruct Vth.
    rewrite (vdistr4 0%fieldsc 0%fieldsc x).
    specialize (vadd_inv0 (0%fieldsc *v x)).
    destruct vadd_inv0 as [y vadd_inv0].
    rewrite <- vadd_inv0.
    apply (add_both_sides _ _ (0%fieldsc *v x)).
    rewrite vsmult_ident0.
  Admitted.

  (*1.30*)
  Theorem number_times_zero (a : F) :
    a *v 0 = 0.
  Proof.
    destruct Vth.

  Admitted.

  Theorem vsmult_distr (a b : F) (x : V) : a *v (b *v x) ==v (a *r b) *v x.
  Proof.
  Admitted.

  Lemma minus_one_squared : -r 1 *r -r 1 ==r 1.
  Proof.
    ring.
  Qed.

  (*exercise 1.B.1*)
  Theorem vopp_involutive (x : V) : -v (-v x) ==v x.
  Proof.
    unfold vopp.
    rewrite vsmult_distr.
    rewrite minus_one_squared.
    destruct Vth.

  Admitted.

End VECTORSPACE.

Section SPAN.

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
  Notation "-v" := (@vopp F V 1 ropp vsmult) (at level 30) : vectorspace_scope.

  (*2.5*)
  Definition span {n : nat} (xs : t V n) : V -> Prop
    :=
      fun x => exists ys, x ==v fold_left vadd 0 (zipwith vsmult ys xs).

  (*2.8*)
  Definition spans {n : nat} (xs : t V n) : Prop
    :=
      span xs = Full_set V.


  (*2.5*)
  Theorem span_empty_zero : span (@nil V) = fun x => x ==v 0.
  Proof.
    apply (functional_extensionality (span (@nil V)) (fun x => x ==v 0)).
    intros x.
    unfold span.
    apply propositional_extensionality.
    split.
    - intros.
      destruct H as [ys H].
      rewrite (nil_unique ys) in H; simpl in H.
      apply H.
    - simpl.
      intros.
      exists (@nil F).
      simpl.
      apply H.
    Qed.

  Check Vth.

  (*2.10*)
  Definition finite_dimensional (V : Type) (H__vectorspace : )

End SPAN.

Section LINEAR_INDEPENDENCE.

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
  Notation "-v" := (vopp 1 ropp vsmult) (at level 30) : vectorspace_scope.

  (*2.17*)
  Definition linearly_independent {n : nat} (xs : t V n) : Prop :=
    forall (ys : t F n),
      fold_left vadd 0 (zipwith vsmult ys xs) ==v 0 ->
      Forall (fun y => y ==r 0%fieldsc) ys.

  (*2.17 b*)
  Theorem empty_independent : linearly_independent (@nil V).
  Proof.
    unfold linearly_independent; intros.
    specialize (nil_unique ys); intros.
    rewrite H0.
    apply Forall_nil.
  Qed.

  (*2.19*)
  Definition linearly_dependent {n : nat} (xs : t V n) : Prop :=
    exists (ys : t F n),
      Exists (fun y => y <> 0%fieldsc) ys -> fold_left vadd 0 (zipwith vsmult ys xs) ==v 0.


  Definition three_zeros : t V 3 :=
    (cons V 0 2 (cons V 0 1 (cons V 0 0 (nil V)))).
(*)
  Definition coprojection {A : Type} {n : nat} (v : t A n) (j : nat) (H : j < n) : t A (n-1) :=
    (*[x for i, x in enumerate(xs) if i != j]*)
    take (n-1) v.
*)
  Check nth_order (cons V 0 2 (cons V 0 1 (cons V 0 0 (nil V)))).
  Definition a_leq_prop := 5 <= 7.

  (*2.21*)
  Theorem linear_dependence_lemma1 {n : nat} (xs : t V n) (H : linearly_dependent xs) :
    exists (j : nat),
    forall (H0 : j <= n) (H1 : j < n),
      (@span F V vadd vsmult 0 veq j (take j H0 xs) (nth_order xs H1)).
  Proof.
    exists 1%nat.
    intros.
    induction xs.
    - inversion H0.
    - simpl.
      unfold linearly_dependent in H.
      destruct H as [ys H].
      unfold span.
     
  Admitted.

  (*2.23*)
  Theorem length_linearly_independent_list_leq_length_spanning_list {n m : nat} :
    forall (xs : t V n) (xs' : t V m),
      linearly_independent xs -> spans F V vadd vsmult 0 veq xs' -> n <= m.
  Proof.
    intros.
    unfold linearly_independent in H.
    unfold spans, span in H0.
  Admitted.

  Lemma fold_commute {n : nat} {a__k : t F n} {xs : t V n} {l : F} :
    fold_left vadd 0 (map (vsmult l) (zipwith vsmult a__k xs)) = vsmult l (fold_left vadd 0 (zipwith vsmult a__k xs)).
  Proof.
    generalize dependent a__k.
    induction xs; intros a__k.
    - specialize (nil_unique a__k); intros.
      rewrite H.
      simpl.
      symmetry.
      apply number_times_zero with (r0 := r0) (r1 := r1) (radd := radd) (rmul := rmul)
                                   (rsub := rsub) (ropp := ropp) (req := req) (rdiv := rdiv)
                                   (rinv := rinv) (vadd := vadd) (veq := veq); give_up.
    - simpl.
  Admitted.

  Lemma factor_out_scalar {n : nat} {a__k : t F n} {xs : t V n} : forall (l : F) (H__l : l <> 0%fieldsc),
      fold_left vadd 0 (map (vsmult l) (zipwith vsmult a__k xs)) = 0 ->
      fold_left vadd 0 (zipwith vsmult a__k xs) = 0.
  Proof.
    intros l H__l H__xsl.
    rewrite fold_commute in H__xsl.
    Admitted.

  (*exercise 2.A.8*)
  Theorem scalar_ind {n : nat} :
    forall (l : F) (H__l : l <> 0%fieldsc) (xs : t V n) (H__xs : linearly_independent xs),
      linearly_independent (map (vsmult l) xs).
  Proof.
    intros l H__l xs H__xs.
    unfold linearly_independent in *.
    intros b__k H__lx.
    specialize (H__xs b__k).
  Admitted.


  (*exercise 2.A.9*)
  (*This is actually false, counterexample is v = [2,0], [0,1] and w = [1, 2], [3, 1]*)
  Theorem sum_ind {n : nat} : forall (xs ys : t V n) (H__xs : linearly_independent xs) (H__ys : linearly_independent ys),
      linearly_independent (zipwith vadd xs ys).
  Proof.
    intros xs ys H__xs H__ys.
    unfold linearly_independent in *.
    intros b__k H__xys.
    specialize (H__xs b__k).
    apply H__xs.
