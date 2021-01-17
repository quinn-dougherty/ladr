From LADR Require Import VectorSpace.
Include DEFINITIONS.
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
Proof. apply case0. reflexivity. Qed.


(*2.5*)
Definition span {n : nat} (xs : t V n) : V -> Prop
  :=
    fun x => exists ys, x = fold_left vadd 0 (zipwith vsmult ys xs).

(*2.8*)
Definition spans {n : nat} (xs : t V n) : Prop
  :=
    span xs = Full_set V.


(*2.5*)
Theorem span_empty_zero : span (@nil V) = fun x => x = 0.
Proof.
  apply (functional_extensionality (span (@nil V)) (fun x => x = 0)).
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
(*
(*2.10*)
Definition finite_dimensional (V : Type) (H__vectorspace : )
*)
(*Linear Independence*)

(*2.17*)
Definition linearly_independent {n : nat} (xs : t V n) : Prop :=
  forall (ys : t F n),
    fold_left vadd 0 (zipwith vsmult ys xs) = 0 ->
    Forall (fun y => y = 0%fieldsc) ys.

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
    Exists (fun y => y <> 0%fieldsc) ys -> fold_left vadd 0 (zipwith vsmult ys xs) = 0.


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
    (span (take j H0 xs) (nth_order xs H1)).
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
