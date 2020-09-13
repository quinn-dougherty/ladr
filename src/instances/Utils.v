Require Import Vector.

Fixpoint zipwith {A B C : Type} {n : nat}
         (f : A -> B -> C) (v1 : t A n) (v2 : t B n) : t C n
  := match v1 in t _ n return t B n -> t C n with
     | nil _ => fun _ => nil C
     | cons _ x1 _ v1' =>
       fun v2 =>
         cons _ (f x1 (hd v2)) _ (zipwith f v1' (tl v2))
     end v2.

Definition zip {A B C : Type} {n : nat} := @zipwith A B _ n pair.

Lemma empty_vec_has_exactly_one {A : Type} (xs : t A 0) : xs = nil A.
Proof.
  Print t.
  Admitted.

Lemma zipwith_step {A B C : Type} {n : nat} :
  forall (f : A -> B -> C) (x : A) (xs : t A n) (y : B) (ys : t B n),
    cons C (f x y) n (zipwith f xs ys) = zipwith f (cons A x n xs) (cons B y n ys).
Proof.
  intros; generalize dependent ys; induction xs; intros ys; simpl; reflexivity.
Qed.


Theorem zipwith_commu {A B : Type} {n : nat} :
  forall (f : A -> A -> B) (xs ys : t A n)
    (H : forall a b, f a b = f b a), zipwith f xs ys = zipwith f ys xs.
Proof.
  intros.
  generalize dependent ys.
  induction xs; intros.
  - rewrite (empty_vec_has_exactly_one ys).
    reflexivity.
  - simpl.
    rewrite zipwith_step.
    give_up.
Admitted.
