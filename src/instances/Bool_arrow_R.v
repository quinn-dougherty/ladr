Inductive coin :=
| heads : coin
| tails : coin
.

Theorem coin_into_R_isvectorspace :
  vectorspace_theory
    (fun k => fun f => fun (x : coin) => rmult k (f x))
    (fun f => fun g => fun (x : coin) => radd (f x) (g x))
    (fun _ => 0).
Proof.
Admitted.

Instance coin_into_R : VectorSpace R (coin -> R) :=
  {
  vscalar_mult := fun k => fun f => fun (x : coin) => rmult k (f x);
  vaddition := fun f => fun g => fun (x : coin) => radd (f x) (g x);
  v0 := fun _ => 0;
  isvectorspace := coin_into_R_isvectorspace
  }.
