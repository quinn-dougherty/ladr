
Section exercise_1B6.
  Require Import VS.Classes.
  Require Import QArith.
  Local Open Scope Q_scope.

  Inductive ExtendedQ : Type :=
    | pinf : ExtendedQ
    | ninf : ExtendedQ
    | fromRat (x : Q) : ExtendedQ.

  Definition EQ_add (x y : ExtendedQ) : ExtendedQ :=
    match x, y with
    | pinf, pinf => pinf
    | pinf, ninf => fromRat 0
    | pinf, fromRat y' => pinf
    | ninf, pinf => fromRat 0
    | ninf, ninf => ninf
    | ninf, fromRat y' => ninf
    | fromRat x', pinf => pinf
    | fromRat x', ninf => ninf
    | fromRat x', fromRat y' => fromRat (x' + y')
    end.

  Definition EQ_smult (x : Q) (y : ExtendedQ) : ExtendedQ :=
    match Q_dec x 0 with
    | inleft (left _) => match y with
                         | pinf => ninf
                         | ninf => pinf
                         | fromRat y' => fromRat (y' + x)
                         end
    | inleft (right _) => match y with
                       | pinf => pinf
                       | ninf => ninf
                       | fromRat y' => fromRat (y' + x)
                       end
    | inright _ => fromRat 0
    end.

  Theorem Q_isring : ring_theory 0 1 Qplus Qmult Qminus Qopp eq.
    Proof.
      Admitted.

  Instance QRing : Ring Q :=
    {
    r0 := 0;
    r1 := 1;
    radd  := Qplus;
    rmult := Qmult;
    rainv := Qopp;
    rminus := Qminus;
    req := eq;
    isring := Q_isring;
    }.
  Check Qinv.

  Theorem Q_isfield : field_theory 0 1 Qplus Qmult Qminus Qopp Qdiv Qinv eq.
  Proof.
    Admitted.

  Instance QField : Field Q :=
    {
    fdiv := Qdiv;
    finv := Qinv;
    isfield := Q_isfield
    }.

  Theorem ExtendedQ_isvectorspace : vectorspace_theory EQ_smult EQ_add (fromRat 0).
  Proof.
    split; intros.
    - induction x; induction y; simpl; try reflexivity.
  Admitted.

End exercise_1B6.
