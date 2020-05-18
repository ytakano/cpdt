Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
    | Nil => O
    | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall ls1 ls2 : list, length (app ls1 ls2) = plus (length ls1) (length ls2).
    induction ls1; crush.
  Qed.
End list.

Arguments Nil [T].

Print list.

Check length.

Check list_ind.
