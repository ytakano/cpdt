Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
  | Nil => O
  | Cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
  | Nil => ls2
  | Cons x ls1' => Cons x (app ls1' ls2)
  end.

Theorem length_app :
  forall T (ls1 ls2 : list T), length (app ls1 ls2) = plus (length ls1) (length ls2).
  induction ls1; crush.
Qed.

Print list.

Check length.

Check list_ind.
