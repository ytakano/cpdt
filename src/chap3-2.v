Inductive unit : Set :=
| tt.

Check unit.
Check tt.

Theorem unit_singleton : forall x : unit, x = tt.
  induction x.
  reflexivity.
Qed.

Check unit_ind.

Inductive Empty_set : Set := .

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
  destruct 1.
Qed.

Check Empty_set_ind.

Definition e2u (e : Empty_set) : unit :=
  match e with end.

Inductive bool : Set :=
| true
| false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
  destruct b.
  reflexivity.
  Restart.
  destruct b; reflexivity.
Qed.

Theorem negb_ineq : forall b : bool, negb b <> b.
  destruct b;
    discriminate.
Qed.

Check bool_ind.
