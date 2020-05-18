Require Import Bool Arith List Cpdt.CpdtTactics.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem O_plus_n : forall n : nat, plus O n = n.
  intro.
  reflexivity.
Qed.

Theorem n_plus_O : forall n : nat, plus n O = n.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Check nat_ind.

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
  injection 1.
  trivial.
Qed.

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
  | NNil => O
  | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
  | NNil => ls2
  | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

Theorem nlength_napp : forall ls1 ls2 : nat_list,
    nlength (napp ls1 ls2) = plus (nlength ls1) (nlength ls2).
  induction ls1; crush.
Qed.

Check nat_list_ind.

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
  | NLeaf => S O
  | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
  | NLeaf => NNode tr2 O NLeaf
  | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc: forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
  induction n1;
    crush.
Qed.

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree,
    nsize (nsplice tr1 tr2) = plus (nsize tr2) (nsize tr1).
  induction tr1;
    crush.
  rewrite plus_assoc.
  reflexivity.
Qed.

