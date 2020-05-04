Require Import Bool Arith List Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Definition typeDenote (t : type) : Set :=
  match t with
  | Nat => nat
  | Bool => bool
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res) :
  typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | TPlus => plus
  | TTimes => mult
  | TEq Nat => beq_nat
  | TEq Bool => eqb
  | TLt => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
  | TNConst n => n
  | TBConst b => b
  | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiBinop : forall arg1 arg2 res s,
    tbinop arg1 arg2 res -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3, tinstr s1 s2 -> tprog s2 s3 -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
  | nil => unit
  | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition instrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i with
  | TiNConst _ n => fun s => (n, s)
  | TiBConst _ b => fun s => (b, s)
  | TiBinop _ _ _ _ b => fun s => let '(arg1, (arg2, s')) := s in
                                  ((tbinopDenote b) arg1 arg2, s')
  end.
