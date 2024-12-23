(*
   Sanjay Adhith
   <tfmsadhith@gmail.com>
*)

Require Import Arith.

Structure Group : Type :=
  make_group
    {
      S : Set;

      op : S -> S -> S;
      inv : S -> S;
      z : S;

      op_assoc : forall a b c,
        op a (op b c) =
          op (op a b) c;

      op_z : forall a,
        op z a = a /\
          op a z = a;

      op_inv : forall a,
        op a (inv a) = z /\
          op (inv a) a = z;
    }.


Lemma group_cancel_l:
  forall T : Group,
    forall a b c: (T.(S)),
        T.(op) a b = T.(op) a c -> b = c.

Proof.  
  intros T a b c H_eq.
  assert (op T (T.(inv) a) (op T a b) = op T (T.(inv) a) (op T a c)) as both_sides.
  {
    rewrite -> H_eq.
    reflexivity.
  }
  rewrite ->2 op_assoc in both_sides.
  pose (op_inv T a) as inv.
  destruct inv as [_ H_inv].
  rewrite -> H_inv in both_sides.
  pose (op_z T b) as null.
  destruct null as [H_null _].
  rewrite -> H_null in both_sides.
  clear H_null.
  pose (op_z T c) as null.
  destruct null as [H_null _].
  rewrite -> H_null in both_sides.
  exact both_sides.
Qed.
