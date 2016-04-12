Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories.

Module Make(Import M: notation.T).
 Module Export functors_exp := categories.Make(M).
 
Record Product (catC: Category) (p a b: obj catC)
               (pi1: arrow catC a p) (pi2: arrow catC b p): Type :=
 mk_Product
  {
    pcomm_diag: forall (x: obj catC) (f1: arrow catC a x) (f2: arrow catC b x), 
      exists !(g: arrow catC p x), f1 = pi1 o g /\ f2 = pi2 o g
  }.
Check Product.

Record coProduct (catC: Category) (cp a b: obj catC)
                (inl: arrow catC cp a) (inr: arrow catC cp b): Type :=
  {
    cpcomm_diag: forall (x: obj catC) (f1: arrow catC x a) (f2: arrow catC x b), 
      exists !(g: arrow catC x cp), f1 = g o inl /\ f2 = g o inr
  }.
Check coProduct.

Record Pullback (catC: Category) (p a b c: obj catC) 
               (f: arrow catC c a) (g: arrow catC c b)
               (pi1: arrow catC a p) (pi2: arrow catC b p): Type :=
{
   pbcomm_diag1: g o pi2 = f o pi1;
   pbcomm_diag2: forall (q: obj catC) (q1: arrow catC a q) (q2: arrow catC b q), 
     exists !(u: arrow catC p q), pi2 o u = q2 /\ pi1 o u = q1
}.
Check Pullback.

Record Pushout  (catC: Category) (p a b c: obj catC) 
               (f: arrow catC a c) (g: arrow catC b c)
               (inl: arrow catC p a) (inr: arrow catC p b): Type :=
{
   pocomm_diag1: inr o g = inl o f;
   pocomm_diag2: forall (q: obj catC) (q1: arrow catC q a) (q2: arrow catC q b), 
     exists !(u: arrow catC q p), u o inr = q2 /\ u o inl = q1
}.
Check Pushout.

End Make.