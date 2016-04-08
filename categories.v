Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation.

Module Make(Import M: notation.T).

Record Category: Type := 
 mk_Category 
 {
     obj :> Type;
     arrow: obj -> obj -> Type;
     identity : forall a, arrow a a;
     comp : forall {a b c}, (arrow a b) -> (arrow b c) -> (arrow a c);
     assoc : forall {a b c d} (f : arrow b a) (g : arrow c b) (h : arrow d c), comp h (comp g f) = comp (comp h g) f
  }.

Notation " x 'o' y " := (comp _ x y) (at level 40, left associativity). 

Definition Product_Category (catC catD: Category) : Category.
Proof. 
refine (@mk_Category 
(catC * catD)%type
(fun a b => (arrow catC (fst a) (fst b) * arrow catD (snd a) (snd b))%type)
(fun a => (identity catC (fst a), identity catD (snd a)))
(fun a b c f2 f1 => (fst f2 o fst f1, snd f2 o snd f1))
_ ). intros. setoid_rewrite <- assoc. reflexivity.
Qed.
Check Product_Category.

Definition Dual_Category (catC: Category) : Category.
Proof. 
refine (@mk_Category 
(catC)%type
(fun a b => (arrow catC b a %type))
(fun a => (@identity catC a))
(fun a b c f1 f2 => f2 o f1)
_ ). intros. setoid_rewrite <- assoc. reflexivity.
Qed.
Check Dual_Category.

(*
Class Category (Obj : Type) (Arrow: Obj -> Obj -> Type) : Type := 
 {
     obj := Obj;
     arrow := Arrow;
     identity : forall a, arrow a a;
     comp : forall {a b c}, (arrow a b) -> (arrow b c) -> (arrow a c);
     assoc : forall {a b c d} (f : arrow b a) (g : arrow c b) (h : arrow d c), comp h (comp g f) = comp (comp h g) f
  }.
Coercion obj : Category >-> Sortclass.
Check comp.

Notation " x 'o' y " := (comp x y) (at level 40, left associativity).

Definition Dual_Category `(catC: Category Obj Arrow) : Category Obj (fun x y => Arrow y x).
refine (@Build_Category Obj
                              (fun x y => arrow y x) 
                              (fun a => (@identity obj arrow catC a))
                              (fun a b c f g => g o f )
                             _).
intros. rewrite assoc. reflexivity. Defined.
*)

Record Product (catC: Category) (p a b: obj catC)
               (pi1: arrow catC a p) (pi2: arrow catC b p): Type :=
 mk_Product
  {
    pcomm_diag: forall (x: catC) (f1: arrow catC a x) (f2: arrow catC b x), 
      exists !(g: arrow catC p x), f1 = pi1 o g /\ f2 = pi2 o g
  }.
Check Product.

Record coProduct (catC: Category) (cp a b: catC)
                (inl: arrow catC cp a) (inr: arrow catC cp b): Type :=
  {
    cpcomm_diag: forall (x: catC) (f1: arrow catC x a) (f2: arrow catC x b), 
      exists !(g: arrow catC x cp), f1 = g o inl /\ f2 = g o inr
  }.
Check coProduct.

Record Pullback (catC: Category) (p a b c: catC) 
               (f: arrow catC c a) (g: arrow catC c b)
               (pi1: arrow catC a p) (pi2: arrow catC b p): Type :=
{
   pbcomm_diag1: g o pi2 = f o pi1;
   pbcomm_diag2: forall (q: catC) (q1: arrow catC a q) (q2: arrow catC b q), 
     exists !(u: arrow catC p q), pi2 o u = q2 /\ pi1 o u = q1
}.
Check Pullback.

Record Pushout  (catC: Category) (p a b c: catC) 
               (f: arrow catC a c) (g: arrow catC b c)
               (inl: arrow catC p a) (inr: arrow catC p b): Type :=
{
   pocomm_diag1: inr o g = inl o f;
   pocomm_diag2: forall (q: catC) (q1: arrow catC q a) (q2: arrow catC q b), 
     exists !(u: arrow catC q p), u o inr = q2 /\ u o inl = q1
}.
Check Pushout.

End Make.
