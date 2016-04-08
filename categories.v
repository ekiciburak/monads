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
           _ 
         ). 
  intros. setoid_rewrite <- assoc. reflexivity.
Defined.
Check Product_Category.

Definition Dual_Category (catC: Category) : Category.
Proof. 
  refine (@mk_Category 
           (catC)%type
           (fun a b => (arrow catC b a %type))
           (fun a => (@identity catC a))
           (fun a b c f1 f2 => f2 o f1)
           _
         ). 
  intros. setoid_rewrite <- assoc. reflexivity.
Defined.
Check Dual_Category.

(*
Class Category2 (Obj : Type) (Arrow: Obj -> Obj -> Type) : Type := 
 {
     obj2 := Obj;
     arrow2 := Arrow;
     identity2 : forall a, arrow2 a a;
     comp2 : forall {a b c}, (arrow2 a b) -> (arrow2 b c) -> (arrow2 a c);
     assoc2 : forall {a b c d} (f : arrow2 b a) (g : arrow2 c b) (h : arrow2 d c), comp2 h (comp2 g f) = comp2 (comp2 h g) f
  }.

Coercion obj2 : Category2 >-> Sortclass.
Check comp2.


Notation " x 'O' y " := (comp2 x y) (at level 40, left associativity).

Generalizable All Variables.

Definition Dual_Category2 `(catC: Category2 objC arrowC) : Category2 objC (fun x y => arrowC y x).
refine (@Build_Category2 objC
                              (fun x y => arrow2 y x) 
                              (fun a => (@identity2 obj2 arrow2 catC a))
                              (fun a b c f g => g O f)
                             _).
intros. rewrite <- assoc2. reflexivity. Defined.
Check Dual_Category2.
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
