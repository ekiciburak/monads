Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.

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

Class Functor (catC catD: Category) (F: catC -> catD)
              (fmap : forall {a b: catC} (f: arrow catC b a), (arrow catD (F b) (F a))): Type :=
  {
    preserve_id     : forall {a: catC}, fmap (@identity catC a) = (@identity catD (F a));
    preserve_comp   : forall {a b c: catC} (f: arrow catC b a) (g : arrow catC c b), fmap (g o f) = (fmap g) o (fmap f)
  }.
Check Functor.

Definition coq_id_on_objects (catC: Category) (a: catC) := a.
Definition coq_id_on_morphisms (catC: Category) (a b: catC) (f: (@arrow catC b a)) := f.
Check coq_id_on_morphisms.

Program Instance ID (catC: Category): 
                       (@Functor catC catC (coq_id_on_objects catC) (coq_id_on_morphisms catC)).
(*
Obligation 1. destruct catC. apply arrows_setoid0. Qed.
Next Obligation. destruct catC. apply arrows_setoid0. Qed.
Next Obligation. unfold coq_id_on_objects. reflexivity. Qed.
Next Obligation. unfold coq_id_on_objects; reflexivity. Qed.*)
Check ID.

Class NaturalTransformation (catC catD: Category) (F G: catC -> catD) 
                            (fmapF : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            (fmapG : forall (a b: catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                            `(@Functor catC catD F fmapF) 
                            `(@Functor catC catD G fmapG) 
                                                  (trans : forall (a: catC), (arrow catD (G a) (F a))): Type :=
  {
    comm_diag: forall {a b: catC} (f: arrow catC b a), fmapG _ _ f o trans a = trans b o fmapF _ _ f
  }.
Check NaturalTransformation.

Class Monad (catC: Category) (F: catC -> catC)
            (fmapId : forall (a b: catC) (f: arrow catC b a), (arrow catC (id b) (id a)))
            (fmapT  : forall (a b: catC) (f: arrow catC b a), (arrow catC (F b) (F a)))
            (fmapT2 : forall (a b: catC) (f: arrow catC b a), (arrow catC (F (F b)) (F (F a))))
                        (IdF : (Functor catC catC id fmapId))
                        (T   : (Functor catC catC F fmapT))
                        (T2  : (Functor catC catC (fun a: catC => F (F a)) fmapT2))
                        (eta : forall (a: catC), (arrow catC (F a) (id a)))
                        (mu  : forall (a: catC), (arrow catC (F a) (F (F a))))
                          `(@NaturalTransformation catC catC id F fmapId fmapT IdF T eta)
                          `(@NaturalTransformation catC catC (fun a: catC => F (F a)) F fmapT2 fmapT T2 T mu): Type :=
  {
    comm_diagram1   : forall (a: catC), (mu a) o (fmapT _ _  (mu a)) = (mu a) o (mu (F a));
    comm_diagram2   : forall (a: catC), (mu a) o (fmapT _ _ (eta a)) = (mu a) o (eta (F a));
    comm_diagram2_b1: forall (a: catC), (mu a) o (fmapT _ _ (eta a)) =  (identity catC (F a));
    comm_diagram2_b2: forall (a: catC), (mu a) o (eta (F a)) =  (identity catC (F a))
  }.
Check Monad.

Class Adjunction (catC catD: Category) (F: catC -> catD) (G: catD -> catC) 
                 (fmapF : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                 (fmapG : forall (a b: catD) (f: arrow catD b a), (arrow catC (G b) (G a)))
                 `(@Functor catC catD F fmapF) 
                 `(@Functor catD catC G fmapG): Type :=
  {
     bijl : forall (b: catC) (a: catD), (arrow catD a (F b)) -> (arrow catC (G a) b);
     bijr : forall (b: catC) (a: catD), (arrow catC (G a) b) -> (arrow catD a (F b))
  }.
Check Adjunction.
