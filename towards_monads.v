Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.

Class Morp (X: Type) : Type := 
  {
     arrow: X -> X -> Type
  }.
Check Morp.

Class Category (A: Type) `(@Morp A): Type := 
  {
     arrows_setoid :> forall a b, Setoid (arrow b a);
     identity : forall {a: A}, arrow a a;
     comp : forall {a b c}, (arrow a b) -> (arrow b c) -> (arrow a c);
     assoc : forall {a b c d} (f : arrow b a) (g : arrow c b) (h : arrow d c), comp h (comp g f) == comp (comp h g) f
  }.
Check Category. 

Notation " x 'o' y " := (comp x y) (at level 40, left associativity).

Class Functor (C D: Type) (mc: Morp C) (catC: Category C mc) 
                          (md: Morp D) (catD: Category D md)
              (F: C -> D)
              (fmap : forall {a b: C} (f: arrow b a), (arrow (F b) (F a))) :=
  {
    preserve_id : forall {a: C}, fmap (@identity C mc catC a) == (@identity D md catD (F a));
    preserve_comp : forall {a b c: C} (f: arrow b a) (g : arrow c b), fmap (g o f) == (fmap g) o (fmap f)
  }.
Check Functor.

 Definition coq_id_on_objects (A: Type) (a: A) := a.
 Definition coq_id_on_morphisms (C: Type) (mc: Morp C) (catC: Category C mc) (a b:C) (f: (@arrow C mc b a)) := f.
 Check coq_id_on_morphisms.

 Program Instance ID (C: Type) (mc: Morp C) (catC: Category C mc) : 
                       (@Functor C C mc catC mc catC (coq_id_on_objects C) (coq_id_on_morphisms C mc catC)).
 Next Obligation. unfold coq_id_on_objects; reflexivity. Qed.
 Next Obligation. unfold coq_id_on_objects; reflexivity. Qed.
 Check ID.

Class NaturalTransformation (C D: Type)  (mc: Morp C) (catC: Category C mc) 
                                         (md: Morp D) (catD: Category D md)
                            (F G: C -> D) 
                                         (fmapF : forall (a b: C) (f: arrow b a), (arrow (F b) (F a)))
                                         (fmapG : forall (a b: C) (f: arrow b a), (arrow (G b) (G a)))
                                         `(@Functor C D mc catC md catD F fmapF) 
                                         `(@Functor C D mc catC md catD G fmapG) 
                            (trans : forall (a: C), (arrow (G a) (F a))) :=
  {
    comm_diag: forall {a b: C} (f: arrow b a), fmapG _ _ f o trans a == trans b o fmapF _ _ f
  }.
Check NaturalTransformation.

Class Monad (C: Type) (mc: Morp C) (catC: Category C mc) (F: C -> C)
                      (fmapId : forall (a b: C) (f: arrow b a), (arrow (id b) (id a)))
                      (fmapT  : forall (a b: C) (f: arrow b a), (arrow (F b) (F a)))
                      (fmapT2 : forall (a b: C) (f: arrow b a), (arrow (F (F b)) (F (F a))))
                        (IdF : (Functor C C mc catC mc catC id fmapId))
                        (T   : (Functor C C mc catC mc catC F fmapT))
                        (T2  : (Functor C C mc catC mc catC (fun a: C => F (F a)) fmapT2))
                        (eta : forall (a: C), (arrow (F a) (id a)))
                        (mu  : forall (a: C), (arrow (F a) (F (F a))))
                          `(@NaturalTransformation C C mc catC mc catC id F fmapId fmapT IdF T eta)
                          `(@NaturalTransformation C C mc catC mc catC (fun a: C => F (F a)) F fmapT2 fmapT T2 T mu) :=
  {
    comm_diagram1   : forall (a: C), (mu a) o (fmapT _ _  (mu a)) == (mu a) o (mu (F a));
    comm_diagram2   : forall (a: C), (mu a) o (fmapT _ _ (eta a)) == (mu a) o (eta (F a));
    comm_diagram2_b1: forall (a: C), (mu a) o (fmapT _ _ (eta a)) ==  identity;
    comm_diagram2_b2: forall (a: C), (mu a) o (eta (F a)) ==  identity
  }.
Check Monad.
