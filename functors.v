Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories.

Module Make(Import M: notation.T).
 Module Export functors_exp := categories.Make(M).

Class Functor `(catC: Category) `(catD: Category) (F: catC -> catD)
                (fmap: forall {a b: catC} (f: arrow catC b a), (arrow catD (F b) (F a))): Type :=
  mk_Functor
  {
    preserve_id     : forall {a: catC}, fmap (@identity catC a) = (@identity catD (F a));
    preserve_comp   : forall {a b c: catC} (f: arrow catC b a) (g : arrow catC c b), fmap (g o f) = (fmap g) o (fmap f)
  }.
Check Functor.

Definition Opposite_Functor `(catC: Category) `(catD: Category) 
                            (F: catC -> catD)
                            (fmapF: forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                                (FunctF: Functor catC catD F fmapF): (Functor (Dual_Category catC) (Dual_Category catD) F (fun a b => fmapF b a)).
Proof. refine (@mk_Functor
                (Dual_Category catC) 
                (Dual_Category catD)
                F
                (fun a b => fmapF b a)
                (fun a => (@preserve_id catC catD F fmapF FunctF a)) 
                (fun a b c f g => (@preserve_comp catC catD F fmapF FunctF c b a g f))
              ).
Defined.
Check Opposite_Functor.

(*define how the identity functor behaves on objects and morphisms*)
Definition coq_id_on_objects (catC: Category) (a: catC) := a.
Definition coq_id_on_morphisms (catC: Category) (a b: catC) (f: (@arrow catC b a)) := f.
Check coq_id_on_morphisms.

Program Instance ID (catC: Category): 
                       (@Functor catC catC (coq_id_on_objects catC)  (coq_id_on_morphisms catC)).
(*
Obligation 1. destruct catC. apply arrows_setoid0. Qed.
Next Obligation. destruct catC. apply arrows_setoid0. Qed.
Next Obligation. unfold coq_id_on_objects. reflexivity. Qed.
Next Obligation. unfold coq_id_on_objects; reflexivity. Qed.*)
Check ID.


(*define how the functor composition behaves on objects and morphisms*)
Definition coq_comp_on_objects (catC catD catE: Category) (F: catC -> catD) (G: catD -> catE) (a: catC) := 
G (F a).
Definition coq_comp_on_morphism (catC catD catE: Category) (F: catC -> catD) (G: catD -> catE) 
                                (fmapF  : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                                (fmapG  : forall (a b: catD) (f: arrow catD b a), (arrow catE (G b) (G a)))
                                (a b: catC) (f: (arrow catC b a)) :=
fmapG _ _ (fmapF _ _ f).
Check coq_comp_on_morphism.

Program Instance Compose_Functors (catC catD catE: Category) (F: catC -> catD) (G: catD -> catE) 
                                  (fmapF  : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                                  (FunctF: @Functor catC catD F fmapF) 
                                  (fmapG  : forall (a b: catD) (f: arrow catD b a), (arrow catE (G b) (G a)))
                                  (FunctG: @Functor catD catE G fmapG):
                                  (@Functor catC catE 
                                     (@coq_comp_on_objects catC catD catE F G)
                                     (@coq_comp_on_morphism catC catD catE F G fmapF fmapG)).
Obligation 1. unfold coq_comp_on_morphism, coq_comp_on_objects. remember (@preserve_id catC catD F fmapF FunctF a).
  remember (@preserve_id catD catE G fmapG FunctG (F a)). rewrite <- e0. rewrite e. reflexivity. Defined.
Next Obligation. unfold coq_comp_on_objects, coq_comp_on_morphism. remember (@preserve_comp catC catD F fmapF FunctF a b c f g).
  remember (@preserve_comp catD catE G fmapG FunctG (F a) (F b) (F c) (fmapF _ _ f) (fmapF _ _ g)).
  rewrite <- e0. rewrite e. reflexivity. Defined.
Check Compose_Functors.

End Make.