Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories.

Module Make(Import M: notation.T).
 Module Export functors_exp := categories.Make(M).

Class Functor `(catC: Category) `(catD: Category) (F: catC -> catD)
              (fmap : forall {a b: catC} (f: arrow catC b a), (arrow catD (F b) (F a))): Type :=
  mk_Functor
  { 
    preserve_id     : forall {a: catC}, fmap (@identity catC a) = (@identity catD (F a));
    preserve_comp   : forall {a b c: catC} (f: arrow catC b a) (g : arrow catC c b), fmap (g o f) = (fmap g) o (fmap f)
  }.
Check Functor.

(*define how the identity functor behaves on objects and morphisms*)
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

Generalizable All Variables.

(*
Definition func_op `(FunctF: Functor (catC := C) (catD := D) (F := fobj)): (Functor (Dual_Category D) (Dual_Category D) fobj).

Class Functor `(catC: Category  objC arrowC) `( catD: Category  objD arrowD) (F: catC -> catD) :=
  { 
    fmap2            : forall {a b} (f: (@arrow objC arrowC catC b a)), (@arrow objD arrowD catD (F b) (F a));
    preserve_id2     : forall {a: catC}, fmap2 (@identity objC arrowC catC a) = (@identity objD arrowD catD (F a));
    preserve_comp2   : forall {a b c: catC} (f: (@arrow objC arrowC catC b a)) (g : (@arrow objC arrowC catC c b)), fmap2 (g o f) = (fmap2 g) o (fmap2 f)
  }.
Check Functor.

Definition func_op `(FunctF: Functor (catC := C) (catD := D) (F := fobj)): (Functor (Dual_Category D) (Dual_Category D) fobj).

Class Functor3 (catC catD: Category): Type :=
  mk_Functor3
  { 
    omap            :> catC -> catD;
    fmap3            : forall a b (f: arrow catC b a), (arrow catD (omap b) (omap a));
    preserve_id3     : forall a, fmap3 _ _ (@identity catC a) = (@identity catD (omap a));
    preserve_comp3   : forall a b c (f: arrow catC b a) (g : arrow catC c b), fmap3 _ _ (g o f) = (fmap3 _ _ g) o (fmap3 _ _ f)
  }.

Check Functor2.


Definition Opposite_Functor (catC catD: Category) (F: Functor3 catC catD): Functor3 (Dual_Category catC) (Dual_Category catD):=
  (@mk_Functor3 (Dual_Category catC)%type (Dual_Category catD)%type
  (fun a => omap a)
  (fun x y => fmap3 x y)
  (fun x => preserve_id3 x)
  (fun a b c f g => preserve_comp3 a b c f g)  
).

*)

End Make.