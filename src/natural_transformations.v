Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks functors.

Module Make(Import M: notation.T).
 Module Export natural_transformations_exp := functors.Make(M).

Definition id {catC: Category} (a: catC) := a.

Class NaturalTransformation (catC catD: Category) (F G: catC -> catD) 
                            (fmapF : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            (fmapG : forall (a b: catC) (f: arrow catC b a), (arrow catD (G b) (G a)))
                            `(@Functor catC catD F fmapF) 
                            `(@Functor catC catD G fmapG) 
                                (trans : forall (a: catC), (arrow catD (G a) (F a))): Type :=
  mk_nt
  {
    comm_diag: forall {a b: catC} (f: arrow catC b a), fmapG _ _ f o trans a = trans b o fmapF _ _ f
  }.
Check NaturalTransformation.

(* TODO:= these might be obligations of the Category record *)
Axiom identity_f: forall (catC: Category) (a b: catC) (f: arrow catC b a), (@identity catC b) o f = f.
Axiom f_identity: forall (catC: Category) (a b: catC) (f: arrow catC b a), f o (@identity catC a) = f.

Program Instance IdentityNaturalTransformation `(catC: Category) `(catD: Category) (F G: catC -> catD) 
                            (fmapF : forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: @Functor catC catD F fmapF):
                            `(@NaturalTransformation catC catD F F fmapF fmapF FunctF FunctF 
                                   (fun a => (@identity catD (F a)))).
Obligation 1. destruct FunctF. rewrite <- preserve_id0. rewrite <- preserve_id0.
       rewrite <- preserve_comp0. rewrite <- preserve_comp0. rewrite identity_f.
       rewrite f_identity. reflexivity. Defined.
Check IdentityNaturalTransformation.

(*TODO:= composition of natural transformations *)

End Make.
