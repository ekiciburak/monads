Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation categories prods_pullbacks.

Module Make(Import M: notation.T).
 Module Export functors_exp := categories.Make(M).

Class Functor `(catC: Category) `(catD: Category) (F: obj catC -> obj catD)
                (fmap: forall {a b: obj catC} (f: arrow catC b a), (arrow catD (F b) (F a))): Type :=
  mk_Functor
  {
    preserve_id     : forall {a: obj catC}, fmap (@identity catC a) = (@identity catD (F a));
    preserve_comp   : forall {a b c: obj catC} (f: arrow catC b a) (g : arrow catC c b), fmap (g o f) = (fmap g) o (fmap f)
  }.
Check Functor.

Program Instance Opposite_Functor `(catC: Category) `(catD: Category) 
                            (F: obj catC -> obj catD)
                            (fmapF: forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: Functor catC catD F fmapF): 
                                `(Functor (Dual_Category catC) (Dual_Category catD) F (fun a b => fmapF b a)).
Obligation 1. specialize (@mk_Functor
                (Dual_Category catC) 
                (Dual_Category catD)
                F
                (fun a b => fmapF b a)
                (fun a => (@preserve_id catC catD F fmapF FunctF a)) 
                (fun a b c f g => (@preserve_comp catC catD F fmapF FunctF c b a g f))
              ). intros. destruct H as [H1 H2]. apply H1. Qed.
Next Obligation. specialize (@mk_Functor
                (Dual_Category catC) 
                (Dual_Category catD)
                F
                (fun a b => fmapF b a)
                (fun a => (@preserve_id catC catD F fmapF FunctF a)) 
                (fun a b c f g => (@preserve_comp catC catD F fmapF FunctF c b a g f))
              ). intros. destruct H as [H1 H2]. apply H2. Qed.
Check Opposite_Functor.

(* another way of showing the same instance above:
Definition Opposite_Functor_v2 `(catC: Category) `(catD: Category) 
                            (F: catC -> catD)
                            (fmapF: forall (a b: catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                            `(FunctF: Functor catC catD F fmapF): 
                                `(Functor (Dual_Category catC) (Dual_Category catD) F (fun a b => fmapF b a)).
Proof. refine (@mk_Functor
                (Dual_Category catC) 
                (Dual_Category catD)
                F
                (fun a b => fmapF b a)
                (fun a => (@preserve_id catC catD F fmapF FunctF a)) 
                (fun a b c f g => (@preserve_comp catC catD F fmapF FunctF c b a g f))
              ).
Defined.
*)

Definition Opposite_Opposite_Functor `(catC: Category) `(catD: Category) 
                                     (F: obj (Dual_Category catC) -> obj (Dual_Category catD))
                                     (fmapF: forall (a b: obj (Dual_Category catC)) (f: arrow (Dual_Category catC) b a), 
                                        (arrow (Dual_Category catD) (F b) (F a)))
                                     `(FunctF: Functor (Dual_Category catC) (Dual_Category catD) F fmapF):
                                        (Functor catC catD F (fun a b => fmapF b a)).
Proof. refine (@mk_Functor
                catC 
                catD
                F
                (fun a b => fmapF b a)
                (fun a => (@preserve_id (Dual_Category catC) (Dual_Category catD) F fmapF FunctF a)) 
                (fun a b c f g => (@preserve_comp (Dual_Category catC) (Dual_Category catD) F fmapF FunctF c b a g f))
              ).
Defined.
Check Opposite_Opposite_Functor.

(** TODO:= prove the theorem here: oppositing is involutive **)

(*define how the identity functor behaves on objects and morphisms*)
Definition id {catC: Category} (a: obj catC) := a.
Definition idf {catC: Category} {a b: obj catC} (f: arrow catC b a) := f.

(** the identity functor **)
Program Instance IdentityFunctor (catC: Category): (@Functor catC catC id (fun a b f => (@idf catC a b f))).
Check IdentityFunctor.

(*define how the functor composition behaves on objects and morphisms*)
Definition comp_obj_FG  {catC catD catE: Category} {F: obj catC -> obj catD} {G: obj catD -> obj catE} (a: obj catC) := G (F a).
Definition comp_morp_FG {catC catD catE: Category} {F: obj catC -> obj catD} {G: obj catD -> obj catE} 
                                {fmapF  : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a))}
                                {fmapG  : forall (a b: obj catD) (f: arrow catD b a), (arrow catE (G b) (G a))}
                                (a b: obj catC) (f: (arrow catC b a)) := fmapG _ _ (fmapF _ _ f).

(**functors compose**)
Program Instance Compose_Functors (catC catD catE: Category) (F: obj catC -> obj catD) (G: obj catD -> obj catE) 
                                  (fmapF  : forall (a b: obj catC) (f: arrow catC b a), (arrow catD (F b) (F a)))
                                  (FunctF: @Functor catC catD F fmapF) 
                                  (fmapG  : forall (a b: obj catD) (f: arrow catD b a), (arrow catE (G b) (G a)))
                                  (FunctG: @Functor catD catE G fmapG):
                                  (@Functor catC catE (@comp_obj_FG catC catD catE F G) (@comp_morp_FG catC catD catE F G fmapF fmapG)).
Obligation 1. unfold comp_obj_FG, comp_morp_FG. remember (@preserve_id catC catD F fmapF FunctF a).
  remember (@preserve_id catD catE G fmapG FunctG (F a)). rewrite <- e0. rewrite e. reflexivity. Qed.
Next Obligation. unfold comp_obj_FG, comp_morp_FG. remember (@preserve_comp catC catD F fmapF FunctF a b c f g).
  remember (@preserve_comp catD catE G fmapG FunctG (F a) (F b) (F c) (fmapF _ _ f) (fmapF _ _ g)).
  rewrite <- e0. rewrite e. reflexivity. Qed.
Check Compose_Functors.

(** constant functor **)
Definition Constant_Functor `(catC: Category) `(catD: Category) (const: obj catD): 
                                              `(Functor catC catD (fun _ => const) (fun _ _ _ => (@identity catD const))).
Proof. refine(@mk_Functor
               catC
               catD _ _ _ _
             ).
       intros. reflexivity.
       intros. simpl. rewrite identity_f; reflexivity.
Defined.
Check Constant_Functor.

(* obligated fmap *)

Class Functor2 `(catC: Category) `(catD: Category) (F: obj catC -> obj catD): Type :=
  mk_Functor2
  {
    fmap2            : forall {a b: obj catC} (f: arrow catC b a), (arrow catD (F b) (F a));
    preserve_id2     : forall {a: obj catC}, fmap2 (@identity catC a) = (@identity catD (F a));
    preserve_comp2   : forall {a b c: obj catC} (f: arrow catC b a) (g : arrow catC c b), fmap2 (g o f) = (fmap2 g) o (fmap2 f)
  }.
Check Functor2.

(*
Program Instance IdentityFunctor2 (catC: Category): 
   (@Functor2 catC catC (fun a => id a)).
Check IdentityFunctor2.
*)

Definition Opposite_Functor2 (catC: Category) `(catD: Category) 
                             (F: obj catC -> obj catD)
                             (FunctF: Functor2 catC catD F ): (Functor2 (Dual_Category catC) (Dual_Category catD) F).
Proof. refine (@mk_Functor2
                (Dual_Category catC)
                (Dual_Category catD)
                F
                (fun a b => (@fmap2 catC catD F FunctF b a))
                (fun a => (@preserve_id2 catC catD F FunctF a)) 
                (fun a b c f g => (@preserve_comp2 catC catD F FunctF c b a g f))).
Qed. 
Check Opposite_Functor2.

Definition Opposite_Opposite_Functor2 (catC: Category) (catD: Category) 
                                     (F: obj (Dual_Category catC) -> obj (Dual_Category catD))
                                     (FunctF: Functor2 (Dual_Category catC) (Dual_Category catD) F): (Functor2 catC catD F).
Proof. refine (@mk_Functor2
                catC 
                catD
                F
                (fun a b => (@fmap2 (Dual_Category catC) (Dual_Category catD) F FunctF b a))
                (fun a => (@preserve_id2 (Dual_Category catC) (Dual_Category catD) F FunctF a)) 
                (fun a b c f g => (@preserve_comp2 (Dual_Category catC) (Dual_Category catD) F FunctF c b a g f))
              ).
Defined.
Check Opposite_Opposite_Functor2.

(**functors compose**)
Definition Compose_Functors2 (catC catD catE: Category) (F: obj catC -> obj catD) (G: obj catD -> obj catE) 
                             (FunctF : @Functor2 catC catD F) 
                             (FunctG : @Functor2 catD catE G): (@Functor2 catC catE (@comp_obj_FG catC catD catE F G)).
Proof. refine (@mk_Functor2
                catC
                catE
                (fun a => G (F a))
                (fun a b f => ((@fmap2 catD catE G FunctG _ _ (@fmap2 catC catD F FunctF a b f))))
                _ _ ).
      - intros. destruct catC, catD, catE, FunctF, FunctG. simpl in *.
        specialize (preserve_id4 (F a)). rewrite <- preserve_id4. rewrite preserve_id3. reflexivity.
      - intros. destruct catC, catD, catE, FunctF, FunctG. simpl in *.
        rewrite <- preserve_comp4. rewrite preserve_comp3. reflexivity.
Defined.
Check Compose_Functors2.

Definition IdentityFunctor2 (catC: Category): (@Functor2 catC catC id).
Proof. refine (@mk_Functor2
                catC
                catC
                id
                (fun a b f => (@idf catC a b f))
                _ _ ).
        - intros. unfold idf. simpl; reflexivity.
        - intros. unfold idf; reflexivity.
Defined.
Check IdentityFunctor2.

(** constant functor **)
Definition Constant_Functor2 (catC: Category) (catD: Category) (const: obj catD): 
                            (Functor2 catC catD (fun _ => const)).
Proof. refine(@mk_Functor2
               catC
               catD
               (fun _     => const)
               (fun _ _ _ => (@identity catD const))
               _ _
             ).
       - intros. reflexivity.
       - intros. simpl. rewrite identity_f; reflexivity.
Defined.
Check Constant_Functor2.

End Make.
