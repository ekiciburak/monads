Require Import Morphisms.
Import ProperNotations.
Require Import SetoidClass.
Require notation.

Module Make(Import M: notation.T).

Record Category: Type := 
 mk_Category 
 {
     obj : Type;
     arrow: obj -> obj -> Type;
     identity : forall a, arrow a a;
     comp : forall {a b c}, (arrow a b) -> (arrow b c) -> (arrow a c);
     assoc : forall {a b c d} (f : arrow b a) (g : arrow c b) (h : arrow d c), comp h (comp g f) = comp (comp h g) f;
     identity_f: forall {a b} (f: arrow b a), comp (@identity b) f = f;
     f_identity: forall {a b} (f: arrow b a), comp f (@identity a) = f 
  }.
Check obj.
Check arrow.

Notation " x 'o' y " := (comp _ x y) (at level 40, left associativity). 

Definition Product_Category (catC catD: Category) : Category.
Proof. 
  refine (@mk_Category 
           (obj catC * obj catD)%type
           (fun a b => (arrow catC (fst a) (fst b) * arrow catD (snd a) (snd b))%type)
           (fun a => (identity catC (fst a), identity catD (snd a)))
           (fun a b c f2 f1 => (fst f2 o fst f1, snd f2 o snd f1))
           _ _ _
         ). 
  intros. setoid_rewrite <- assoc. reflexivity. 
  intros. simpl. specialize (@identity_f catC (fst a) (fst b) (fst f)). intros. rewrite H.
  intros. simpl. specialize (@identity_f catD (snd a) (snd b) (snd f)). intros. rewrite H0.
    destruct f. simpl. reflexivity.
  intros. simpl. specialize (@f_identity catC (fst a) (fst b) (fst f)). intros. rewrite H.
  intros. simpl. specialize (@f_identity catD (snd a) (snd b) (snd f)). intros. rewrite H0.
    destruct f. simpl. reflexivity.
Defined.
Check Product_Category.

Definition Dual_Category (catC: Category) : Category.
Proof. 
  refine (@mk_Category 
           (obj catC)%type
           (fun a b => (arrow catC b a %type))
           (fun a => (@identity catC a))
           (fun a b c f1 f2 => f2 o f1)
           _ _ _ 
         ). 
  intros. setoid_rewrite <- assoc. reflexivity.
  intros.  specialize (@f_identity catC b a f). intros. exact H.
  intros.  specialize (@identity_f catC b a f). intros. exact H. 
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

End Make.