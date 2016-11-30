(** **********************************************************

Contents:

- Definition of the discrete category of a type

Written by: Anders Mörtberg, 2016

************************************************************)

Require Import UniMath.Foundations.Basics.PartD.
Require Import UniMath.Foundations.Basics.Propositions.
Require Import UniMath.Foundations.Basics.Sets.

Require Import UniMath.CategoryTheory.precategories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.UnicodeNotations.

(** * Discrete precategories *)
Section DiscretePrecategory.

Variable (A : UU).

Definition discrete_precategory_data : precategory_data.
Proof.
mkpair.
- apply (A,,paths).
- mkpair; [ apply idpath | apply @pathscomp0 ].
Defined.

Definition is_precategory_discrete_precategory_data : is_precategory discrete_precategory_data.
Proof.
split; [split|]; trivial; intros.
+ apply pathscomp0rid.
+ apply path_assoc.
Qed.

Definition discrete_precategory : precategory :=
  (discrete_precategory_data,,is_precategory_discrete_precategory_data).

Lemma has_homsets_discrete_precategory (H : isofhlevel 3 A) : has_homsets discrete_precategory.
Proof.
intros ? ? ? ? ? ?; apply H.
Qed.

(** To define a functor out of a discrete category it suffices to give a function *)
Lemma functor_discrete_precategory (D : precategory) (f : A → D) :
  functor discrete_precategory D.
Proof.
mkpair.
+ mkpair.
  - apply f.
  - intros s t []; apply identity.
+ abstract (now split; [intro|intros a b c [] []; simpl; rewrite id_left]).
Defined.

Definition discrete_fun_is_nat_trans {D : precategory} (Dhom : has_homsets D)
           {f g : functor_precategory discrete_precategory D Dhom}
           (F : Π x : A , (pr1 f) x --> (pr1 g) x)
  : is_nat_trans (pr1 f) (pr1 g) F.
  Proof.
    intros x y h.
    rewrite h.
    rewrite (pr1 (pr2 f)) , (pr1 (pr2 g)).
    rewrite (id_left (F y)) , (id_right (F y)).
    reflexivity.
  Defined.

End DiscretePrecategory.