
(*Require Import UniMath.CategoryTheory.limits.binproducts.*)
Require Import UniMath.CategoryTheory.limits.products.


Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Local Open Scope cat.

Section LawvereTheory.

Variable C : precategory.

Definition isNFoldProduct (t p : C) (n : nat) :=
  total2 (fun projections => isProductCone (stn n) C (fun _ => t) p projections).

Definition isGeneratingObject (t : C) :=
  ∏ (c : C), total2 (isNFoldProduct t c). (* probably need truncation *)

Definition isLawvereTheory :=
  total2 isGeneratingObject.

End LawvereTheory.

Definition LawvereTheory := total2 isLawvereTheory.

Section FinProductPreservation.

Context {C D : precategory}.
Variable (F : functor C D).

Definition preserves_fin_products (n : nat) (d : ∏ (i : stn n), C) (p : C)
  (cc : ∏ (i : stn n), p --> d i) : UU :=
    isProductCone (stn n) C d p cc ->
    isProductCone (stn n) D (fun i => F (d i)) (F p) (fun i => functor_on_morphisms F (cc i)).

End FinProductPreservation.

(* todo: category of Lawvere theories *)
(* todo: projections *)
(* todo: models *)