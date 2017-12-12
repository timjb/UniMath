
(*Require Import UniMath.CategoryTheory.limits.binproducts.*)
Require Import UniMath.CategoryTheory.limits.products.


Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.categories.category_hset.
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

Definition underlying_precat (T: LawvereTheory) := pr1 (pr1 T).

Definition generating_object (T: LawvereTheory) := pr1 (pr2 T).

Section FinProductPreservation.

Context {C D : precategory}.
Variable (F : functor C D).

Definition preserves_fin_products : UU :=
    ∏ (n : nat),
    ∏ (d : ∏ (i : stn n), C),
    ∏ (p : C),
    ∏ (cc : ∏ (i : stn n), p --> d i),
      isProductCone (stn n) C d p cc ->
      isProductCone (stn n) D (fun i => F (d i)) (F p) (fun i => functor_on_morphisms F (cc i)).


End FinProductPreservation.

Lemma comp_of_FP_functors_is_FP : 
∏ (C D E : precategory) (F1 : functor C D) (F2 : functor D E), 
(preserves_fin_products F1) -> (preserves_fin_products F2) -> (preserves_fin_products (F1 ∙ F2)).
Proof.
  intros.
  unfold preserves_fin_products.
  intros.
  apply X0.
  apply X.
  assumption.
Defined.

Section Models.

Variable (T : LawvereTheory).

Definition isModel (A : functor (pr1 T) HSET) := preserves_fin_products A.
Definition Model := total2 (fun x => isModel x).

End Models.

Section Morphisms.

Context {T1 T2: LawvereTheory}.

Variable (F : functor (underlying_precat T1) (underlying_precat T2)).

Definition is_Lawvere_map := (F (generating_object T1) = generating_object T2) × (preserves_fin_products F).

End Morphisms.

Lemma identity_is_Lawvere_map : ∏ T: LawvereTheory, is_Lawvere_map (functor_identity (underlying_precat T)).
Proof.
  intro T.
  unfold is_Lawvere_map.
  split.
    - simpl.
      reflexivity.
    - unfold preserves_fin_products.
      simpl.
      tauto.
Defined.



(* todo: category of Lawvere theories *)
(* todo: projections *)
(* todo: models *)