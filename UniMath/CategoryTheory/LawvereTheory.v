
(*Require Import UniMath.CategoryTheory.limits.binproducts.*)
Require Import UniMath.CategoryTheory.limits.products.


Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.FinOrdProducts.
Require Import UniMath.CategoryTheory.categories.category_hset.
Local Open Scope cat.

Section Lawvere_Theory.

(* Definition of a Lawvere Theory*)

Variable C : category.

Definition is_N_Fold_Product (t p : C) (n : nat) :=
  total2 (fun projections => isProductCone (stn n) C (fun _ => t) p projections).

Definition is_Generating_Object (t : C) :=
   ∥ ∏ (c : C), total2 (is_N_Fold_Product t c) ∥.

Definition is_Lawvere_Theory :=
  total2 is_Generating_Object × hasFinOrdProducts C.

End Lawvere_Theory.

Definition Lawvere_Theory := total2 is_Lawvere_Theory.

Coercion underlying_category (T : Lawvere_Theory) : category := pr1 T.

Definition generating_object (T : Lawvere_Theory) : T :=
  pr1 (pr1 (pr2 T)).

Section Finite_Product_Preservation.

Context {C D : precategory}.
Variable (F : functor C D).

Definition preserves_finite_products : UU :=
    ∏ (n : nat),
    ∏ (d : stn n -> C),
    ∏ (p : C),
    ∏ (cc : ∏ (i : stn n), p --> d i),
      isProductCone (stn n) C d p cc ->
      isProductCone (stn n) D (fun i => F (d i)) (F p) (fun i => functor_on_morphisms F (cc i)).

Lemma isaprop_preserves_finite_products : isaprop preserves_finite_products.
Proof.
  repeat (apply impred; intro).
  apply isapropiscontr.
Defined.

End Finite_Product_Preservation.

Lemma comp_of_fin_prod_preserving_functors_is_fin_prod_preserving : 
∏ (C D E : precategory) (F1 : functor C D) (F2 : functor D E), 
(preserves_finite_products F1) -> (preserves_finite_products F2) -> (preserves_finite_products (F1 ∙ F2)).
Proof.
  intros.
  unfold preserves_finite_products.
  intros.
  apply X0.
  apply X.
  assumption.
Defined.

Section Models.

Variable (T : Lawvere_Theory).

Definition is_Model (A : functor (pr1 T) HSET) := preserves_finite_products A.
Definition Model := total2 (fun x => is_Model x).

End Models.

Section Morphisms.

Context {T1 T2: Lawvere_Theory}.

Definition preserves_generating_object (F : functor  T1  T2) :=
   iso (F (generating_object T1)) (generating_object T2).

Definition is_Lawvere_map (F : functor  T1 T2) :=
  (preserves_generating_object F) × (preserves_finite_products F).

Definition Lawvere_maps := total2 is_Lawvere_map.

End Morphisms.

Lemma identity_is_Lawvere_map : ∏ T: Lawvere_Theory, is_Lawvere_map (functor_identity T).
Proof.
  intro T.
  unfold is_Lawvere_map.
  split.
    - simpl.
      apply identity_iso.
    - unfold preserves_finite_products.
      simpl.
      tauto.
Defined.

Definition precategory_of_Lawvere_Theories_ob_mor : precategory_ob_mor.
Proof.
   unfold precategory_ob_mor.
   exists Lawvere_Theory.
   intros.
   exact (@Lawvere_maps X X0).
   Defined.

Definition precategory_of_Lawvere_Theories_data : precategory_data.
Proof.
   exists precategory_of_Lawvere_Theories_ob_mor.
   split.
   - intro c.
   destruct c.
   exists (functor_identity pr1).
   exact (identity_is_Lawvere_map _).
   - intros.
     exists ((pr1 X) ∙ (pr1 X0)).
     unfold is_Lawvere_map.
     split.
     + unfold preserves_generating_object. simpl.
       eapply iso_comp.
       -- apply functor_on_iso. exact (pr1 (pr2 X)).
       -- exact (pr1 (pr2 X0)).
     + apply comp_of_fin_prod_preserving_functors_is_fin_prod_preserving.
       exact (pr2 (pr2 X)).
       exact (pr2 (pr2 X0)).
Defined.

Definition precategory_of_Lawvere_Theories : precategory.
Proof.
  exists precategory_of_Lawvere_Theories_data.
  unfold is_precategory.
  split.
  split.
  - simpl.
    intros.
    unfold compose.
    unfold identity.
    apply total2_paths_equiv.
    use tpair.
    -- simpl.
       apply functor_identity_left.
    -- SearchAbout dirprod.
       apply dirprod_paths.
       --- simpl. 
           apply functor_on_iso_identity_iso_is_identity_iso.
  - simpl.
    intros.
    unfold compose.
    unfold identity.
    apply total2_paths_equiv.
    use tpair.
    -- simpl.
       apply functor_identity_right.
    -- apply isaprop_is_Lawvere_map.
  - intros a b c d f g h.
    apply total2_paths_equiv.
    use tpair.
    -- simpl.
       symmetry.
       apply (functor_assoc  (underlying_category a) (underlying_category b) (underlying_category c) (underlying_category d)).
    -- apply isaprop_is_Lawvere_map.
Qed.

(* todo: is Law univalent? *)
(* todo: models *)