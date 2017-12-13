
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

Definition underlying_category (T : Lawvere_Theory) : category := pr1 T.

Definition generating_object (T : Lawvere_Theory) : underlying_category T :=
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

Definition isModel (A : functor (pr1 T) HSET) := preserves_finite_products A.
Definition Model := total2 (fun x => isModel x).

End Models.

Section Morphisms.

Context {T1 T2: Lawvere_Theory}.

Definition preserves_generating_object (F : functor (underlying_category T1) (underlying_category T2)) :=
  ∥ iso (F (generating_object T1)) (generating_object T2) ∥.

Definition is_Lawvere_map (F : functor (underlying_category T1) (underlying_category T2)) :=
  (preserves_generating_object F) × (preserves_finite_products F).

Lemma isaprop_is_Lawvere_map (F : functor (underlying_category T1) (underlying_category T2)) : isaprop (is_Lawvere_map F).
Proof.
  apply isapropdirprod.
  + apply isapropishinh.
  + apply isaprop_preserves_finite_products.
Defined.

Definition Lawvere_maps := total2 is_Lawvere_map.

End Morphisms.

Lemma identity_is_Lawvere_map : ∏ T: Lawvere_Theory, is_Lawvere_map (functor_identity (underlying_category T)).
Proof.
  intro T.
  unfold is_Lawvere_map.
  split.
    - simpl.
      apply hinhpr.
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
       assert (preserves_generating_object (pr1 X0) -> preserves_generating_object (pr1 X) -> ishinh_UU (iso ((pr1 X0) ((pr1 X) (generating_object a))) (generating_object c))).
         apply (@factor_through_squash (iso (pr1 X0 (generating_object b)) (generating_object c)) (preserves_generating_object (pr1 X) -> _)).
           repeat (apply impred; intro).
           exact (pr2 t0).
         intro iso1.
         apply factor_through_squash.
           repeat (apply impred; intro).
           exact (pr2 t).
         intro iso2.
         apply hinhpr.
         eapply iso_comp.
          apply functor_on_iso. exact iso2.
          exact iso1.
       apply X1.
       exact (pr1 (pr2 X0)).
       exact (pr1 (pr2 X)).
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
    -- apply isaprop_is_Lawvere_map.
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
       apply (functor_assoc (underlying_category a) (underlying_category b) (underlying_category c) (underlying_category d)).
    -- apply isaprop_is_Lawvere_map.
Qed.

(* todo: is Law univalent? *)
(* todo: models *)