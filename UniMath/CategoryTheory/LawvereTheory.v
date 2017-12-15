Require Import UniMath.Foundations.Sets.
Require Import UniMath.MoreFoundations.Tactics.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.categories.category_hset.
Require Import UniMath.CategoryTheory.functor_categories.
Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.FinOrdProducts.


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

Context (T1 T2: Lawvere_Theory).

Definition preserves_generating_object (F : functor  T1  T2) :=
   iso (F (generating_object T1)) (generating_object T2).

Definition is_Lawvere_map (F : functor  T1 T2) :=
  (preserves_generating_object F) × (preserves_finite_products F).

Definition Lawvere_map := total2 is_Lawvere_map.

End Morphisms.

Coercion underlying_functor {A B : Lawvere_Theory} (F : Lawvere_map A B) : functor A B := pr1 F.
Definition generator_image_iso {A B : Lawvere_Theory} (F : Lawvere_map A B) : preserves_generating_object A B F := pr1 (pr2 F).
Definition finite_product_preservation {A B : Lawvere_Theory} (F : Lawvere_map A B) : preserves_finite_products F := pr2 (pr2 F).

Lemma identity_is_Lawvere_map : ∏ T: Lawvere_Theory, is_Lawvere_map T T (functor_identity T).
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
   exact (@Lawvere_map X X0).
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
     exists (underlying_functor X ∙ underlying_functor X0).
     unfold is_Lawvere_map.
     split.
     + unfold preserves_generating_object. simpl.
       eapply iso_comp.
       -- apply functor_on_iso. exact (generator_image_iso X).
       -- exact (generator_image_iso X0).
     + apply comp_of_fin_prod_preserving_functors_is_fin_prod_preserving.
       exact (finite_product_preservation X).
       exact (finite_product_preservation X0).
Defined.

Check idtoiso.

Lemma Lawvere_functor_path {A B : Lawvere_Theory} (F G : Lawvere_map A B)
  (e : underlying_functor F = underlying_functor G)
  (e2 : transportf (λ x : A ⟶ B, preserves_generating_object A B x) e (generator_image_iso F) = generator_image_iso G)
  : F = G.
Proof.
  apply total2_paths_equiv.
  use tpair.
  - assumption.
  - apply dirprod_paths.
    + fold (generator_image_iso G).
      rewrite <- e2.
      unfold is_Lawvere_map.
      rewrite transportf_dirprod.
      reflexivity.
    + apply isaprop_preserves_finite_products.
Defined.

Definition precategory_of_Lawvere_Theories : precategory.
Proof.
  exists precategory_of_Lawvere_Theories_data.
  unfold is_precategory.
  split.
  split.
  - intros A B F.
    use Lawvere_functor_path.
    + apply functor_identity_left.
    + unfold preserves_generating_object.
      rewrite (functtransportf (fun H : functor (underlying_category A) (underlying_category B) => H (generating_object A)) (fun X => iso X (generating_object B))).
      rewrite <- idtoiso_precompose_iso. Focus 2. apply homset_property.
      simpl.
      rewrite iso_comp_id_left.
      unfold compose. simpl. unfold generator_image_iso. simpl. unfold generating_object. simpl.
      rewrite functor_on_iso_id.
      rewrite iso_comp_id_left.
      reflexivity.
  - intros A B F.
    use Lawvere_functor_path.
    + apply functor_identity_right.
    + unfold preserves_generating_object.
      rewrite (functtransportf (fun H : functor (underlying_category A) (underlying_category B) => H (generating_object A)) (fun X => iso X (generating_object B))).
      rewrite (functor_identity_right_on_objects (underlying_category A) (underlying_category B) (underlying_functor F)).
      rewrite idpath_transportf.
      unfold compose. simpl. unfold generator_image_iso. simpl. unfold generating_object. simpl.
      rewrite iso_comp_id_right.
      apply identity_functor_on_iso.
  - intros A B C D F G H.
    symmetry.
    use Lawvere_functor_path.
    + apply functor_assoc.
    + unfold preserves_generating_object.
      rewrite (functtransportf (fun H : functor (underlying_category A) (underlying_category D) => H (generating_object A)) (fun X => iso X (generating_object D))).
      rewrite (functor_assoc_on_objects (underlying_category A) (underlying_category B) (underlying_category C) (underlying_category D) (underlying_functor F) (underlying_functor G) (underlying_functor H)).
      rewrite idpath_transportf.
      unfold compose. simpl. unfold generator_image_iso. simpl. unfold generating_object. simpl.
      rewrite iso_comp_assoc.
      rewrite functor_on_iso_comp.
      Search functor_on_iso.
      rewrite functor_composite_on_iso.
      apply idpath.
Defined.

(* todo: is Law univalent? *)
(* todo: models *)