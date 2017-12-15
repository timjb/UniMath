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

Definition is_N_Fold_Product {C : precategory} (t p : C) (n : nat) :=
  total2 (fun projections => isProductCone (stn n) C (fun _ => t) p projections).

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

Print is_N_Fold_Product.

SearchAbout precategory_ob_mor.

Print Scopes.

Definition nat_precategory_data : UU := ∑ (mor : nat -> nat -> UU), (∏ n : nat, mor n n) × (∏ (n m k : nat) (f : mor n m) (g : mor m k), mor n k).

Definition nat_precategory_morphisms ( C : nat_precategory_data ) :
       nat ->  nat -> UU := pr1 C.

Definition nat_precategory_identity (C : nat_precategory_data)
  : ∏ n : nat, nat_precategory_morphisms C n n
  := pr1 (pr2 C).

Definition nat_precategory_compose (C : nat_precategory_data) ( n m k : nat )
  : (nat_precategory_morphisms C n m) -> (nat_precategory_morphisms C m k) -> nat_precategory_morphisms C n k
  := pr2 (pr2 C) n m k.

Definition precategory_data_from_nat_precategory_data (C : nat_precategory_data) : precategory_data  
  := precategory_data_pair (precategory_ob_mor_pair nat (nat_precategory_morphisms C)) (nat_precategory_identity C) (nat_precategory_compose C). 

Definition is_nat_category (C : nat_precategory_data) 
:= (is_precategory (precategory_data_from_nat_precategory_data C)) × has_homsets (precategory_data_from_nat_precategory_data C).

Definition is_precategory_from_is_nat_category {C : nat_precategory_data} (is : is_nat_category C) := pr1 is.

Definition has_homsets_from_is_nat_category {C : nat_precategory_data} (is : is_nat_category C):= pr2 is.

Definition nat_category : UU := ∑ (C : nat_precategory_data), is_nat_category C.

Definition precategory_from_nat_category (C : nat_category) : precategory 
:= precategory_pair (precategory_data_from_nat_precategory_data (pr1 C)) (is_precategory_from_is_nat_category (pr2 C)). 

Coercion category_from_nat_category (C: nat_category) : category := category_pair (precategory_from_nat_category  C) (has_homsets_from_is_nat_category (pr2 C)). 

Definition is_Lawvere_Theory (C : nat_category) : UU := ∏ n : nat, @is_N_Fold_Product (precategory_from_nat_category C) 1 n n.

Definition Lawvere_Theory : UU := ∑ (C : nat_category), is_Lawvere_Theory C.

Coercion category_from_Lawvere_Theory (C : Lawvere_Theory) := category_from_nat_category (pr1 C).

Definition Lawvere_map_data (C D : Lawvere_Theory) := ∏ n m : nat, C ⟦ n , m ⟧ -> D ⟦ n , m ⟧. 

Definition functor_data_from_Lawvere_map_data {C D : Lawvere_Theory} (F : Lawvere_map_data C D): functor_data C D
  := @mk_functor_data C D (idfun nat) F.

Print Scopes.



