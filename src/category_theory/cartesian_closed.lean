
import category_theory.monoidal.category
import category_theory.category.Cat
import category_theory.monoidal.of_has_finite_products
import category_theory.closed
import category_theory.limits.shapes.finite_products
import category_theory.limits.preserves

universes v v' u u'

namespace category_theory
set_option pp.universes true

section preserves

variables {C : Type u} {D : Type u}
          [𝒞 : category.{v+1} C]
          [𝒟 : category.{v+1} D]
include 𝒞 𝒟

#check @limits.preserves_limits_of_shape

class preserves_finite_products (F : C ⥤ D) :=
(preserves : Π (J : Type v) [fintype J], limits.preserves_limits_of_shape (discrete J) F)


end preserves

open category_theory.limits

section defs

variables (C : Type u) [𝒞 : category.{v+1} C]
-- variables [𝒟 : monoidal_category.{v+1} C]  [closed_monoidal_category.{v} C]
-- variables [ℰ : has_finite_products.{v} C]
include 𝒞

-- #check @closed_monoidal_category.{v} C 𝒞 (@monoidal_of_has_finite_products C 𝒞 _)
-- #check (@monoidal_of_has_finite_products C 𝒞 ℰ)

local attribute [instance] monoidal_of_has_finite_products

class cartesian_closed_category
extends has_finite_products.{v} C,
        closed_monoidal_category.{v} C

class bicartesian_closed_category
extends cartesian_closed_category.{v} C,
        has_finite_coproducts.{v} C


end defs

#check Cat.category.{v+1 u}

instance Cat.ccc : @cartesian_closed_category Cat.{v u} Cat.category :=
{ has_limits_of_shape := λ J _, { has_limit := λ F, _ } }


end category_theory
