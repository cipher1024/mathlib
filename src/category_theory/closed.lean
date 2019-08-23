
-- import .tac
import tactic.reassoc_axiom
import category_theory.products.bifunctor
import category_theory.natural_transformation
import category_theory.category
import category_theory.adjunction
import category_theory.opposites
import category_theory.products
-- import category_theory.functor_category
-- import category_theory.natural_isomorphism
import category_theory.monoidal.category
import category_theory.monoidal.functor

universes v v' u u'

namespace category_theory

-- variables (C : Type u) [𝒞 : category.{v} C] -- [𝒟 : monoidal_category.{v} C]
-- include 𝒞

-- local notation `𝟙_` := monoidal_category.tensor_unit
local notation `α_` := monoidal_category.associator
local notation `λ_` := monoidal_category.left_unitor
local notation `ρ_` := monoidal_category.right_unitor
-- #exit

class closed_category (C : Type u) [𝒞 : category.{v} C] [has_one C] :=
(hom_obj : C → C → C)
(infix ` ⇒ `:50 := hom_obj)
(hom_map : Π {X₀ X₁ Y₀ Y₁ : C} (f : X₀ ⟶ Y₀) (g : X₁ ⟶ Y₁), Y₀⇒X₁ ⟶ X₀⇒Y₁)
(infix ` ⇒' `:50 := hom_map)
(notation `𝟙_` := 1)
(hom_map_id : Π {X Y : C}, 𝟙 X ⇒' 𝟙 Y = 𝟙 (X ⇒ Y))
(hom_map_comp : Π {X₀ X₁ Y₀ Y₁ Z₀ Z₁ : C} (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀) (f₁ : Z₁ ⟶ Y₁) (g₁ : Y₁ ⟶ X₁),
                  (g₁ ⇒' f₀) ≫ (f₁ ⇒' g₀) = (f₁ ≫ g₁ ⇒' f₀ ≫ g₀))
(i_hom : Π (X : C), X ⟶ (1 ⇒ X))
(i_hom_naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), f ≫ i_hom Y = i_hom X ≫ (𝟙 1 ⇒' f))
(i_inv : Π (X : C), (𝟙_ ⇒ X) ⟶ X)
(i_inv_naturality : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (𝟙 𝟙_ ⇒' f) ≫ i_inv Y = i_inv X ≫ f)
(i_hom_inv_id : ∀ ⦃X⦄, i_hom X ≫ i_inv X = 𝟙 X)
(i_inv_hom_id : ∀ ⦃X⦄, i_inv X ≫ i_hom X = 𝟙 (𝟙_ ⇒ X))
(j_hom : Π X : C, 𝟙_ ⟶ (X ⇒ X))
(j_ex_naturality : Π {X X' : C} (f : X ⟶ X'), j_hom X' ≫ (f ⇒' 𝟙 _) = j_hom X ≫ (𝟙 _ ⇒' f))
(L_hom : Π X Y Z : C, (Y ⇒ Z) ⟶ ((X ⇒ Y) ⇒ (X ⇒ Z)))
(L_ex_naturality_X : Π {X X' Y Z : C} (f : X ⟶ X'), L_hom X Y Z ≫ (f ⇒' 𝟙 _ ⇒' 𝟙 _) = L_hom X' Y Z ≫ (𝟙 _ ⇒' (f ⇒' 𝟙 _)))
(L_naturality_Y : Π {X Y Y' Z : C} (f : Y ⟶ Y'), (f ⇒' 𝟙 Z) ≫ L_hom X Y Z = L_hom X Y' Z ≫ (𝟙 _ ⇒' f ⇒' 𝟙 _))
(L_naturality_Z : Π {X Y Z Z' : C} (f : Z ⟶ Z'), (𝟙 Y ⇒' f) ≫ L_hom X Y Z' = L_hom X Y Z ≫ (𝟙 _ ⇒' (𝟙 _ ⇒' f)))
(law1 : ∀ X Y, j_hom Y ≫ L_hom X Y Y = j_hom (X ⇒ Y))
(law2 : ∀ X Y, L_hom X X Y ≫ (j_hom X ⇒' 𝟙 _) = i_hom _)
(law3 : ∀ Y Z, L_hom 𝟙_ Y Z ≫ (i_hom Y ⇒' 𝟙 _) = (𝟙 _ ⇒' i_hom Z))
(law4 : ∀ X Y U V, L_hom X U V ≫ L_hom (X ⇒ Y) (X ⇒ U) (X ⇒ V) ≫ (L_hom X Y U ⇒' 𝟙 _) = L_hom Y U V ≫ (𝟙 _ ⇒' L_hom X Y V))
-- (bij : Π X Y Z : C, ((X ⊗ Y) ⟶ Z) ≃ (X ⟶ (Y ⇒ Z : C)))
-- (bij_unit : 𝟭 C )
-- (bijj : Π X Y Z : C, ((X ⊗ Y) ⇒ Z) ≅ (X ⇒ (Y ⇒ Z)))
-- ()
(bij : Π X Y, function.bijective (λ f : X ⟶ Y, j_hom X ≫ (𝟙 _ ⇒' f))) --(X ⟶ Y) ≃ (𝟙_ _ ⟶ (X ^ Y)))
-- (hom_curry : Π X Y Z : C, ((X ⊗ Y : C) ⟶ Z) ≅ ((X : C) ⟶ (hom_obj Y Z)))

namespace closed_category

variables (C : Type u)
-- omit 𝒞
variables [𝒞 : category.{v+1} C] [has_one C] [𝒟 : closed_category.{v+1} C]
include 𝒞 𝒟

infixr ` ⇒ `:40 := hom_obj
-- #print ⇒
infixr ` ⇒' `:40 := hom_map
local notation `𝟙_` := 1

open opposite has_hom.hom category_theory.bifunctor monoidal_category

local attribute [simp] hom_map_comp hom_map_id i_inv_hom_id i_hom_inv_id

reassoc_axiom hom_map_comp
reassoc_axiom i_inv_hom_id
reassoc_axiom i_hom_inv_id
variables (C)

@[simp]
def Hom : (Cᵒᵖ × C) ⥤ C :=
{ obj := λ X, hom_obj.{v+1} (unop X.1) X.2,
  map := λ X Y f, hom_map.{v+1} f.1.unop f.2 }

-- #check @right.{} (Cᵒᵖ) _ C 𝒞' C 𝒞' (Hom C) (op $ 𝟙_ C)

def i : 𝟭 C ≅ right.{v v v u u u} (Hom.{v} C) (op 𝟙_) :=
{ hom := { app := λ X, i_hom.{v+1} X,
           naturality' := i_hom_naturality },
  inv := { app := λ X, i_inv.{v+1} X,
           naturality' := i_inv_naturality } }

-- def i_hom' (X : C) : X ⟶ (𝟙_ C ⇒ X) := (bij X _ X).to_fun (ρ_ _).hom
-- def i_inv' : Π (X : C), (𝟙_ C ⇒ X) ⟶ X := _
-- def j_hom' (X : C) : 𝟙_ C ⟶ (X ⇒ X) := (bij (𝟙_ _) X X).to_fun (λ_ _).hom
-- def L_hom' (X Y Z : C) : (Y ⇒ Z) ⟶ ((X ⇒ Y) ⇒ (X ⇒ Z)) := (bij _ _ _).to_fun $ (bij _ _ _).to_fun _

def bij' {X Y : C} (f : X ⟶ Y) : 𝟙_ ⟶ (hom_obj.{v+1} X Y) := j_hom.{v+1} X ≫ (𝟙 X ⇒' f)
-- def bij'' {X Y : C} (f : 𝟙_ ⟶ (hom_obj.{v+1} X Y)) : X ⟶ Y := (λ_ _).inv ≫ (bij.{v+1} (𝟙_ C) X Y).inv_fun f -- ≫ (f ^^ 𝟙 _) ≫ i_inv _

-- def bij''' {X Y : C} (f : X ⟶ Y) : 𝟙_ C ⟶ (hom_obj.{v+1} X Y) := _

-- def foo {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ (Y ⊗ Z) := _ ≫ (f ⊗ g)

-- def hom_equiv (X Y Z : C) : ((X ⊗ Y) ⟶ Z) ≅ (X ⟶ (Y ⇒ Z : C)) :=
-- { hom := (bij X Y Z),
--   inv := (bij X Y Z).symm }
-- 𝒞 Π (W X Y Z : C) (f : W )
/-
class heterogenous_assoc_op (C : Sort*) (hom : C → C → Sort*) (comp : Π (X Y Z : C), : hom X Y → hom Y Z → hom X Z) (id : out_param $ Π X, hom X X) :=
( )
-/
variables {C} {D : Type u'}
-- omit 𝒞
variables [𝒞' : category.{v'+1} D] [has_one D] [𝒟' : closed_category.{v'+1} D]
include 𝒞' 𝒟'
-- #exit
class closed_functor (F : C ⥤ D) :=
(trans : Π X Y : C, F.obj (X ⇒ Y) ⟶ F.obj X ⇒ F.obj Y)
(natural : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'), F.map (f ⇒' g) ≫ trans X Y' = trans X' Y ≫ (F.map f ⇒' F.map g))
(F₀ : 1 ⟶ F.obj 1)
(law1 : ∀ X, F₀ ≫ F.map (j_hom X) ≫ trans _ _ = j_hom _)
(law2 : ∀ X, trans 1 X ≫ (F₀ ⇒' 𝟙 _) = F.map (i_inv _) ≫ i_hom _)
(law3 : ∀ X Y Z : C, F.map (L_hom X Y Z) ≫ trans _ _ ≫ (𝟙 _ ⇒' trans _ _) =
                     trans Y Z ≫ L_hom (F.obj X) _ _ ≫ (trans _ _ ⇒' 𝟙 _))

class strong_closed_functor (F : C ⥤ D)
extends closed_functor F :=
(trans_iso : Π X Y, is_iso (trans X Y))
(F₀_iso : is_iso F₀)

open closed_functor

class closed_nat_trans {F G : C ⥤ D} [closed_functor F] [closed_functor G] (a : nat_trans F G) :=
(law1 : F₀ F ≫ a.app _ = F₀ G)
(law2 : Π X Y, trans F X Y ≫ (𝟙 _ ⇒' a.app _) = a.app _ ≫ trans G X Y ≫ (a.app _ ⇒' 𝟙 _))

variables (X Y Z : C)

-- def hom_equiv_hom (f : X ⊗ Y ⟶ Z) : (X ⟶ Y ⇒ Z) := -- _ ≫ (𝟙 _ ⇒' f)
-- (ρ_ _).inv ≫ (𝟙 _ ⊗ j_hom Y) ≫ _ ≫ (𝟙 _ ⇒' f)
-- def hom_equiv_inv (f : X ⟶ Y ⇒ Z) : (X ⊗ Y ⟶ Z) := _

-- def hom_equiv₂ (X Y Z : C) : ((X ⊗ Y) ⟶ Z) ≅ (X ⟶ (Y ⇒ Z : C)) :=
-- { hom := hom_equiv_hom C X Y Z,
--   inv := hom_equiv_inv C X Y Z, } -- (bijj X Y Z).inv }
-- (bijj X Y Z).hom ≫

-- @[simp]


-- def hom_equiv' (X Y Z : C) : ((X ⊗ Y) ⇒ Z) ≅ (X ⇒ (Y ⇒ Z : C)) :=
-- { hom := (bij _ _ _).to_fun $ (bij _ _ _).to_fun $ (α_ _ _ _).hom ≫ (bij _ _ _).inv_fun (𝟙 _),
--   inv := (bij _ _ _).to_fun $ (α_ _ _ _).inv ≫ (bij _ _ _).inv_fun ((bij _ _ _).inv_fun (𝟙 _)) }

end closed_category

@[simp]
lemma equiv_to_fun {X Y : Sort*} (f : X ≃ Y) : f.to_fun = f := rfl

@[simp]
lemma equiv_inv_fun {X Y : Sort*} (f : X ≃ Y) : f.inv_fun = f.symm := rfl

instance (C : Type u) [category C] [monoidal_category C] : has_one C :=
⟨ monoidal_category.tensor_unit C ⟩
open closed_category bifunctor monoidal_category opposite

-- set_option pp.universes true

class closed_monoidal_category (C : Type u)
  [category.{v+1} C] [monoidal_category C]
extends closed_category C :=
(adj : Π Y : C, left.{v v v u u} (tensor C) (Y) ⊣ right.{v v v u} (Hom C) (op Y) )

variables {C : Type u} [𝒞 : category.{v+1} C]
          [monoidal_category C]
          [closed_monoidal_category C]
variables (X Y Z : C)
include 𝒞

def hom_bij : (X ⊗ Y ⟶ Z) ≃ (X ⟶ Y ⇒ Z) :=
((closed_monoidal_category.adj.{v} Y).hom_equiv X Z)

def indirect_iso (h : Π Z : C, (Z ⟶ X) ≃ (Z ⟶ Y))
  (Hnat : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), (h Z').to_fun (f ≫ g) = f ≫ (h Z).to_fun g) :
  X ≅ Y :=
yoneda.ext _ _ (λ Z, (h Z).to_fun) (λ Z, (h Z).inv_fun)
  (λ Z f, equiv.left_inv _ _) (λ Z f, equiv.right_inv _ _)
  @Hnat

def equiv_of_iso (h : X ≅ Y) : (X ⟶ Z) ≃ (Y ⟶ Z) :=
{ to_fun := λ f, h.inv ≫ f,
  inv_fun := λ f, h.hom ≫ f,
  left_inv := λ f, iso.hom_inv_id_assoc _ _,
  right_inv := λ f, iso.inv_hom_id_assoc _ _ }

@[simp]
lemma equiv_of_iso_coe_to_fun (h : X ≅ Y) (f : X ⟶ Z) : equiv_of_iso X Y Z h f = h.inv ≫ f := rfl

@[simp]
lemma tensor_map_eq_tensor_hom {X' Y' : C} (f : X ⟶ Y) (f' : X' ⟶ Y') :
  (tensor C).map ((f, f') : (X, X') ⟶ (Y, Y')) = f ⊗ f' := rfl

@[simp]
lemma tensor_obj_eq : (tensor C).obj ((X, Y)) = X ⊗ Y := rfl

def hom_indirect (K : C) : (K ⟶ X ⇒ Y ⇒ Z) ≃ (K ⟶ X ⊗ Y ⇒ Z) :=
calc  (K ⟶ X ⇒ Y ⇒ Z)
    ≃ (K ⊗ X ⟶ Y ⇒ Z) : (hom_bij _ _ _).symm
... ≃ ((K ⊗ X) ⊗ Y ⟶ Z) : (hom_bij _ _ _).symm
... ≃ (K ⊗ (X ⊗ Y) ⟶ Z) : equiv_of_iso _ _ _ (α_ _ _ _)
... ≃ (K ⟶ X ⊗ Y ⇒ Z) : (hom_bij _ _ _)

variables (A B : C) (f : A ⟶ B)

def hom_iso : X ⇒ Y ⇒ Z ≅ X ⊗ Y ⇒ Z :=
indirect_iso _ _ (hom_indirect X Y Z)
(λ K K' f g, by { have := nat_trans.naturality_assoc ((closed_monoidal_category.adj.{v} $ X ⊗ Y).unit) f _,
                  simp at this,
                  simp [hom_indirect
                            ,hom_bij,equiv_to_fun,equiv.trans,(∘)
                            ,adjunction.hom_equiv_naturality_right
                            ,adjunction.hom_equiv_naturality_left_symm
                            ,(associator_inv_naturality_assoc _ _ _ _).symm],
                  rw this, clear this, simp })

def eval : (X ⇒ Y) ⊗ X ⟶ Y := (hom_bij _ _ _).inv_fun (𝟙 _)

lemma comp_eval (f : X ⟶ Y ⇒ Z) : (f ⊗ 𝟙 Y) ≫ eval Y Z = (hom_bij X Y Z).inv_fun f :=
by simp [hom_bij,eval,equiv_inv_fun]; erw [category.id_comp]

lemma hom_bij_comp_eval (f : X ⊗ Y ⟶ Z) : ((hom_bij X Y Z).to_fun f ⊗ 𝟙 Y) ≫ eval Y Z = f :=
by rw [comp_eval,equiv.left_inv]

set_option pp.universes true

variables {C} {D : Type u'}
-- omit 𝒞
variables [𝒞' : category.{v'+1} D] [monoidal_category D]
          [𝒟' : closed_monoidal_category.{v'} D]
include 𝒞' 𝒟'

open closed_monoidal_category lax_monoidal_functor
-- #print ⇒'
-- #print =

instance (F : C ⥤ D) [lax_monoidal_functor.{v+1 v'+1} F] : closed_functor F := sorry
-- { F₀ := ε F,
--   trans := λ X Y, ((adj _).hom_equiv _ _).to_fun (μ F _ _ ≫ F.map (eval _ _)),
--   natural :=
--     begin intros, simp [eval,hom_bij,left,right,Hom], dsimp [Hom], -- simp,
--     have := nat_trans.naturality_assoc ((adj.{v' u'} (F.obj X)).unit) (F.map (f ⇒' g)) _,
--     -- have := ((adj.{v' u'} ((F.to_functor).obj X)).unit).app ((F.to_functor).obj (X ⇒ Y)),
--     simp at this, rw this, dsimp [Hom], rw [hom_map_comp,hom_map_comp,nat_trans.naturality ((adj.{v u} X').counit)], -- [← F.map_id,← F.map_id,← F.map_id],
--     have := ((adj.{v' u'} (F.obj X')).unit).app (F.obj (X' ⇒ Y)),
--     dsimp [left,right,tensor,Hom] at this,
--     congr' 1,
--     -- conv { to_rhs, rw [← F.to_functor.map_id,← F.to_functor.map_id, ← F.to_functor.map_comp], }
--  end }

-- open closed_category.closed_functor
-- #check functor.map_comp
instance to_lax_monoidal_functor (F : C ⥤ D) [closed_functor F] : lax_monoidal_functor.{v+1 v'+1} F := sorry
-- { ε := F₀ _,
--   μ := λ X Y, (hom_bij _ _ _).inv_fun (F.map ((hom_bij _ _ _).to_fun $ 𝟙 _) ≫ trans _ _ _),
--   μ_natural' := by { intros,
--                      have := nat_trans.naturality ((adj.{v' u'} (F.obj X')).counit) (F.map (f ⊗ g)),
--                      simp at this, dsimp [hom_bij,Hom], -- rw ← this,
--                      simp [Hom,this.symm], dsimp [Hom], -- rw functor.map_comp_symm_assoc,
--                      simp [functor.map_comp_symm_assoc,-functor.map_comp],  },
--   associativity' := _,
--   left_unitality' := _,
--   right_unitality' := _ }

end category_theory
