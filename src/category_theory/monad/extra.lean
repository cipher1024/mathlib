
import data.list.min_max
import category_theory.monad.basic
import category_theory.monoidal.category
import category_theory.monoidal.functor
       .kleisli

namespace tactic

open nat

@[reducible]
meta def M := state_t (list (ℕ × string × string)) tactic

meta def M.trace (x y : expr) : M unit :=
do fmt_x ← to_string <$> monad_lift (pp x),
   fmt_y ← to_string <$> monad_lift (pp y),
   modify $ (::) (fmt_x.length, fmt_x, fmt_y)
meta def M.run (x : M unit) : tactic unit :=
do (_,xs) ← state_t.run x [],
   some m ← pure $ list.maximum $ xs.map prod.fst | pure (),
   xs.reverse.mmap' $ λ ⟨i,x,y⟩,
     let m := string.join (list.repeat " " $ m - i) in
     trace!"{x}{m} : {y}"

meta def show_types : option ℕ → expr → M unit
-- | (some 0) e := trace!"{e} : {infer_type e}"
| n e :=
do t@`(%%a ⟶ %%b) ← monad_lift (infer_type e) | monad_lift skip,
   M.trace e t,
   if n = some 0 then monad_lift skip
   else match e with
        | `(%%a ≫ %%b) :=
          show_types (pred <$> n) a >> show_types (pred <$> n) b
        | e :=
             let xs := e.get_app_args in
             xs.mmap' $ show_types (pred <$> n)
        end

namespace interactive

setup_tactic_parser

meta def show_types (n : parse (small_nat?)) : tactic unit :=
do `(%%a = %%b) ← target,
   trace"",
   (tactic.show_types n a).run,
   trace "=",
   (tactic.show_types n b).run

end interactive

end tactic

universes v₁ u₁ v₂ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory
variables {C : Type u₁} {D : Type u₂}
  [𝒞 : category.{v₁} C]
  [𝒟 : category.{v₂} D]
include 𝒞

namespace category_theory
open category
variables
  [monoidal_category C]
  [monoidal_category D]

class strong_functor (F : C ⥤ C) :=
(τ : Π (A B : C), A ⊗ F.obj B ⟶ F.obj (A ⊗ B))
-- (σ : Π (A B : C), F.obj A ⊗ B ⟶ F.obj (A ⊗ B))
(nat_τ : ∀ (A A' B B' : C) (f : A ⟶ A') (g : B ⟶ B'),
  (f ⊗ F.map g) ≫ τ A' B' = τ A B ≫ F.map (f ⊗ g))
-- (nat_σ : ∀ (A A' B B' : C) (f : A ⟶ A') (g : B ⟶ B'),
--   (F.map f ⊗ g) ≫ σ A' B' = σ A B ≫ F.map (f ⊗ g))
(law1 : ∀ X Y Z : C,
  τ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
  (α_ X Y (F.obj Z)).hom ≫ (𝟙 _ ⊗ τ _ _) ≫ τ _ _ )
(law2 : ∀ X : C, τ (𝟙_ _) X ≫ F.map (λ_ _).hom = (λ_ _).hom)
-- (law3 : ∀ X Y Z : C,
--   σ X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
--   (α_ (F.obj X) Y Z).inv ≫ (σ _ _ ⊗ 𝟙 _) ≫ σ _ _ )
-- (law4 : ∀ X : C, σ X (𝟙_ _) ≫ F.map (ρ_ _).hom = (ρ_ _).hom)

notation `τ_` := strong_functor.τ
-- notation `σ_` := strong_functor.σ

open strong_functor
attribute [reassoc] law1 law2 -- law3 law4
attribute [simp, reassoc] nat_τ -- nat_σ
local attribute [-simp] functor.map_comp nat_trans.naturality
local attribute [simp] functor.map_comp_symm     functor.map_comp_symm_assoc
                       nat_trans.naturality_symm nat_trans.naturality_symm_assoc

section strong_functor

variables {X Y Z X' Y' : C}
variables (F : C ⥤ C) [strong_functor F]

-- @[simp, reassoc]
-- lemma law1' (f : X ⟶ Y) (g : X' ⟶ Y') :
--   (F.map f ⊗ g) ≫ σ_ F _ _ = σ_ _ _ _ ≫ F.map (f ⊗ g) :=
-- by simp

@[simp, reassoc]
lemma law2' (f : X ⟶ Y) (g : X' ⟶ Y') :
  (f ⊗ F.map g) ≫ τ_ F _ _ = τ_ _ _ _ ≫ F.map (f ⊗ g) :=
by simp

-- -- lemma law3' : τ_ F (X ⊗ Y) Z ≫ F.map ((α_ X Y Z).hom) = _
-- lemma assoc_σ {X Y X' Y' Z : C} :
-- (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
--         (𝟙 (F.obj X) ⊗ σ_ F Y (F.obj Z)) = (τ_ _ _ _ ⊗ 𝟙 _) ≫ _ := _
-- -- (α_ X Y (F.obj Z)).hom ≫ (𝟙 _ ⊗ τ_ F _ _) = _

end strong_functor
-- #exit
class strong_monad (M : C ⥤ C) -- [monad M]
-- [strong_functor M] :=
extends monad M, strong_functor M :=
(τ_unit : ∀ A : C, τ (𝟙_ _) A = (λ_ _).hom ≫ M.map (λ_ _).inv)
(str_comm : ∀ X Y Z : C,
  (α_ X Y _).hom ≫ (𝟙 _ ⊗ τ _ _) ≫ τ _ _ =
  τ (X ⊗ Y) Z ≫ M.map (α_ X Y _).hom)
-- (str_comm' : ∀ X Y Z : C,
--   (α_ _ Y Z).inv ≫ (σ X _ ⊗ 𝟙 _) ≫ σ _ _ =
--   σ _ _ ≫ M.map (α_ X Y _).inv )
(str_η : ∀ X Y : C, (𝟙 X ⊗ (η_ M).app Y) ≫ τ X Y = (η_ M).app _)
-- (str_η' : ∀ X Y : C, ((η_ M).app X ⊗ 𝟙 Y) ≫ σ X Y = (η_ M).app _)
(str_μ : ∀ X Y : C, τ X (M.obj Y) ≫ M.map (τ X Y) ≫ (μ_ M).app _ = (𝟙 _ ⊗ (μ_ M).app _) ≫ τ _ _)
-- (str_μ' : ∀ X Y : C, σ (M.obj X) Y ≫ M.map (σ X Y) ≫ (μ_ M).app _ = ((μ_ M).app _ ⊗ 𝟙 _) ≫ σ _ _)

attribute [simp, reassoc] strong_monad.str_η  strong_monad.str_μ
                          -- strong_monad.str_η' strong_monad.str_μ'

section kleisli

variables  {X Y Z W : C}
variables  (M : C ⥤ C) [has_kleisli M] [strong_functor M]
open has_kleisli

notation `Bind` := λ {C} [𝒞 : category C] (M : C ⥤ C), @bind' C 𝒞 M _

-- def bind_σ (f : X ⊗ Y ⟶ M.obj Z) : (M.obj X ⊗ Y ⟶ M.obj Z) :=
-- σ_ _ _ _ ≫ bind' f

#check @bind' C 𝒞 M _ (X ⊗ Y) (Z ⊗ Y)
-- def bind_σ' (f : X ⟶ M.obj Z) :
--   (σ_ M X (M.obj Y) ≫ _ ≫ bind' (τ_ M X Y) ⊗ 𝟙 (M.obj Z)) = _ := _

-- #exit

def bind_τ (f : X ⊗ Y ⟶ M.obj Z) : (X ⊗ M.obj Y ⟶ M.obj Z) :=
τ_ _ _ _ ≫ bind' f

end kleisli

class strong_kleisli (M : C ⥤ C)
extends has_kleisli M, strong_functor M :=
(str_pure : Π {X Y : C}, (𝟙 X ⊗ pure Y) ≫ τ_ M _ _ = pure _) --  := by intros; show_types 1)
(str_bind : Π {X Y Z : C} (f : M.obj Y ⟶ M.obj Z),
     (𝟙 X ⊗ bind' f) ≫ τ_ M _ _ =
     τ_ M _ _ ≫ bind' ((𝟙 _ ⊗ f) ≫ τ_ M _ _))
-- (str_pure' : Π {X Y : C}, (pure X ⊗ 𝟙 Y) ≫ σ_ M _ _ = pure _) -- := by intros; show_types 1)
-- (str_bind' : Π {X Y Z : C} (f : M.obj Y ⟶ M.obj Z),
--      (bind' f ⊗ 𝟙 X) ≫ σ_ M _ _ =
--      σ_ M _ _ ≫ bind' ((f ⊗ 𝟙 _) ≫ σ_ M _ _))

attribute [simp, reassoc] strong_kleisli.str_pure strong_kleisli.str_bind
                          -- strong_kleisli.str_pure' strong_kleisli.str_bind'

-- #exit
open strong_functor strong_monad has_kleisli

attribute [simp, reassoc] str_comm -- str_comm'

-- (law1 : ∀ X Y Z : C,
--   τ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
--   (α_ X Y (F.obj Z)).hom ≫ (𝟙 _ ⊗ τ _ _) ≫ τ _ _ )
-- (law2 : ∀ X : C, τ (𝟙_ _) X ≫ F.map (λ_ _).hom = (λ_ _).hom)
-- #exit

instance (T : C ⥤ C) [strong_kleisli T] : strong_monad T :=
{ τ_unit := by { obviously, rw ← law2, simp, },
  str_comm  := by { obviously, rw law1, },
  -- str_comm' := by { obviously, rw law3, },
  str_η := by { obviously, },
  str_μ := by { obviously, },
  -- str_η' := by { obviously, },
  -- str_μ' := by { obviously, },
  .. monad.of_kleisli T
  }

-- (nat_τ : ∀ (A A' B B' : C) (f : A ⟶ A') (g : B ⟶ B'),
--        (f ⊗ F.map g) ≫ τ A' B' = τ A B ≫ F.map (f ⊗ g))
-- (nat_σ : ∀ (A A' B B' : C) (f : A ⟶ A') (g : B ⟶ B'),
--        (F.map f ⊗ g) ≫ σ A' B' = σ A B ≫ F.map (f ⊗ g))
-- (str_η : (𝟙 X ⊗ (η_ M).app Y) ≫ τ X Y = (η_ M).app _)
-- (str_μ : τ X (M.obj Y) ≫ M.map (τ X Y) ≫ (μ_ M).app _ = (𝟙 _ ⊗ (μ_ M).app _) ≫ τ _ _)

-- str_η' : ((η_ M).app X ⊗ 𝟙 Y) ≫ σ_ M X Y = (η_ M).app ((𝟭 C).obj X ⊗ Y)
-- str_μ' : σ_ M (M.obj X) Y ≫ M.map (σ_ M X Y) ≫ (μ_ M).app (X ⊗ Y) = ((μ_ M).app X ⊗ 𝟙 Y) ≫ σ_ M X Y
local attribute [simp] functor.map_comp nat_trans.naturality
local attribute [-simp] functor.map_comp_symm functor.map_comp_symm_assoc nat_trans.naturality_symm nat_trans.naturality_symm_assoc

instance (T : C ⥤ C) [I : strong_monad T] : strong_kleisli T :=
{ str_pure := by obviously,
  -- str_pure' := by obviously,
  str_bind :=  by { obviously, rw [← nat_τ_assoc,str_μ] },
  -- str_bind' := by { obviously, rw [← nat_σ_assoc,str_μ'] },
  .. I }

-- (τ_unit : ∀ A : C, τ (𝟙_ _) A = (λ_ _).hom ≫ M.map (λ_ _).inv)
-- (str_comm : ∀ X Y Z : C,
--   (α_ X Y _).hom ≫ (𝟙 _ ⊗ τ _ _) ≫ τ _ _ =
--   τ (X ⊗ Y) Z ≫ M.map (α_ X Y _).hom)
-- (str_η : ∀ X Y : C, (𝟙 X ⊗ (η_ M).app Y) ≫ τ X Y = (η_ M).app _)
-- (str_μ : ∀ X Y : C, τ X (M.obj Y) ≫ M.map (τ X Y) ≫ (μ_ M).app _ = (𝟙 _ ⊗ (μ_ M).app _) ≫ τ _ _)
-- (str_pure : Π {X Y : C}, (𝟙 X ⊗ pure Y) ≫ τ_ M _ _ = pure _)
-- (str_bind : Π {X Y Z : C} (f : M.obj Y ⟶ M.obj Z),
--      (𝟙 X ⊗ bind' f) ≫ τ_ M _ _ =
--      τ_ M _ _ ≫ bind' ((𝟙 _ ⊗ f) ≫ τ_ M _ _))
-- (str_pure' : Π {X Y : C}, (pure Y ⊗ 𝟙 X) ≫ σ_ M _ _ = pure _)
-- (str_bind' : Π {X Y Z : C} (f : M.obj Y ⟶ M.obj Z),
--      (bind' f ⊗ 𝟙 X) ≫ σ_ M _ _ =
--      σ_ M _ _ ≫ bind' ((f ⊗ 𝟙 _) ≫ σ_ M _ _))

end category_theory

namespace category_theory

variables
  [symmetric_monoidal_category C]
  [symmetric_monoidal_category D]

open has_kleisli strong_kleisli strong_functor symmetric_monoidal_category

variables (M : C ⥤ C)

def σ_  [strong_functor M] (X Y : C) : M.obj X ⊗ Y ⟶ M.obj (X ⊗ Y) :=
B_ _ _ ≫ τ_ _ _ _ ≫ M.map (B_ _ _)

def M_ [strong_monad M] (X Y : C) :
  M.obj X ⊗ M.obj Y ⟶ M.obj (X ⊗ Y) :=
σ_ _ _ _ ≫ M.map (τ_ _ _ _) ≫ (μ_ M).app (X ⊗ Y)

@[reassoc]
lemma law3 [strong_functor M] (X Y Z : C) :
  σ_ M X (Y ⊗ Z) ≫ M.map (α_ X Y Z).inv =
  (α_ (M.obj X) Y Z).inv ≫ (σ_ M _ _ ⊗ 𝟙 _) ≫ σ_ M _ _  := _

@[reassoc]
lemma law4 [strong_functor M] (X : C) : σ_ M X (𝟙_ _) ≫ M.map (ρ_ _).hom = (ρ_ _).hom := _


#check @nat_τ .
  -- ∀ {C : Type u_2} [𝒞 : category C] [_inst_1 : monoidal_category C 𝒞] (F : C ⥤ C) [c : strong_functor F]
  -- (A A' B B' : C) (f : A ⟶ A') (g : B ⟶ B'), (f ⊗ F.map g) ≫ τ_ F A' B' = τ_ F A B ≫ F.map (f ⊗ g)

-- @[simp, reassoc]
-- lemma braid_map (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') :
--   (g ⊗ f) ≫ B_ Y' X' = B_ Y X ≫ (f ⊗ g) :=
-- sorry

local attribute [-simp] functor.map_comp nat_trans.naturality
local attribute [simp] functor.map_comp_symm     functor.map_comp_symm_assoc
                       nat_trans.naturality_symm nat_trans.naturality_symm_assoc

@[reassoc]
lemma nat_σ [strong_functor M] (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y') :
  (M.map f ⊗ g) ≫ σ_ _ _ _ = σ_ _ _ _ ≫ M.map (f ⊗ g) :=
begin
  rw [σ_,σ_], simp,
end

@[simp, reassoc]
lemma str_pure' [strong_kleisli M] {X Y : C} : (pure M X ⊗ 𝟙 Y) ≫ σ_ M _ _ = pure M _ :=
by simp [σ_]

@[simp, reassoc]
lemma str_bind' [strong_kleisli M] {X Y Z : C} (f : M.obj Y ⟶ M.obj Z) :
     (bind' f ⊗ 𝟙 X) ≫ σ_ M _ _ =
     σ_ M _ _ ≫ bind' ((f ⊗ 𝟙 _) ≫ σ_ M _ _) :=
by simp [σ_]

-- #print nat_σ_assoc
class commutative_strong_monad (M : C ⥤ C) [strong_monad M] :=
-- (str_def : ∀ X Y, B_ _ _ ≫ τ M X Y = σ M _ _ ≫ M.map (B_ _ _))
(foob : ∀ X Y, τ_ M X Y = ((η_ M).app _ ⊗ 𝟙 _) ≫ M_ M _ _)

namespace commutative_strong_monad

-- def costrength

variables {M} [strong_monad M] [commutative_strong_monad M]
variables {X Y Z : C} (f : M.obj Y ⟶ M.obj Z)

-- lemma str_def' : τ M X Y = B_ _ _ ≫ σ M _ _ ≫ M.map (B_ _ _) :=
-- by rw [← str_def,braiding_inv_assoc]

#check functor.map_comp

-- attribute [reassoc] nat_trans.naturality
#check functor.map_comp
lemma str_μ : M_ M _ _ = B_ _ _ ≫ τ_ _ _ _ ≫ M.map (σ_ _ _ _) ≫ (μ_ M).app (X ⊗ Y) ≫ M.map (B_ _ _) :=
-- by rw [M_,str_def',foob,M_,← nat_σ]
begin
  rw [M_,σ_,σ_,← nat_trans.naturality],
  simp [- functor.map_comp,functor.map_comp_symm,functor.map_comp_symm_assoc],
end

end commutative_strong_monad

section strong_kleisli
variables {M} [strong_kleisli M]
variables {X Y Z : C} (f : M.obj Y ⟶ M.obj Z)

-- def M_ : M.obj X ⊗ M.obj Y ⟶ M.obj (X ⊗ Y) := σ_ _ _ _ ≫ bind' (τ_ M X Y)

-- lemma braid_τ : B_ _ _ ≫ τ M X Y = σ M _ _ ≫ M.map (B_ _ _) := sorry
-- lemma braid_σ : B_ _ _ ≫ σ M X Y = τ M _ _ ≫ M.map (B_ _ _) := sorry

-- #check B_ _ _ ≫ σ M X Y

lemma M_def : σ_ _ _ _ ≫ bind' (τ_ _ _ _) = τ_ M _ _ ≫ bind' (σ_ M X Y) :=
by rw [σ_]

end strong_kleisli

-- local attribute [-simp] functor.map_comp nat_trans.naturality
-- local attribute [simp] functor.map_comp_symm functor.map_comp_symm_assoc nat_trans.naturality_symm nat_trans.naturality_symm_assoc

-- local attribute [-simp] functor.map_comp nat_trans.naturality
-- local attribute [simp] functor.map_comp_symm functor.map_comp_symm_assoc nat_trans.naturality_symm nat_trans.naturality_symm_assoc


--  [strong_functor T]
instance (T : C ⥤ C) [strong_kleisli T] : lax_monoidal_functor T :=
{ ε := pure _ _,
  μ := λ X Y, σ_ _ _ _ ≫ bind' (τ_ _ _ _),
  μ_natural' := by intros; simp [nat_τ_assoc,nat_σ_assoc],
  associativity' := by { obviously, -- rw [category.assoc],
                                    -- ,bind_nat_c,law1,← has_kleisli.bind_nat_b,
                                    --  ← has_kleisli.bind_nat_b],
                         conv_rhs { congr, },
-- ⊢ (σ_ T X (T.obj Y) ≫ bind' (τ_ T X Y) ⊗ 𝟙 (T.obj Z)) ≫
--       σ_ T (X ⊗ Y) (T.obj Z) ≫
--         T.map ((α_ X Y (T.obj Z)).hom) ≫ T.map (𝟙 X ⊗ τ_ T Y Z) ≫ bind' (τ_ T X (Y ⊗ Z)) =
--     (α_ (T.obj X) (T.obj Y) (T.obj Z)).hom ≫
--       (𝟙 (T.obj X) ⊗ σ_ T Y (T.obj Z) ≫ bind' (τ_ T Y Z)) ≫
--         σ_ T X (T.obj (Y ⊗ Z)) ≫ bind' (τ_ T X (Y ⊗ Z))
                          },
  left_unitality'  :=
    by { intros,
         rw [category.assoc,str_pure'_assoc,bind_nat_c,has_kleisli.pure_bind,law2],
         -- simp, rw law2
 },
         -- rw assoc,
         -- rw strong_kleisli.str_pure'_assoc,
         -- rw bind_nat_c,
         -- rw has_kleisli.pure_bind,
         -- rw law2,


         -- -- rw strong_kleisli.str_pure'_assoc,
         -- -- rw assoc,
         -- -- rw has_kleisli.pure_bind,
         -- -- rw bind_nat_c,
         -- rw law2,


         -- simp only [has_kleisli.pure_bind, strong_kleisli.str_pure'_assoc, assoc, bind_nat_c], rw law2 },
  -- left_unitality'  := by { obviously, rw law2 },
  right_unitality' :=
    by { intros,
         rw [category.assoc,σ_],
         have := str_pure_assoc T,
         erw [σ_], simp,
         rw [str_pure_assoc],
         rw [bind_nat_c],
         rw [has_kleisli.pure_bind],
         rw [law4],
         -- rw [M_def,category.assoc,str_pure_assoc,bind_nat_c,has_kleisli.pure_bind,law4],
         -- simp,
         -- rw law2',
         -- rw ← str_bind',

         -- rw assoc,
         -- rw strong_kleisli.str_pure'_assoc,
         -- rw bind_nat_c,
         -- rw has_kleisli.pure_bind,
         -- rw law2,


         -- simp only [assoc],
         -- rw assoc,
         -- rw bind_nat_c,
         -- rw bind_nat_c,

         -- rw strong_kleisli.str_pure_assoc,
         -- rw assoc,
         -- rw has_kleisli.pure_bind,
         -- rw bind_nat_c,
         -- rw [law2],
         } }

-- instance (T : C ⥤ C) [monad T] [strong_monad T] : lax_monoidal_functor T :=
-- { ε := (η_ T).app _,
--   μ := λ X Y, τ_ T _ _ ≫ T.map (σ_ T _ _) ≫ (μ_ _).app _,
--   μ_natural' := by intros; simp [nat_τ_assoc,nat_σ],
--   associativity' := by intros; simp,
--   left_unitality' := by obviously,
--   right_unitality' := _}

#exit
variables (T : C ⥤ C) [monad T] [strong_functor T] (X : C)

open category_theory.monad

variables {C T}

def Kleisli.prod : Kleisli T → Kleisli T → Kleisli T :=
λ X Y : C, show C, from X ⊗ Y

def Kleisli.unit : Kleisli T :=
show C, from 𝟙_ _

set_option pp.universes true
local infix ` ⊗' `:30 := Kleisli.prod
notation `𝟙'` := Kleisli.unit

abbreviation hom' : Kleisli T → Kleisli T → Sort v₁ :=
λ X Y : C, X ⟶ Y

infix ` ⟶' `:10 := hom'

section lift
open strong_functor
variable T
def lift : Π {X Y : Kleisli T} (f : X ⟶' Y), X ⟶ Y :=
λ (X Y : C) (f : X ⟶ Y), show X ⟶ T.obj Y, from f ≫ (η_ _).app _

end lift

def left : Π {X Y Z : Kleisli T} (f : Y ⟶ Z), X ⊗' Y ⟶ X ⊗' Z :=
λ {X Y Z : C} f : Y ⟶ T.obj Z,
show X ⊗ Y ⟶ T.obj (X ⊗ Z), from
(𝟙 _ ⊗ f) ≫ τ_ T _ _

def right : Π {X Y Z : Kleisli T} (f : X ⟶ Y), X ⊗' Z ⟶ Y ⊗' Z :=
λ {X Y Z : C} f : X ⟶ T.obj Y,
show X ⊗ Z ⟶ T.obj (Y ⊗ Z), from
(f ⊗ 𝟙 _) ≫ σ_ T _ _

@[simp] lemma left_id {X Y : Kleisli T} : left (𝟙 Y) = 𝟙 (X ⊗' Y) :=
by simp [left,category_struct.id]; erw nat_τ_Y

@[simp] lemma right_id {X Y : Kleisli T} : right (𝟙 X) = 𝟙 (X ⊗' Y) := _

#check strong_functor.nat_τ_Y_assoc

@[simp] lemma left_comp {X Y Z W : Kleisli T} (f : X ⟶ Y) (g : Y ⟶ Z) :
  -- left f ≫ (left g : Kleisli.prod W Y ⟶ _) = left (f ≫ g) := _
  left (f ≫ g) = left f ≫ (left g : Kleisli.prod W Y ⟶ _) :=
begin
  simp [left,(≫)], rw [← strong_functor.nat_τ_Y_assoc],
    -- congr' 2,
  simp [-functor.map_comp,functor.map_comp_symm,functor.map_comp_symm_assoc],
end

@[simp] lemma right_comp {X Y Z W : Kleisli T} (f : X ⟶ Y) (g : Y ⟶ Z) :
  -- right f ≫ (right g : Kleisli.prod Y W ⟶ _) = right (f ≫ g) := _
  right (f ≫ g) = right f ≫ (right g : Kleisli.prod Y W ⟶ _) := _

@[simp, reassoc] lemma left_right_swap {X Y Z W : Kleisli T} (f : X ⟶ Y) (g : Z ⟶ W) :
  left f ≫ right g = right g ≫ left f := _

@[simp] lemma lift_id {X : Kleisli T} : lift T (𝟙 _ : X ⟶' X) = 𝟙 X :=
by simp [lift]; refl

@[simp, reassoc] lemma lift_comp {X Y Z : Kleisli T} (f : X ⟶' Y) (g : Y ⟶' Z) :
  lift T f ≫ lift T g = lift T (f ≫ g) :=
by simp [lift,(≫)]; rw ← nat_trans.naturality; refl

@[simp, reassoc] lemma lift_assoc_right {X Y Z W : C} (f : X ⟶ T.obj W) :
  lift T ((α_ X Y Z).hom) ≫ right f = right (right f) ≫ lift T ((α_ W Y Z).hom) := _

@[simp, reassoc] lemma lift_assoc_left_right {X Y Z W : C} (f : Y ⟶ T.obj W) :
  lift T ((α_ X Y Z).hom) ≫ left (right f) = right (left f) ≫ lift T ((α_ X W Z).hom) := _

@[simp, reassoc] lemma lift_assoc_left_left {X Y Z W : C} (f : Z ⟶ T.obj W) :
  lift T ((α_ X Y Z).hom) ≫ left (left f) = left f ≫ lift T ((α_ X Y W).hom) := _

-- @[simp] lemma right_eta {X Y : C} :
--   right ((η_ T).app X) = (η_ T).app (X ⊗' Y) := _

-- @[simp] lemma left_eta {X Y : C} :
--   left ((η_ T).app Y) = (η_ T).app (X ⊗' Y) := _

@[simp] lemma left_lift {X Y Z : C} (f : Y ⟶ Z) :
  left (lift T f) = lift T (𝟙 X ⊗ f) := _

@[simp] lemma right_lift {X Y Z : C} (f : X ⟶ Y) :
  right (lift T f) = lift T (f ⊗ 𝟙 Z) := _

@[simp] def right_unitor : Π (X : Kleisli T), X ⊗' 𝟙' ≅ X :=
λ X : C,
{ hom := lift T (monoidal_category.right_unitor X).hom,
  inv := lift T (monoidal_category.right_unitor X).inv }

@[simp] def left_unitor (X : Kleisli T) : 𝟙' ⊗' X ≅ X :=
{ hom := lift T (monoidal_category.left_unitor X).hom,
  inv := lift T (monoidal_category.left_unitor X).inv }

@[simp] def associator (X Y Z : Kleisli T) : (X ⊗' Y) ⊗' Z ≅ X ⊗' (Y ⊗' Z) :=
{ hom := lift T (monoidal_category.associator X Y Z).hom,
  inv := lift T (monoidal_category.associator X Y Z).inv }

@[simp, reassoc] lemma lift_left_id_comp {X Y : C} (f : X ⟶ T.obj Y) :
  lift T ((λ_ X).hom) ≫ f = left f ≫ lift T ((λ_ Y).hom) := _
#check σ_ T
@[simp, reassoc] lemma lift_right_id_comp {X Y : C} (f : X ⟶ T.obj Y) :
  lift T ((ρ_ X).hom) ≫ f = right f ≫ lift T ((ρ_ Y).hom) :=
by simp [right]

local attribute [-simp] nat_trans.naturality nat_trans.naturality_assoc
local attribute [simp] nat_trans.naturality_symm nat_trans.naturality_symm_assoc

instance : monoidal_category (Kleisli T) :=
{ tensor_obj := λ X Y : C, @monoidal_category.tensor_obj C _ _ X Y,
  tensor_hom := λ (X₁ Y₁ X₂ Y₂ : C) f g, right f ≫ left g,
  tensor_unit := @monoidal_category.tensor_unit C _ _,
  right_unitor := right_unitor,
  left_unitor := left_unitor,
  associator := associator,
  left_unitor_naturality' := by intros; simp; erw category.id_comp,
  triangle' := by intros; simp; erw category.id_comp; simp,
  pentagon' := by intros; simp; erw category.id_comp; simp [monoidal_category.pentagon] }

end category_theory
