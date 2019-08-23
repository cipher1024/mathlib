
import category_theory.monad.basic
import category_theory.types
import category.functor
import category.monad.basic

namespace category_theory
open category

universes v₁ v₂ u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C] (T : C ⥤ C)
include 𝒞

class has_kleisli :=
(pure : Π X : C, X ⟶ T.obj X)
-- (bind : Π {X Y Z : C}, (X ⟶ T.obj Y) → (Y ⟶ T.obj Z) → (X ⟶ T.obj Z))
(bind' : Π {X Y : C}, (X ⟶ T.obj Y) → (T.obj X ⟶ T.obj Y))
(pure_bind : Π {X Y : C} (f : X ⟶ T.obj Y), pure X ≫ bind' f = f  . obviously)
(bind_pure : Π {X : C}, bind' (pure X) = 𝟙 _ . obviously)
(bind_assoc : Π {X Y Z : C} (g : X ⟶ T.obj Y) (h : Y ⟶ T.obj Z),
  bind' g ≫ bind' h = bind' (g ≫ bind' h) . obviously )
(pure_nat : Π {X Y : C} (f : X ⟶ Y), f ≫ pure Y = pure X ≫ T.map f . obviously)
-- (bind_nat_a : Π {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ T.obj Z) (h : Z ⟶ T.obj W),
--   f ≫ bind g h = bind (f ≫ g) h . obviously)
  -- f ≫ g ≫ bind' h = (f ≫ g) ≫ bind' h
(bind_nat_b : Π {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ T.obj Z),
  T.map f ≫ bind' g = bind' (f ≫ g) . obviously)
(bind_nat_c : Π {Y Z W : C} (g : Y ⟶ T.obj Z) (h : Z ⟶ W),
  bind' g ≫ T.map h = bind' (g ≫ T.map h) . obviously)

open has_kleisli

local attribute [-simp] nat_trans.naturality
local attribute [simp] nat_trans.naturality_symm nat_trans.naturality_symm_assoc monad.assoc
attribute [simp, reassoc] pure_nat bind_nat_b bind_nat_c
attribute [simp] has_kleisli.pure_bind has_kleisli.bind_pure has_kleisli.bind_assoc
  -- bind_nat_b

namespace kleisli

-- variables [has_kleisli.{v₁} T]
-- variables ⦃X Y Z : C⦄ (f : X ⟶ Y) (g : Y ⟶ Z)

-- protected def map : T.obj X ⟶ T.obj Y :=
-- bind'.{v₁} (f ≫ pure _ _)

-- @[simp, reassoc]
-- def map_comp : kleisli.map T f ≫ kleisli.map T g = kleisli.map T (f ≫ g) :=
-- by simp [kleisli.map]

-- @[simp]
-- def map_id : kleisli.map T (𝟙 X) = 𝟙 (T X) :=
-- by simp [kleisli.map]

-- def to_functor : C ⥤ C :=
-- { obj := T,
--   map := kleisli.map T }

-- @[simp]
-- lemma to_functor_map {X Y : C} (f : X ⟶ Y) : (to_functor T).map f = @kleisli.map.{v₁} _ _ T _ _ _ f := rfl

-- @[simp]
-- lemma to_functor_obj : (to_functor T).obj = T := rfl

-- @[simp, reassoc]
-- lemma pure_nat {X Y : C} (f : X ⟶ Y) : pure T X ≫ kleisli.map T f = f ≫ pure T Y :=
-- by simp [kleisli.map]

-- @[simp]
-- lemma bind_nat_b {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ T Z) :
--   kleisli.map T f ≫ bind' g = bind' (f ≫ g) :=
-- -- by simp only [kleisli.map, category_theory.has_kleisli.pure_bind, category_theory.has_kleisli.bind_assoc, category.assoc]
-- by simp [kleisli.map]

-- @[simp, reassoc]
-- lemma bind_nat_c {Y Z W : C} (g : Y ⟶ T Z) (h : Z ⟶ W) :
--   bind' g ≫ kleisli.map T h = bind' (g ≫ kleisli.map T h) :=
-- by simp [kleisli.map]

end kleisli


-- def bind'' : Π {X Y Z : C}, (X ⟶ T.obj Y) → (Y ⟶ T.obj Z) → (X ⟶ T.obj Z)

-- @[simp] lemma bind_nat_b' [has_kleisli T] {W X Y Z : C} (h : W ⟶ T.obj X) (f : X ⟶ Y) (g : Y ⟶ T.obj Z) :
--   bind (h ≫ T.map f) g = bind h (f ≫ g) :=
-- by rw [← bind_nat_a,bind_nat_b,bind_nat_a,comp_id]

instance {T : C ⥤ C} [monad T] : has_kleisli.{v₁} T :=
{ pure := λ X, (η_ _).app X,
  bind' := λ Y Z g, T.map g ≫ (μ_ T).app _ }

open has_kleisli

def monad.of_kleisli [K : has_kleisli.{v₁} T] : monad T :=
{ η := { app := @has_kleisli.pure _ _ T K },
  μ := { app := λ X, @bind' _ _ T K _ _ (𝟙 _) } }

local attribute [simp] functor.map_comp_symm functor.map_comp_symm_assoc map_map

@[simp] lemma monad.of_kleisli_η_app [has_kleisli T] (X : C) : (@monad.η _ _ T (monad.of_kleisli T)).app X = @has_kleisli.pure _ _ T _ X := rfl
@[simp] lemma monad.of_kleisli_μ_app [has_kleisli T] (X : C) : (@monad.μ _ _ T (monad.of_kleisli T)).app X = @has_kleisli.bind' _ _ T _ _ _ (𝟙 _) := rfl

@[simp] lemma kleisli.of_monad_pure [monad T] (X : C) :
  has_kleisli.pure T X = (monad.η T).app _ := rfl

@[simp] lemma kleisli.of_monad_bind [monad T] (X Y : C) (f : X ⟶ T.obj Y) :
  has_kleisli.bind' f = T.map f ≫ (monad.μ T).app _ := rfl

section types

omit 𝒞

section functor
variables  (m : Type.{u₁} → Type.{u₁}) [F : _root_.functor m] [LF : is_lawful_functor m]
include F LF

def functor.of_types : Type.{u₁} ⥤ Type.{u₁} :=
{ obj := m,
  map := @_root_.functor.map m _ }

@[simp]
lemma map_of_types {α β} (f : α → β) : (functor.of_types m).map f = @_root_.functor.map m _ _ _ f := rfl

-- lemma map_of_types_eq [has_kleisli.{u₁+1} m] {X Y : Type u₁} (f : X ⟶ Y) : kleisli.map m f = (<$>) f :=
-- begin
--   ext, dsimp [kleisli.map],
-- end


-- set_option pp.universes true

-- #print category_theory.types
omit F LF
instance functor.of_types.monad {m} [I : _root_.monad m] [is_lawful_functor m] : _root_.monad (functor.of_types m).obj := I
instance functor.of_types.is_lawful_monad {m} [_root_.monad m] [I : is_lawful_monad m] : is_lawful_monad (functor.of_types m).obj := I

#check map_eq_bind_pure_comp

instance is_lawful_monad.to_kleisli {m} [_root_.monad m] [is_lawful_monad m] : has_kleisli.{u₁+1 u₁+1} (functor.of_types m) :=
{ pure := λ X x, pure x,
  bind' := λ X Y (f : X → m Y) (a : m X), (a >>= f : m Y),
  pure_bind := by simp [(≫),(∘)],
  bind_pure := by intros; ext; simp,
  bind_assoc := by intros; ext; simp [(∘),is_lawful_monad.bind_assoc],
  pure_nat := by { obviously },
  bind_nat_b := by { intros, ext, simp with monad_norm, },
  bind_nat_c := by { intros, ext, simp with monad_norm, congr, ext, simp [map_eq_bind_pure_comp], },
  }

-- lemma of_types_eq_of_kleisli [has_kleisli.{u₁+1} m] : functor.of_types m = kleisli.to_functor m :=
-- _

-- variables [has_kleisli.{u₁+1 u₂+1} m]

#check m
#check @has_kleisli
-- #exit

-- instance functor.of_types.functor : _root_.functor (functor.of_types m).obj := F
-- instance : is_lawful_functor (functor.of_types m).obj := LF

-- @[simp] lemma map_of_types {α β} (f : α ⟶ β) : (functor.of_types m).map f = _root_.functor.map f := rfl

end functor

section monad

variables  (m : Type.{u₁} → Type.{u₁}) [M : _root_.monad m] [LM : is_lawful_monad m]
include M LM

-- instance functor.of_types.monad : _root_.monad (functor.of_types m).obj := M
-- instance : is_lawful_monad (functor.of_types m).obj := LM

end monad

local attribute [simp] fish is_lawful_monad.bind_assoc map_bind seq_bind_eq

set_option pp.universes true

def types.kleisli (m : Type* → Type*) [_root_.monad m] [is_lawful_monad m] : has_kleisli.{u₁+1 u₁+1} (functor.of_types m) :=
{ pure := λ X x, has_pure.pure x,
  bind' := λ X Y (f : X → m Y), id >=> f }

local attribute [instance] types.kleisli

instance types.monad (m : Type* → Type*) [_root_.monad m] [is_lawful_monad m] : monad (functor.of_types m) :=
monad.of_kleisli _

end types

variables [has_kleisli.{v₁} T] (X : C)

namespace monad
include T
def Kleisli := C

instance : category (Kleisli T) :=
{ hom := λ X Y : C, X ⟶ T.obj Y,
  id := λ X : C, pure T X,
  comp := λ (X Y Z : C) (f : X ⟶ T.obj Y) (g : Y ⟶ T.obj Z), f ≫ bind' g,
 }

end monad

variables {C} {D : Type u₂} [𝒟 : category.{v₂} D]

-- def pure' (m : Type → Type) [has_pure m] (α : Type) : α ⟶ m α := pure
-- def join' (m : Type → Type) [_root_.monad m] (α : Type) : m (m α) ⟶ m α := mjoin
-- def fmap  (m : Type → Type) [_root_.functor m] {α β : Type} (f : α ⟶ β) : m α ⟶ m β := _root_.functor.map f

-- @[simp, reassoc]
-- def fmap_comp (m : Type → Type) [_root_.functor m] [is_lawful_functor m] {α β γ : Type} (f : α ⟶ β) (g : β ⟶ γ) :
--   fmap C m f ≫ fmap C m g = fmap C m (f ≫ g) := funext $ map_map _ _

section functor

open functor
include 𝒟

class reified_functor (forget : C ⥤ D) (N : D ⥤ D) :=
(M : C ⥤ C)
(types : M ⋙ forget ≅ forget ⋙ N)
-- (map_eq : ∀ (α β : C) (f : α ⟶ β),
--   N.map (forget.map f) ≫ (nat_trans.app types.inv β : (forget ⋙ N).obj β ⟶ _) =
--   (nat_trans.app types.inv α : (forget ⋙ N).obj α ⟶ _) ≫ forget.map (M.map f))

open reified_functor

lemma map_eq (F : C ⥤ D) (N : D ⥤ D) [reified_functor F N] (α β : C) (f : α ⟶ β) :
  N.map (F.map f) ≫ (nat_trans.app (types F N).inv β : (F ⋙ N).obj β ⟶ _) =
  (nat_trans.app (types F N).inv α : (F ⋙ N).obj α ⟶ _) ≫ F.map ((M F N).map f) :=
(types _ N).inv.naturality _

-- variables {m : Type → Type} [_root_.functor m] [R : reified_functor.{v₁} C m]
-- include R
open reified_functor

-- lemma forget_id {α : C} : (forget.{v₁} C m).map (𝟙 α) = id :=
-- funext $ λ x, rfl

attribute [reassoc] map_eq

-- lemma map_id {α : C} (x : m ((forget.{v₁} C m).obj α)) : map id x = x :=
-- suffices fmap C m ((forget.{v₁} C m).map (𝟙 α)) = id,
--   by simp [fmap,*] at this; rw this; refl,
-- by rw [← cancel_mono (types.{v₁} m α).inv,map_eq]; simp

-- lemma map_map {α β γ : C} (f : α ⟶ β) (g : β ⟶ γ) (x : m ((forget.{v₁} C m).obj α)) :
--   map ((forget.{v₁} C m).map (f ≫ g)) x = map ((forget.{v₁} C m).map g) (map ((forget.{v₁} C m).map f) x) :=
-- suffices fmap C m ((forget.{v₁} C m).map (f ≫ g)) = fmap C m ((forget.{v₁} C m).map f) ≫ fmap C m ((forget.{v₁} C m).map g),
--   from congr_fun this _,
-- by rw [← cancel_mono (types.{v₁} m γ).inv]; simp [map_eq m,reified_functor.map_eq_assoc m,-types_comp,-functor.map_comp]; simp only [functor.map_comp]

-- variables (m)

section down
omit 𝒟
variables  {F : C ⥤ Type u₂} {N : Type u₂ → Type u₂}
  [_root_.functor N] [is_lawful_functor N]
  [reified_functor F (functor.of_types N)]

def down {α β : C} (f : α ⟶ (M.{v₁} F (functor.of_types N)).obj β) : F.obj α ⟶ N (F.obj β) :=
F.map f ≫ (types F (functor.of_types N)).hom.app _

end down

end functor

lemma bind_eq_μ (M : C ⥤ C) [monad M] {X Y : C} (f : X ⟶ M.obj Y) :
  bind' f = M.map f ≫ (μ_ M).app Y := rfl

lemma μ_eq_bind (M : C ⥤ C) [monad M] {X : C} :
  (μ_ M).app X = bind' (𝟙 _) :=
by simp [has_kleisli.bind']

open category_theory.monad (Kleisli)

include 𝒟

-- instance  (forget : C ⥤ D) (N : D ⥤ D) [has_kleisli.{v₂} N] [reified_functor forget N] :
--   has_kleisli (reified_functor.M forget N) :=
-- -- { pure := _,
-- --   bind' := _ }
-- { pure := _,
--   bind' := _,
--   pure_bind := _,
--   bind_pure := _,
--   bind_assoc := _,
--   pure_nat := _,
--   bind_nat_b := _,
--   bind_nat_c := _ }

-- set_option pp.universes true
class reified_monad (F : C ⥤ D) (N : D ⥤ D) [has_kleisli.{v₂} N]
extends reified_functor F N :=
[kleisli : monad M]
-- (forget : C ⥤ Type)
-- (M : C ⥤ C)
-- (types : ∀ (α : C), forget.obj (M.obj α) ≅ m (forget.obj α))
-- (types_obj : ∀ (α : C), types (M.obj α) ≪≫ _ = _ ≪≫ fmap_iso C m (types α))
-- (fmap_types : ∀ (β : C), fmap C m (types β).inv = fmap C m (types β).inv ≫ (types (M.obj β)).inv ≫ _)
(pure_eq : ∀ (α : C), (pure N (F.obj α)) ≫ types.inv.app α = F.map (has_kleisli.pure M α))
(bind_eq : ∀ {α β : C} (f : α ⟶ M.obj β),
  F.map (bind' f) ≫ types.hom.app _ =
  types.hom.app _ ≫ bind' (F.map f ≫ types.hom.app _))
-- (join_eq : ∀ (α : C),
--   join' C m (forget.obj α) ≫ (types α).inv =
--   fmap C m (types _).inv ≫ (types _).inv ≫ forget.map ((μ_ _).app _))
-- (bind_eq : ∀ {X Y Z : monad.Kleisli T} (f : X ⟶ Y) (g : Y ⟶ Z), down C m _ = forget.map (f ≫ g))
-- (bind_eq_mjoin {α β : Type} (x : m α) (f : α → m β) : x >>= f = mjoin (f <$> x))

-- set_option pp.universes true
attribute [instance] reified_monad.kleisli
open reified_monad reified_functor has_kleisli

section foo

variables (F : C ⥤ D) (N : D ⥤ D) [monad N] [reified_monad F N]
-- #print is_lawful_monad

attribute [reassoc] pure_eq
-- attribute [instance] cat_monad

lemma μ_eq (X : C) :
  F.map ((μ_ (M F N)).app X) ≫ (types F N).hom.app _ = (types F N).hom.app _ ≫ N.map ((types F N).hom.app _) ≫ (μ_ N).app (F.obj X) :=
by simp [μ_eq_bind,bind_eq]; erw comp_id; simp [bind_nat_b]

open reified_monad reified_functor

end foo

-- section bar

-- variables
--   (F : C ⥤ Type u₂) {m : Type u₂ → Type u₂}
--   [_root_.monad m] [is_lawful_functor m] [reified_functor F (functor.of_types m)]

-- lemma bind_eq_mjoin {α β : Type*} (x : m α) (f : α → m β) : x >>= f = mjoin (f <$> x) :=
-- -- sorry
-- by rw [mjoin,← bind_pure_comp_eq_map]

-- -- variables X : C
-- -- #check bind_eq_mjoin
-- -- #check @monad.left_unit C 𝒞 (M C m) _ X
-- -- #check @monad.right_unit C 𝒞 (M C m) _ X
-- -- #check @monad.assoc C 𝒞 (M C m) _ X
-- -- #check nat_trans.naturality (μ_ T)
-- -- #check nat_trans.naturality (η_ T)
-- #check @down

-- section bind''

-- omit 𝒞 𝒟

-- def bind'' {α β : Type*} (f : α ⟶ m β) : m α ⟶ m β :=
-- λ x : m α, x >>= f
-- #check @bind''

-- end bind''

-- lemma pure_bind
--   {α β : C} (x : F.obj α) (f : α ⟶ (M.{v₁} F $ functor.of_types m).obj β) :
--   has_pure.pure x >>= down f = down f x :=
-- begin
--   suffices : ((has_pure.pure : F.obj α ⟶ m (F.obj α)) ≫ bind'' (down f) : F.obj α ⟶ m (F.obj β)) = (down f : F.obj α ⟶ m (F.obj β)),
--   { admit },
--   rw down,
--   rw map_eq,
--   rw bind_eq_mjoin.{v₁ u₁} (pure x) (down f),
--   rw mjoin,
--   change (pure' C m _ ≫ fmap C m (down C f) ≫ join' C m _ ) x = _, apply congr_fun,
--   rw [← cancel_mono (types.{v₁} m β).inv],
--   simp [-types_comp,-types_id,join_eq,down,map_eq_assoc,pure_eq_assoc],
--   rw [← functor.map_comp,← functor.map_comp],
--   rw [← nat_trans.naturality_assoc (η_ (M.{v₁} C m))],
--   simp [-types_comp,monad.left_unit,-functor.map_comp], erw category.comp_id,
-- end

-- lemma bind_pure {α : C} (x : m $ (forget.{v₁} C m).obj α) : x >>= pure = x :=
-- begin
--   rw bind_eq_mjoin.{v₁ u₁} C x,
--   change (fmap C m (pure' C m _) ≫ join' C m _) x = id _, apply congr_fun,
--   dsimp only,
--   rw [← cancel_mono (types.{v₁} m α).inv],
--   simp [-types_comp,join_eq,pure_eq,map_eq_assoc],
--   rw [← functor.map_comp,monad.right_unit (M.{v₁} C m)],
--   simp,
-- end

-- lemma bind_assoc {α β γ : Type} (x : m α)
-- (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= λ (x : α), f x >>= g :=
-- begin
--   simp [bind_eq_mjoin.{v₁ u₁} C x,bind_eq_mjoin.{v₁ u₁} C (mjoin (f <$> x))
--        ,bind_eq_mjoin.{v₁ u₁} C (f _)],
--   change (_ ≫ join' C m _) x = _
-- end

-- end bar

end category_theory
