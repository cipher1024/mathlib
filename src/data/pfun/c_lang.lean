
import data.finmap
import data.pfun.fix
import data.pfun.tactic
import category.monad.state
import tactic.norm_num

namespace c

namespace syntax

variables (S : Type)

inductive bin_oper
| plus


inductive un_oper
| minus

inductive type
| int | char | ptr (t : option type)

/--

-/
inductive expr : Type
| var {} : ℕ → expr
| bin_arith : bin_oper → expr → expr → expr
| un_arith : un_oper → expr → expr
| addr_of {} : ℕ → expr
| deref : expr → expr
| lit : unsigned → expr

inductive lhs
| var (v : ℕ) | deref (e : expr)

inductive stmt : Type
| decl {} : type → stmt
| fun_call : S → list expr → stmt
| assgn {} : lhs → expr → stmt
| while : expr → list stmt → stmt
| ite : expr → list stmt → list stmt → stmt

structure proc :=
(params : list type)
(body : list $ stmt S)

end syntax

namespace semantics

variables {S : Type}

inductive value
| int (u : unsigned)
| char (c : char)
| ptr (p : ℕ)
| none

@[reducible]
def runtime (α : Type) := (state_t (stream value) roption) α

instance {α} : has_coe (option α) (runtime α) :=
⟨ λ x, monad_lift $ roption.of_option x ⟩

@[simp]
lemma coe_some {α} (x : α) : (some x : runtime α) = pure x :=
by { unfold_coes, simp [monad_lift,has_monad_lift.monad_lift,state_t.lift,roption.of_option], refl }

def get_int : value → runtime unsigned
| (value.int u) := pure u
| _ := none

def get_ptr : value → runtime ℕ
| (value.ptr p) := pure p
| _ := none

def eval_un_arith : syntax.un_oper → unsigned → unsigned
| syntax.un_oper.minus := id

def eval_bin_arith : syntax.bin_oper → unsigned → unsigned → unsigned
| syntax.bin_oper.plus := (+)

open syntax c.syntax.expr roption

def deref_ptr (p : ℕ) : runtime value :=
do m ← get, pure $ m p

def get_var (l : list ℕ) (v : ℕ) : runtime value :=
do p ← l.nth v, m ← get, pure $ m p

def eval_expr (l : list ℕ) : c.syntax.expr → runtime value
| (var v) := get_var l v
| (lit n) := pure $ value.int n
| (bin_arith op e₀ e₁) :=
  do v₀ ← eval_expr e₀ >>= get_int,
     v₁ ← eval_expr e₁ >>= get_int,
     pure $ value.int $ eval_bin_arith op v₀ v₁
| (un_arith op e) :=
  do v ← eval_expr e >>= get_int,
     pure $ value.int $ eval_un_arith op v
| (addr_of v) := value.ptr <$> l.nth v
| (deref e) :=
  eval_expr e >>= get_ptr >>= deref_ptr

open c.syntax.stmt

def assign (p : ℕ) (v : value) : runtime unit :=
do m ← get,
   put $ λ i, if i = p then v else m i

def eval_lhs (ls : list ℕ) : lhs → runtime ℕ
| (lhs.var v) := ls.nth v
| (lhs.deref e) := eval_expr ls e >>= get_ptr

open complete_partial_order

section iter

variables {α : Type*} {β : Type}
   (f : (α → runtime β) → α → runtime β)
   (y : α → stream value → roption (β × stream value))

def runtime.iter : α → stream value → roption (β × stream value) :=
state_t.run ∘ f (state_t.mk ∘ y)

lemma mk_iter (a : α) : state_t.mk (runtime.iter f y a) = f (state_t.mk ∘ y) a :=
state_t.ext $ λ st, rfl

def monotone_left_comp {α β γ : Type*} [preorder β] [preorder γ] {f : β → γ} (hf : monotone f) :
  monotone (@function.comp α β γ f) :=
λ a b (h : ∀ x, a x ≤ b x) x, hf (h x)

lemma mk_comp_Sup (c : chain (α → stream value → roption (β × stream value))) :
  state_t.mk ∘ Sup c = Sup (c.map _ (monotone_left_comp (state_t.monotone_mk _ _ _))) :=
funext $ λ x, by simp only [Sup,chain.map_comp]

lemma monotone_iter (hf : monotone f) : monotone (runtime.iter f) :=
λ a b (h : ∀ x y, a x y ≤ b x y) x y,
by { apply hf, intros i, apply state_t.monotone_mk _ _ _ (h i) }

lemma continuous_iter (hf : continuous' f) : continuous' (runtime.iter f) :=
begin
  cases hf with h_mono h_cont,
  existsi monotone_iter f h_mono,
  intro c, simp [runtime.iter,mk_comp_Sup,h_cont _], refl,
end

end iter

instance {α β : Type*} : has_fix (α → runtime β) :=
{ fix := λ f x, ⟨has_fix.fix (runtime.iter f) x⟩ }

noncomputable instance {β} : complete_partial_order (runtime β) :=
state_t.complete_partial_order

noncomputable instance {α β : Type*} : lawful_fix (α → runtime β) :=
{ fix_eq := by { introv h, dsimp, ext,
                 conv { to_lhs, rw [lawful_fix.fix_eq (continuous_iter f h),mk_iter] } } }

open has_fix

-- def mk_call_stack : ℕ → runtime (list ℕ)

#check @cont_bind'

@[continuity]
lemma continuous_bind {α : Type*} [complete_partial_order α] {β γ : Type*} (f : α → runtime β)
  (g : α → β → runtime γ) : continuous' f → continuous' g → continuous' (λ (x : α), f x >>= g x) :=
sorry

@[continuity]
lemma continuous_and_then {α : Type*} [complete_partial_order α] {β γ : Type*} (f : α → runtime β)
  (g : α → runtime γ) : continuous' f → continuous' g → continuous' (λ (x : α), f x >> g x) :=
sorry


@[partial 4]
def eval_stmt.intl (procs : S → proc S) (eval_stmt' : list (stmt S) → ℕ → list ℕ → runtime unit) : list (stmt S) → ℕ → list ℕ → runtime unit
| [] _ _ := pure ()
| (decl t :: ss) p st :=
  do assign p value.none,
     eval_stmt' ss (p+1) (p :: st)
| (assgn v e :: ss) p st :=
  do dest ← eval_lhs st v,
     val ← eval_expr st e,
     assign dest val,
     eval_stmt' ss p st
| (ite c ls rs :: ss) p st :=
  do n ← eval_expr st c >>= get_int,
     if n ≠ 0 then eval_stmt' ls p st >> eval_stmt' ss p st
              else eval_stmt' rs p st >> eval_stmt' ss p st
| (while c body :: ss) p st :=
  -- fix (λ (repeat : ℕ → list ℕ → runtime unit) p st,
    do n ← eval_expr st c >>= get_int,
       if n ≠ 0 then eval_stmt' body p st >> eval_stmt' (while c body :: ss) p st
                else eval_stmt' ss p st
| (fun_call fn args :: ss) p st :=
  do vs ← args.mmap (eval_expr st),
     vs.enum.mmap' $ λ ⟨i,v⟩, assign (p+i) v,
     let p_fn := procs fn,
     let st' := (list.iota p_fn.params.length).map (λ x, x+p - 1),
     eval_stmt' p_fn.body (p+st'.length) st',
     eval_stmt' ss p st

def run  (procs : S → proc S) (prog : list $ stmt S) : runtime unit :=
eval_stmt procs prog 0 []

-- @[functor_norm]
lemma bind_pure_unit {m} [monad m] [is_lawful_monad m] (x : m punit) : (x >>= λ _, pure punit.star) = x :=
suffices (x >>= λ _, pure punit.star) = x >>= pure, by simpa,
congr_arg _ $ funext $ λ ⟨⟩, rfl

-- class overwrites {α} (n : ℕ) (x : unit → runtime α) :=
-- (dismiss : ∀ v : value, (assign n v >>= x) = x ())

-- instance {α} (p : ℕ) (v : value) (f : unit → runtime α) : overwrites p (λ _, assign p v >>= f) := _

-- instance {α} (p p' : ℕ) (v : value) (f : unit → runtime α) [overwrites p f] : overwrites p (λ _, assign p' v >>= f) := _

-- @[simp]
@[simp]
lemma get_var_succ (h : ℕ) (v : ℕ) (l : list ℕ) : get_var (h :: l) (v.succ) = get_var l v := rfl

@[simp]
lemma get_var_zero (h : ℕ) (l : list ℕ) : get_var (h :: l) 0 = deref_ptr h :=
by simp [get_var,deref_ptr]

@[reducible]
def asgn := finmap $ λ _ : ℕ, value

def rewrite (ls : asgn) : runtime unit :=
do m ← get,
   put $ λ i, (ls.lookup i).get_or_else (m i)

lemma ext {α} (x y : runtime α) (h : (rewrite ∅ >>= λ _, x) = (rewrite ∅ >>= λ _, y)) : x = y := _

lemma rewrite_assign' (m : asgn) (p : ℕ) (v : value) :
  (rewrite m >>= λ _, assign p v) = rewrite (m.insert p v) :=
by { simp [rewrite,assign] with monad_norm; congr; ext,
     rw [← is_lawful_monad.bind_assoc,state_t.put_get,is_lawful_monad.bind_assoc,pure_bind,state_t.put_put],
     congr, ext, split_ifs, { subst h, rw finmap.lookup_insert, refl },
     { congr' 1, rw finmap.lookup_insert_of_ne _ h } }

lemma rewrite_assign {α} (f : unit → runtime α) (m : asgn) (p : ℕ) (v : value) :
  (rewrite m >>= λ _, assign p v >>= f) = rewrite (m.insert p v) >>= f :=
by rw [← is_lawful_monad.bind_assoc,rewrite_assign']

-- lemma assign_dismiss {α} (p : ℕ) (v v' : value) (f : unit → runtime α) :
--   (assign p v >>= λ _, assign p v' >>= f) = (assign p v' >>= f) := _

-- lemma assign_swap {α} (p p' : ℕ) (v v' : value) (f : unit → runtime α) :
--   (assign p v >>= λ _, assign p' v' >>= f) = (assign p' v' >>= λ _, assign p v >>= f) :=
-- ext _ _ $ by simp [rewrite_assign,rewrite_assign']

@[simp]
lemma get_ptr_ptr (p : ℕ) : get_ptr (value.ptr p) = pure p := rfl

section present

variables {α : Type*} [decidable_eq α] {β : α → Type*} (x y : α) (v : β y) (m : finmap β)

def present := { y // m.lookup x = some y }

def present_insert_of_ne (h' : x ≠ y) : present x m → present x (m.insert y v)
| ⟨v',hv'⟩ := ⟨v',by rw [finmap.lookup_insert_of_ne _ h',hv']⟩

def present_insert : present y (m.insert y v) :=
⟨ v, finmap.lookup_insert _ ⟩

open tactic

meta def check_present' : tactic unit :=
do `(present %%k (finmap.insert %%k' %%v %%m)) ← target,
   if k =ₐ k' then
     applyc ``present_insert
   else applyc ``present_insert_of_ne; [() <$ interactive.norm_num [] (interactive.loc.ns [none]), check_present']

meta def check_present : tactic unit :=
do t ← target,
   (_,pr) ← solve_aux t check_present',
   pr' ← whnf pr,
   exact pr'

meta def mk_insert' (k x : _root_.expr) : tactic _root_.expr :=
do v ← mk_local_def `v `(nat),
   let t := @_root_.expr.lam tt `_ binder_info.default `(nat) `(value),
   -- trace t,
   f ← mk_mapp ``finmap.insert [`(nat),t,none,k],
   pure $ f x

meta def mk_insert (k x s : _root_.expr) : tactic _root_.expr :=
do f ← mk_insert' k x,
   pure $ f s

meta def mk_assumption (e : pexpr) (tac : tactic unit) : tactic _root_.expr :=
do t ← to_expr e,
   (_,pr) ← solve_aux t assumption <|> do
       { h ← assert `h t,
         solve1 tac,
         pure ((),h) },
   pure pr

#check @finmap.insert

meta def insert_finmap (k x : _root_.expr) : _root_.expr → tactic (_root_.expr × _root_.expr)
| s₀@`(finmap.insert %%k' %%x' %%s) :=
  do let t := @_root_.expr.lam tt `_ binder_info.default `(nat) `(value),
     match cmp k k' with
     | ordering.lt :=
       do -- s' ← to_expr ``(finmap.insert %%k %%x %%s₀),
          s' ← mk_insert k x s₀,
          p' ← mk_eq_refl s',
          pure (s', p')
     | ordering.eq :=
       do pr ← mk_mapp ``finmap.insert_insert [`(nat),t,none,k,x',x,s],
          s' ← mk_insert k x s,
          -- s' ← to_expr ``(finmap.insert %%k %%x %%s),
          pure (s',pr)
     | ordering.gt :=
       do (s',pr₁) ← insert_finmap s,
          f'' ← mk_insert' k' x',
          h ← mk_assumption ``(%%k' ≠ %%k) $ interactive.norm_num [] (interactive.loc.ns [none]),
          -- pr₀ ← mk_mapp ``finmap.insert_insert_of_ne [`(nat),t,none,k',k,x',x,s,h],
          -- infer_type h >>= trace, trace s,
          pr₀ ← to_expr ``(@finmap.insert_insert_of_ne nat %%t _ %%k' %%k %%x' %%x %%s %%h),
          pr₂ ← mk_congr_arg f'' pr₁,
          pr' ← mk_eq_trans pr₀ pr₂,
          pure (f'' s',pr')
     end
| s@`(∅ : asgn) :=
        do -- trace "insert",
           s' ← mk_insert k x s,
           -- s' ← to_expr ``(finmap.insert %%k %%x %%s),
           -- trace "insert (after)",
           pr ← mk_eq_refl s', pure (s',pr)
| e := fail format!"can't insert {k}, {x} into {e}"

meta def sort_finmap  : _root_.expr → tactic (_root_.expr × _root_.expr)
| `(finmap.insert %%k %%x %%s) :=
  do (s',p₀) ← sort_finmap s,
     -- trace "• s'", trace s',
     f ← mk_insert' k x,
     p₁ ← mk_congr_arg f p₀,
     k ← instantiate_mvars k,
     (s'',p₂) ← insert_finmap k x s',
     prod.mk s'' <$> mk_eq_trans p₁ p₂
| s@`(∅ : asgn) :=
  do p ← mk_eq_refl s, pure (s, p)
| e := fail format!"can't sort: {e}"

meta def sorted_lhs : tactic unit :=
do (l,r) ← target >>= match_eq,
   (s,lp) ← sort_finmap l,
   note `lhs none lp,
   skip

meta def sorted_rhs : tactic unit :=
do (l,r) ← target >>= match_eq,
   (s,lp) ← sort_finmap r,
   note `rhs none lp,
   skip

meta def finmap_eq : tactic unit :=
do (l,r) ← target >>= match_eq,
   trace "•",
   trace_state,
   (s,lp) ← sort_finmap l,
   (s',rp) ← sort_finmap r,
   infer_type lp >>= trace,
   infer_type rp >>= trace,
   trace "•",
   trace_state,
   rewrite_target lp,
   trace "•",
   trace_state,
   rewrite_target rp,
   trace "•",
   trace_state,
   -- trace s, trace s',
   -- trace_state,
   -- mk_const ``finmap.insert_insert
   --   >>= simp_lemmas.mk.add
   --   >>= simp_target,
   reflexivity

run_cmd add_interactive [``finmap_eq,``sorted_rhs,``sorted_lhs]

end present
open is_lawful_monad

lemma rewrite_deref (m) (x) {α} (f : value → runtime α) (h : present x m . check_present) :
  (rewrite m >>= λ _, deref_ptr x >>= f) = rewrite m >>= λ _, f h.val :=
by { simp only [rewrite,deref_ptr] with monad_norm,
     congr, ext, rw [← is_lawful_monad.bind_assoc,state_t.put_get,is_lawful_monad.bind_assoc,pure_bind],
     congr, ext, cases h, congr,
     transitivity option.get_or_else (some h_val) (x_1 x),
     { rw h_property }, refl }

end semantics

namespace examples
open syntax syntax.type syntax.stmt syntax.lhs syntax.expr

def progs (_ : unit) : proc unit :=
{ params := [ ptr int, ptr int ],
  body := let x : ℕ := 2,
              y : ℕ := 1,
              t : ℕ := 0 in
           [ decl int,
             assgn (var t) (deref (var x)),
             assgn (deref (var x)) (deref (var y)),
             assgn (deref (var y)) (var t)
             ] }

def main₀ : list $ stmt unit :=
[ decl int, decl int,
  assgn (var 0) (lit 1),
  assgn (var 1) (lit 2) ]

def main₁ : list $ stmt unit :=
[ decl int, decl int,
  assgn (var 0) (lit 1),
  assgn (var 1) (lit 2),
  fun_call () [ addr_of 0, addr_of 1 ]  ]

open semantics

set_option trace.app_builder true

example : run progs main₀ =
          assign 0 (value.int 2) >>
          assign 1 (value.int 1) :=
begin
  apply ext,
  simp [c.semantics.run,main₀,eval_lhs,eval_expr,rewrite_assign,rewrite_assign',(>>),bind_pure_unit] with eqn_lemma,
  congr' 1,
  finmap_eq,
end

-- #eval (list.iota 2)

example : run progs main₁ =
          assign 0 (value.int 1) >>
          assign 1 (value.int 2) >>
          assign 2 (value.ptr 1) >>
          assign 3 (value.ptr 0) >>
          assign 4 (value.int 1) :=
begin
  -- have : (progs ()).params = _ :: _ := rfl,
  simp [c.semantics.run,main₁,eval_lhs,mmap,mmap',list.enum,list.enum_from,eval_stmt.intl._match_1,(>>),eval_expr,list.iota,progs] with eqn_lemma monad_norm,
  norm_num [nat.succ_eq_add_one],
  apply ext, simp [rewrite_assign,rewrite_assign',bind_pure_unit],
  repeat { rw rewrite_deref <|> simp [id,subtype.val,rewrite_assign,rewrite_assign'] },
  congr' 1,
  finmap_eq,
end

end examples


end c
