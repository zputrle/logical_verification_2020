import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

set_option pp.beta true
set_option pp.generalized_field_notation false

namespace TestMutState

@[class] structure lawful_monad (m : Type → Type)
  extends has_bind m, has_pure m :=
(pure_bind {α β : Type} (a : α) (f : α → m β) :
   (pure a >>= f) = f a)
(bind_pure {α : Type} (ma : m α) :
   (ma >>= pure) = ma)
(bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
     (ma : m α) :
   ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)))

/- ## Mutable State -/

def action (σ α : Type) :=
σ → α × σ

#check action

def action.read {σ : Type} : action σ σ
| s := (s, s)

#check action.read

def action.write {σ : Type} (s : σ) : action σ unit
| _ := ((), s)

#check action.write

def action.pure {σ α : Type} (a : α) : action σ α
| s := (a, s)

def action.bind {σ : Type} {α β : Type} (ma : action σ α)
    (f : α → action σ β) :
  action σ β
| s :=
  match ma s with
  | (a, s') := (f a) s'
  end

@[instance] def action.lawful_monad {σ : Type} :
  lawful_monad (action σ) :=
{ pure       := @action.pure σ,
  bind       := @action.bind σ,
  pure_bind  :=
    begin
      intros α β a f,
      apply funext,
      intro s,
      refl
    end,
  bind_pure  :=
    begin
      intros α ma,
      apply funext,
      intro s,
      simp [action.bind],
      cases' ma s,
      refl
    end,
  bind_assoc :=
    begin
      intros α β γ f g ma,
      apply funext,
      intro s,
      simp [action.bind],
      cases' ma s,
      refl
    end }

-- ## Some examples

def write_and_then_read_list (ls : list ℕ) : action (list ℕ) (list ℕ) :=
  do
    action.write ls,
    ls' <- action.read,
    (pure ls')

def write_and_then_read_list' (ls : list ℕ) : action (list ℕ) (list ℕ) :=
    let ac := (action.bind (action.write ls) (λx, action.read)) in
      action.bind ac (λls', pure ls')

end TestMutState

namespace TestMutState'

@[class] structure lawful_monad (m : Type → Type)
  extends has_bind m, has_pure m :=
(pure_bind {α β : Type} (a : α) (f : α → m β) :
   (pure a >>= f) = f a)
(bind_pure {α : Type} (ma : m α) :
   (ma >>= pure) = ma)
(bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
     (ma : m α) :
   ((ma >>= f) >>= g) = (ma >>= (λa, f a >>= g)))

-- Action accepts a state, performs the action and returns the result + new state.
def action (ty_st ty_rt: Type) := ty_st -> ty_rt × ty_st

-- Action that returns (and preserves) the current state.
def action.read {ty_st: Type} : action ty_st ty_st
| st := (st, st)

-- Action that stores the provided (new) state and discards the old state
-- (that is provided as an input to the action).
def action.write {ty_st: Type} (new_st : ty_st): action ty_st unit
-- | old_st := ((), new_st)
| _ := ((), new_st)

def action.pure {ty_st ty_rt: Type} (r : ty_rt) : action ty_st ty_rt
| st := (r, st) 

def action.bind
  {ty_st ty_rt ty_rt': Type}
  (ac: action ty_st ty_rt)
  (f: ty_rt -> action ty_st ty_rt') 
  : action ty_st ty_rt'
| st :=
  -- perform action
  let action_rs := ac st in
  match action_rs with
  | (rt', st') := 
    -- perform function
    let f_rs := (f rt') in
    -- provide a new state
    f_rs st'
  end

@[instance] def action.lawful_monad {σ : Type} :
  lawful_monad (action σ) :=
{ pure       := @action.pure σ,
  bind       := @action.bind σ,
  pure_bind  := sorry,
  bind_pure  := sorry,
  bind_assoc := sorry
}

def diff_list : list ℕ -> action ℕ (list ℕ)
| [] := pure []
| (v :: tl) := (
  do hv ← (@action.read ℕ),
  if v > hv then
    do action.write v,
    do ls' ← diff_list tl,
    pure (v :: ls')
  else
    diff_list tl
)

#eval diff_list [1, 2, 3, 2] 0
#eval diff_list [1, 2, 3, 2, 4, 5, 2] 0

end TestMutState'