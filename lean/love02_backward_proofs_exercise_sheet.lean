import .love02_backward_proofs_demo


/- # LoVe Exercise 2: Backward Proofs -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe

namespace backward_proofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 2.3 in the Hitchhiker's Guide. -/

lemma I (a : Prop) :
  a → a :=
begin
  intro ha,
  exact ha
end

lemma K (a b : Prop) :
  a → b → b :=
begin
  intros ha hb,
  exact hb
end

lemma C (a b c : Prop) :
  (a → b → c) → b → a → c :=
begin
  intro haibic,
  intro hb,
  intro ha,
  apply haibic,
  {apply ha,},
  {apply hb}
end

lemma proj_1st (a : Prop) :
  a → a → a :=
begin
  intros ha1 ha2,
  exact ha1,
end

/- Please give a different answer than for `proj_1st`: -/

lemma proj_2nd (a : Prop) :
  a → a → a :=
begin
  intros ha1 ha2,
  exact ha2,
end

lemma some_nonsense (a b c : Prop) :
  (a → b → c) → a → (a → c) → b → c :=
begin
  intros haibic ha haic hb,
  apply haic,
  apply ha,
end

/- 1.2. Prove the contraposition rule using basic tactics. -/

lemma contrapositive (a b : Prop) :
  (a → b) → ¬ b → ¬ a :=
begin
  intros haib,
  rw not_def,
  rw not_def,
  intro hnb,
  intro ha,
  apply hnb,
  apply haib,
  exact ha
end

/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap₂` in the lecture, might be
necessary. -/

lemma forall_and {α : Type} (p q : α → Prop) :
  (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
begin
  apply iff.intro,
  {intro hpq,
   apply and.intro,
   {intro x,
    apply and.elim_left,
    apply hpq,},
   {intro x,
    apply and.elim_right,
    apply hpq,}},
  {intro h,
   intro x,
   apply and.intro,
   {apply and.elim_left h,},
   {apply and.elim_right h,}}
end


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul

lemma mul_zero (n : ℕ) :
  mul 0 n = 0 :=
begin
  induction' n,
  {rw mul},
  {rw mul, rw ih, rw add,}
end

lemma mul_succ (m n : ℕ) :
  mul (nat.succ m) n = add (mul m n) n :=
begin
  induction' n,
  {simp [mul, add],},
  {simp [mul, add, ih, add_succ, add_assoc], }
end

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction'` tactic. Choose the induction variable carefully. -/

lemma mul_comm (m n : ℕ) :
  mul m n = mul n m :=
begin
  induction' n,
  {rw mul, rw mul_zero,},
  {rw mul, rw ih, rw mul_succ, rw add_comm,}
end  

lemma mul_assoc (l m n : ℕ) :
  mul (mul l m) n = mul l (mul m n) :=
begin
  induction' n,
  {rw mul, rw mul, rw mul,},
  {simp [mul, mul_add, ih]}
end

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

lemma add_mul (l m n : ℕ) :
  mul (add l m) n = add (mul n l) (mul n m) :=
begin
  induction' n,
  {rw mul, rw mul_zero, rw mul_zero, rw add},
  {simp [mul, ih, mul_add, mul_comm], }
end


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def excluded_middle :=
∀a : Prop, a ∨ ¬ a

def peirce :=
∀a b : Prop, ((a → b) → a) → a

def double_negation :=
∀a : Prop, (¬¬ a) → a

/- For the proofs below, please avoid using lemmas from Lean's `classical`
namespace, because this would defeat the purpose of the exercise.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `or.elim` and `false.elim`. You can use
`rw excluded_middle` to unfold the definition of `excluded_middle`,
and similarly for `peirce`. -/

lemma peirce_of_em :
  excluded_middle → peirce :=
begin
  rw excluded_middle,
  rw peirce,
  intro em,
  intros a b,
  apply or.elim (em a),
  {intros ha haba,
   exact ha},
  {rw not_def,
   intros hna haba,
   apply haba,
   intros ha,
   apply false.elim,
   apply hna,
   assumption,
  }
end

/- 3.2 (**optional**). Prove the following implication using tactics. -/

lemma dn_of_peirce :
  peirce → double_negation :=
begin
  rw peirce,
  rw double_negation,
  intro h,
  intro a,
  rw not_def,
  rw not_def,
  intro nna,
  apply h a false,
  intro aif,
  apply false.elim,
  apply nna,
  exact aif,
end

/- We leave the missing implication for the homework: -/

namespace sorry_lemmas

lemma em_of_dn :
  double_negation → excluded_middle :=
begin
  rw double_negation,
  rw excluded_middle,
  intro h,
  intro a,
  apply h,
  rw not_def,
  rw not_def,
  intro horf,
  apply horf,
  apply or.intro_left,
  apply h,
  rw not_def, rw not_def,
  intro haf,
  apply horf,
  apply or.intro_right,
  rw not_def,
  assumption,
end

end sorry_lemmas

end backward_proofs

end LoVe
