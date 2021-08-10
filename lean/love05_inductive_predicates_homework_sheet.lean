import .lovelib


/- # LoVe Homework 5: Inductive Predicates

Homework must be done individually. -/


set_option pp.beta true
set_option pp.generalized_field_notation false

namespace LoVe


/- ## Question 1 (3 points): A Type of λ-Terms

Recall the following type of λ-terms from question 3 of exercise 4. -/

inductive term : Type
| var : string → term
| lam : string → term → term
| app : term → term → term

/- 1.1 (1 point). Define an inductive predicate `is_app` that returns true if
and only if its argument has an `app` constructor at the top level. -/

-- enter your definition here

inductive is_app : term -> Prop
| app (t1 t2: term): is_app (term.app t1 t2)

/- 1.2 (2 points). Define an inductive predicate `is_abs_free` that is true if
and only if its argument is a λ-term that contains no λ-expressions. -/

-- enter your definition here

inductive is_app_free' : term -> Prop
| var (s: string): is_app_free' (term.var s)
| app (s: string) (t: term): is_app_free' t -> is_app_free' (term.lam s t)

inductive is_app_free : term -> Prop
| app (t1 t2: term):
  is_app_free' t1 -> is_app_free' t2 -> is_app_free (term.app t1 t2)


/- ## Question 2 (6 points): Even and Odd

Consider the following inductive definition of even numbers: -/

inductive even : ℕ → Prop
| zero            : even 0
| add_two {n : ℕ} : even n → even (n + 2)

/- 2.1 (1 point). Define a similar predicate for odd numbers, by completing the
Lean definition below. The definition should distinguish two cases, like `even`,
and should not rely on `even`. -/

inductive odd : ℕ → Prop
| one : odd 1
| add_two {n : ℕ} : odd n -> odd (n + 2)

/- 2.2 (1 point). Give proof terms for the following propositions, based on
your answer to question 2.1. -/

lemma odd_3 :
  odd 3 :=
odd.add_two odd.one

lemma odd_5 :
  odd 5 :=
odd.add_two odd_3

/- 2.3 (2 points). Prove the following lemma by rule induction, as a "paper"
proof. This is a good exercise to develop a deeper understanding of how rule
induction works (and is good practice for the final exam).

    lemma even_odd {n : ℕ} (heven : even n) :
      odd (n + 1) :=

Guidelines for paper proofs:

We expect detailed, rigorous, mathematical proofs. You are welcome to use
standard mathematical notation or Lean structured commands (e.g., `assume`,
`have`, `show`, `calc`). You can also use tactical proofs (e.g., `intro`,
`apply`), but then please indicate some of the intermediate goals, so that we
can follow the chain of reasoning.

Major proof steps, including applications of induction and invocation of the
induction hypothesis, must be stated explicitly. For each case of a proof by
induction, you must list the inductive hypotheses assumed (if any) and the goal
to be proved. Minor proof steps corresponding to `refl`, `simp`, or `linarith`
need not be justified if you think they are obvious (to humans), but you should
say which key lemmas they depend on. You should be explicit whenever you use a
function definition or an introduction rule for an inductive predicate. -/

-- enter your paper proof here

/-
lemma even_odd: ∀n: ℕ, even n -> odd (n + 1)

Proof:
  For some n, assume that n is even, we derive odd (n + 1) by
  induciton on even:

  (Base case) We assume even n = even 0 = even.zero. Then
    odd (0 + 1) = odd 1. One is odd by definition of odd (i.e. by odd.one).

  (Inductive step) IH: We assume even n -> odd (n + 1). Then
    even.add_two n -> odd.add_two (n + 1) =
      (by definition of even.add_two and odd.add_two)
    even (n + 2) -> odd (n + 3).
      By definition odd we know that odd (n + 3) only holds if odd (n + 1)
      holds. We assume that even (n + 2) hold. Therfore, by def. of even, even n
      also holds. Thus, by IH we know that odd (n + 1) hold and therfore
      odd (n + 3).
-/

/- 2.4 (1 point). Prove the same lemma again, but this time in Lean: -/

lemma even_odd {n : ℕ} (heven : even n) :
  odd (n + 1) :=
begin
  induction' heven,
    {simp, exact odd.one},
    {exact odd.add_two ih,}
end

/- 2.5 (1 point). Prove the following lemma in Lean.

Hint: Recall that `¬ a` is defined as `a → false`. -/

#check even_odd

lemma not_two_odd_in_row : ∀n : ℕ, odd n -> ¬ odd (n + 1) :=
begin
  intro n,
  induction' n,
  {rw not_def,
   assume h0,
   cases h0,},
  {intro h1,
   cases h1,
   {simp at ih,
    rw not_def,
    intro,
    cases a,
    have hn := ih a_a,
    have contra := and.intro hn h1,
    simp at contra,
    exact contra},
   {intro h,
    cases h,
    have hn := ih h_a,
    have contra := and.intro h1 hn,
    simp at contra,
    exact contra}}
end

lemma even_not_odd {n : ℕ} (heven : even n) :
  ¬ odd n :=
begin
  rw not_def,
  have h : odd (n+1) := even_odd heven,
  intro hn,
  have hn := not_two_odd_in_row n hn,
  have contra := and.intro h hn,
  simp at contra,
  exact contra,
end

-- lemma even_not_odd {n : ℕ} (heven : even n) :
--   ¬ odd n :=
-- begin
--   rw not_def,
--   have h : odd (n+1) := even_odd heven,
-- end

end LoVe
