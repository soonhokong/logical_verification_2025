/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Demo 3: Backward Proofs

A __tactic__ operates on a proof goal and either proves it or creates new
subgoals. Tactics are a __backward__ proof mechanism: They start from the goal
and work towards the available hypotheses and theorems. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## Tactic Mode

Syntax of tactical proofs:

    by
      _tactic₁_
      …
      _tacticN_

The keyword `by` indicates to Lean the proof is tactical. -/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  by
  intros a b ha hb
  apply ha

/- Note that `a → b → a` is parsed as `a → (b → a)`.

Propositions in Lean are terms of type `Prop`. `Prop` is a type, just like `Nat`
and `List Bool`. In fact there is a close correspondence between propositions
and types, which will be explained in lecture 4.


## Basic Tactics

`intro` moves `∀`-quantified variables, or the assumptions of implications `→`,
from the goal's conclusion (after `⊢`) into the goal's hypotheses (before `⊢`).

`apply` matches the goal's conclusion with the conclusion of the specified
theorem and adds the theorem's hypotheses as new goals. -/

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
    a :=
  by
  apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha

/- The above proof step by step:

* Assume we have a proof of `a`.
* The goal is `c`, which we can show if we prove `b` (from `hbc`).
* The goal is `b`, which we can show if we prove `a` (from `hab`).
* We already know `a` (from `ha`).

Next, `exact` matches the goal's conclusion with the specified theorem, closing
the goal. We can often use `apply` in such situations, but `exact` communicates
our intentions better. -/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
    a :=
  by exact ha

/- `assumption` finds a hypothesis from the local context that matches the
goal's conclusion and applies it to prove the goal. -/

theorem fst_of_two_props_assumption (a b : Prop)
      (ha : a) (hb : b) :
    a :=
  by
    assumption
  -- assumption

/- `rfl` proves `l = r`, where the two sides are syntactically equal up to
computation. Computation means unfolding of definitions, β-reduction
(application of `fun` to an argument), `let`, and more. -/

-- Alpha-conversion (α-conversion) in Lean refers to the automatic
-- renaming of bound variables. It's one of the definitional equalities that Lean's
-- kernel recognizes when checking rfl (reflexivity).

theorem α_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl

-- Beta-conversion: substituting an argument into a function's body.
theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x ↦ f x) a = f a :=
  by rfl

def double (n : ℕ) : ℕ :=
  n + n

-- Delta-conversion: unfolding definitions.
theorem δ_example :
    double 5 = 5 + 5 :=
  by rfl

/- `let` introduces a definition that is locally scoped. Below, `n := 2` is only
in scope in the expression `n + n`. -/

theorem ζ_example :
    (let n : ℕ := 2
     n + n) = 4 :=
  by rfl


-- eta-conversion: function extentionality
-- A function is equal to its eta-expansion:
-- (λx. f x) => f
theorem η_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = f :=
  by rfl

/- `(a, b)` is the pair whose first component is `a` and whose second component
is `b`. `Prod.fst` is a so-called projection that extracts the first component
of a pair. -/

-- iota-conversion. reducing pattern matches & recursors.
theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a :=
  by rfl

-- propositional equality: the ones that require proofs.
example (n : Nat) : n + 0 = n := by rfl

example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [ih]

/- ## Reasoning about Logical Connectives and Quantifiers

Introduction rules: -/

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

def h1 : Exists (· > 0) := Exists.intro (5 : Nat) (by simp  : (fun x => x > 0) 5)
#check h1

#check Exists.elim h1 x

example : ∃ n : Nat, n > 5 := by
  exact ⟨10, by trivial⟩

example : ∃ n : Nat, n > 0 → ∃ m : Nat, m < n := by
  exists 1
  intro h1
  exact ⟨0, by assumption⟩

example (h : ∃ x : Nat, x > 10) : ∃ y : Nat, y > 5 := by
  apply Exists.elim h
  intros a ha
  exists a
  grind only


/- Elimination rules: -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- Definition of `¬` and related theorems: -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- There are no explicit rules for `Not` (`¬`) since `¬ p` is defined as
`p → False`. -/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    exact ⟨hab.2, hab.1⟩

/- The above proof step by step:

* Assume we know `a ∧ b`.
* The goal is `b ∧ a`.
* Show `b`, which we can if we can show a conjunction with `b` on the right.
* We can, we already have `a ∧ b`.
* Show `a`, which we can if we can show a conjunction with `a` on the left.
* We can, we already have `a ∧ b`.

The `{ … }` combinator focuses on a specific subgoal. The tactic inside must
fully prove it. In the proof below, `{ … }` is used for each of the two subgoals
to give more structure to the proof. -/

theorem And_swap_braces :
    ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

/- Notice above how we pass the hypothesis `hab` directly to the theorems
`And.right` and `And.left`, instead of waiting for the theorems' assumptions to
appear as new subgoals. This is a small forward step in an otherwise backward
proof. -/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
    f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  by
    intro hab
    apply hab.elim
    . intro ha
      exact Or.inr ha
    . intro hb
      exact Or.inl hb

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  by
    intro hab ha
    apply hab ha

theorem Not_Not_intro (a : Prop) :
    a → ¬¬ a :=
  by
    intro ha hna
    apply hna ha

theorem Exists_double_iden :
    ∃n : ℕ, double n = n :=
  by
    exact ⟨0, by rfl⟩

/- ## Reasoning about Equality -/

#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- The above rules can be used directly: -/

theorem Eq_trans_symm {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans
    . apply hab
    . apply hcb.symm

/- `rw` applies a single equation as a left-to-right rewrite rule, once. To
apply an equation right-to-left, prefix its name with `←`. -/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    rw [hcb]
    assumption

/- `rw` can expand a definition. Below, `¬¬ a` becomes `¬ a → False`, and `¬ a`
becomes `a → False`. -/

theorem a_proof_of_negation (a : Prop) :
    a → ¬¬ a :=
  by
    simp only [Not]
    intro ha hna
    apply hna ha
/- `simp` applies a standard set of rewrite rules (the __simp set__)
exhaustively. The set can be extended using the `@[simp]` attribute. Theorems
can be temporarily added to the simp set with the syntax
`simp [_theorem₁_, …, _theoremN_]`. -/

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
      (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 :=
  by rw [hab, hcd]

/- `ac_rfl` is similar to `rfl`, but it can reason up to associativity and
commutativity of `+`, `*`, and other binary operators. -/

theorem abc_Eq_cba (a b c : ℕ) :
    a + b + c = c + b + a :=
  by ac_rfl


/- ## Proofs by Mathematical Induction

`induction` performs induction on the specified variable. It gives rise to one
named subgoal per constructor. -/

-- Soonho: 2025/11/17 working on this.

theorem add_zero (n : ℕ) :
    add 0 n = n :=
  by
    induction n with
    | zero => rfl
    | succ n' ih =>
      rewrite [add]
      rewrite [ih]
      rfl

-- (m + 1) + n = (m + n) + 1
theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero => rfl
    | succ n' ih =>
      rewrite [add]
      rewrite [ih]
      rewrite [add]
      rfl

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    induction n with
    | zero       =>
      rewrite [add_zero]
      rewrite [add]
      rfl
    | succ n' ih =>
      -- m + (n' + 1) = (n' + 1) + m
      rewrite [add]
      -- (m + n') + 1 = (n' + 1) + m
      rewrite [ih]
      -- (n' + m) + 1 = (n' + 1) + m
      rewrite [add_succ]
      -- (n' + m) + 1 = (n' + m) + 1
      rfl

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       =>
    | succ n' ih =>

/- `ac_rfl` is extensible. We can register `add` as a commutative and
associative operator using the type class instance mechanism (explained in
lecture 5). This is useful for the `ac_rfl` invocation below. -/

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl


/- ## Cleanup Tactics

`clear` removes unused variables or hypotheses.

`rename` changes the name of a variable or hypothesis. -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
      (hab : a → b) (hbc : b → c) :
    c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end LoVe
