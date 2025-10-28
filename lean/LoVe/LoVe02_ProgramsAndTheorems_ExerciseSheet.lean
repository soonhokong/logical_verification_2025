/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Exercise 2: Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Predecessor Function

1.1. Define the function `pred` of type `ℕ → ℕ` that returns the predecessor of
its argument, or 0 if the argument is 0. For example:

    `pred 7 = 6`
    `pred 0 = 0` -/

def pred : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

/- 1.2. Check that your function works as expected. -/
#guard pred 0 = 0
#guard pred 1 = 0
#guard pred 2 = 1
#guard pred 3 = 2
#guard pred 10 = 9
#guard pred 99 = 98

/- ## Question 2: Arithmetic Expressions

Consider the type `AExp` from the lecture and the function `eval` that
computes the value of an expression. You will find the definitions in the file
`LoVe02_ProgramsAndTheorems_Demo.lean`. One way to find them quickly is to

1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
2. move the cursor to the identifier `AExp` or `eval`;
3. click the identifier. -/

#check AExp
#check eval

/- 2.1. Test that `eval` behaves as expected. Make sure to exercise each
constructor at least once. You can use the following environment in your tests.
What happens if you divide by zero?

Note that `#eval` (Lean's evaluation command) and `eval` (our evaluation
function on `AExp`) are unrelated. -/

def someEnv : String → ℤ
  | "x" => 3
  | "y" => 17
  | _   => 201

#eval eval someEnv (AExp.var "x")   -- expected: 3
-- invoke `#eval` here

/- 2.2. The following function simplifies arithmetic expressions involving
addition. It simplifies `0 + e` and `e + 0` to `e`. Complete the definition so
that it also simplifies expressions involving the other three binary
operators. -/

def simplify : AExp → AExp
  | AExp.add (AExp.num 0) e₂ => simplify e₂
  | AExp.add e₁ (AExp.num 0) => simplify e₁
  | AExp.sub e₁ (AExp.num 0) => simplify e₁
  | AExp.mul _ (AExp.num 0) => AExp.num 0
  | AExp.mul (AExp.num 0) _ => AExp.num 0
  | AExp.div (AExp.num 0) _ => AExp.num 0
  -- insert the missing cases here
  -- catch-all cases below
  | AExp.num i               => AExp.num i
  | AExp.var x               => AExp.var x
  | AExp.add e₁ e₂           => AExp.add (simplify e₁) (simplify e₂)
  | AExp.sub e₁ e₂           => AExp.sub (simplify e₁) (simplify e₂)
  | AExp.mul e₁ e₂           => AExp.mul (simplify e₁) (simplify e₂)
  | AExp.div e₁ e₂           => AExp.div (simplify e₁) (simplify e₂)

/- 2.3. Is the `simplify` function correct? In fact, what would it mean for it
to be correct or not? Intuitively, for `simplify` to be correct, it must
return an arithmetic expression that yields the same numeric value when
evaluated as the original expression.

Given an environment `env` and an expression `e`, state (without proving it)
the property that the value of `e` after simplification is the same as the
value of `e` before. -/

theorem simplify_correct (env : String → ℤ) (e : AExp) :
  eval env e = eval env (simplify e) :=   -- replace `True` by your theorem statement
  sorry   -- leave `sorry` alone


/- ## Question 3 (**optional**): Map

3.1 (**optional**). Define a generic `map` function that applies a function to
every element in a list. -/

def map {α : Type} {β : Type} (f : α → β) : List α → List β
  | [] => []
  | x :: xs => f x :: map f xs


#eval map (fun n ↦ n + 10) [1, 2, 3]   -- expected: [11, 12, 13]
#guard (map (fun n ↦ n + 10) [1, 2, 3]) = [11,12,13]   -- expected: [11, 12, 13]


/- 3.2 (**optional**). State (without proving them) the so-called functorial
properties of `map` as theorems. Schematically:

     map (fun x ↦ x) xs = xs
     map (fun x ↦ g (f x)) xs = map g (map f xs)

Try to give meaningful names to your theorems. Also, make sure to state the
second property as generally as possible, for arbitrary types. -/

-- enter your theorem statements here

theorem mapId {α : Type} (xs : List α) : map (fun x ↦ x) xs = xs := by sorry
theorem map2 {α β γ: Type} (xs : List α) (f : α → β) (g : β → γ) : map (fun x ↦ g $ f $ x) xs = map g (map f xs) := by sorry


end LoVe
