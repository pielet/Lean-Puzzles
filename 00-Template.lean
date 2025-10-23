
import AutograderLib

set_option pp.fieldNotation false

open List

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α -> α -> Tree α -> Tree α
  deriving Repr

open Tree

/- ***********************************************************************************
   Problem 1 (NK: exercise 2.6)
   *********************************************************************************** -/

 def contents {α : Type} (t: Tree α) : List α :=
  match t with
  | leaf => []
  | node l x r => contents l ++ (x :: contents r)

def sum_tree (t: Tree Nat) : Nat :=
  match t with
  | leaf => 0
  | node l x r => sum_tree l + x + sum_tree r

def sum_list (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs

/- HINT:  You may need a helper lemma -/


@[autogradedProof 10]
theorem sum_tree_contents : ∀ (t: Tree Nat), sum_tree t = sum_list (contents t) := by
 sorry

/- ***********************************************************************************
   Problem 2 (NK: exercise 2.7)
   *********************************************************************************** -/

def mirror {α : Type} (t: Tree α) : Tree α :=
  match t with
  | leaf => leaf
  | node l x r => node (mirror r) x (mirror l)

def pre_order {α : Type} (t: Tree α) : List α :=
  match t with
  | leaf => []
  | node l x r => x :: (pre_order l ++ pre_order r)

def post_order {α : Type} (t: Tree α) : List α :=
  match t with
  | leaf => nil
  | node l x r => post_order l ++ post_order r ++ [x]

@[autogradedProof 10]
theorem mirror_order : ∀ {α : Type} (t: Tree α), pre_order (mirror t) = reverse (post_order t) := by
 sorry


/- ***********************************************************************************
   Problem 3 (NK: exercise 2.8)
   *********************************************************************************** -/

-- (a) First, complete the implementation of `intersp` so that `test_intersp` is automatically verified.
def intersp {α : Type} (y: α) (xs : List α) : List α :=
 sorry

@[autogradedProof 5]
theorem test_intersp : intersp 0 [1,2,3,4,5] = [1,0,2,0,3,0,4,0,5] := by rfl

-- (b) Next, write a function `mymap` such that `test_map` is automatically verified
def mymap {α β : Type} (f : α -> β) (xs: List α) : List β :=
 sorry

@[autogradedProof 5]
theorem test_mymap : mymap (λ x => x * 10) [1,2,3] = [10,20,30] := by rfl

-- (c) Finally, prove the following theorem about `intersp` and `mymap`

@[autogradedProof 10]
theorem map_intersperse : (∀ {α β : Type} (f: α -> β) (y: α) (xs: List α), map f (intersp y xs) = intersp (f y) (map f xs)) := by
 sorry


/- ***********************************************************************************
   Problem 4 (NK: exercise 2.8)
   *********************************************************************************** -/
def tail_rec_add (n m: Nat) : Nat :=
  match n with
  | 0 => m
  | n' + 1 => tail_rec_add n' (m + 1)

@[autogradedProof 10]
theorem tail_rec_add_eq : ∀ (n m: Nat), tail_rec_add n m = n + m := by
 sorry

/- ***********************************************************************************
   Problem 5 (NK: exercise 2.10)
   *********************************************************************************** -/

-- HINT: You may find this theorem useful in your proof
theorem mul_shuffle : ∀ (a b c : Nat), a * (b * c) = b * (a * c) := by
  intros a b c
  calc
    a * (b * c) = (a * b) * c := by simp [Nat.mul_assoc]
    _           = (b * a) * c := by simp [Nat.mul_comm]
    _           = b * (a * c) := by simp [Nat.mul_assoc]

-- An `Exp` datatype to represent polynomials over a variable `x`
-- e ::= n | x | e + e | e * e

inductive Exp where
 | Var : Exp
 | Con : Nat -> Exp
 | Add : Exp -> Exp -> Exp
 | Mul : Exp -> Exp -> Exp
 deriving Repr

open Exp

-- `poly0` is a representation of `x + 10`
def poly0 : Exp := Add (Var) (Con 10)

-- `poly1` is a representation of `2x^2`
def poly1 : Exp := Mul (Con 2) (Mul Var Var)

-- `poly2` is a representation of `2x^2 + x + 10`
def poly2 : Exp := Add poly1 poly0

-- (a) Complete the definition of a function `eval` such that `eval e x` evaluates `e` at the value `x`;
-- when you are done, `eval_test` should be automatically checked.

def eval (e: Exp) (x: Nat) : Nat :=
 sorry

@[autogradedProof 5]
theorem eval_test : eval poly2 5 = 65 := rfl

-- A "compact" representation of polynomials as a list of coefficients, starting with the constant
-- For example, `[4, 2, 1, 3]` represents the polynomial `4 + 2.x + 1.x^2 + 3.x^3`, and
-- [10,1,2] represents the polynomial `10 + 1.x + 2.x^2` (i.e. `poly2`)

abbrev Poly := List Nat

-- (b) Complete the implementation of `evalp` so that `evalp_test` succeeds automatically
def evalp (p: Poly) (x: Nat) : Nat :=
 sorry

@[autogradedProof 5]
theorem evalp_test : evalp [10, 1, 2] 5 = eval poly2 5 := rfl

-- (c) Complete the implementation of `coeffs` so that `coeffs_test` succeeds automatically
-- HINT: you may need helper functions `addp` and `mulp` which *add* and *multiply* two `Poly`s


def coeffs (e: Exp) : Poly :=
 sorry

@[autogradedProof 20]
theorem coeffs_test : coeffs poly2 = [10, 1, 2] := by rfl


-- (d) Complete the proof of `eval_poly`; HINT: you will likely
-- require helper lemmas e.g. about the helper functions `addp` and `mulp`...



@[autogradedProof 30]
theorem eval_poly : ∀ (e:Exp) (x:Nat), evalp (coeffs e) x = eval e x := by
 sorry
