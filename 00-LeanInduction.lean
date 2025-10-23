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

theorem sum_list_helper: ∀ (l1 l2: List Nat), sum_list (l1 ++ l2) = sum_list l1 + sum_list l2 := by
  intros l1 l2
  induction l1
  . case nil => simp [sum_list]
  . case cons x xs ih => simp +arith [sum_list, ih]

theorem sum_tree_contents : ∀ (t: Tree Nat), sum_tree t = sum_list (contents t) := by
  intros t
  induction t
  . case leaf => rfl
  . case node l x r ih_r ih_l => simp +arith [sum_tree, contents, sum_list_helper, sum_list,
    *]

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

theorem mirror_order : ∀ {α : Type} (t: Tree α), pre_order (mirror t) = reverse (post_order t) := by
  intros α t
  induction t
  . case leaf => rfl
  . case node l x r ih_l ih_r => simp +arith [mirror, pre_order, post_order, *]

/- ***********************************************************************************
   Problem 3 (NK: exercise 2.8)
   *********************************************************************************** -/

-- (a) First, complete the implementation of `intersp` so that `test_intersp` is automatically verified.
def intersp {α : Type} (y: α) (xs : List α) : List α :=
  match xs with
  | [] => []
  | x :: [] => [x]
  | x :: xs' => x :: y :: intersp y xs'

theorem test_intersp : intersp 0 [1,2,3,4,5] = [1,0,2,0,3,0,4,0,5] := by rfl

-- (b) Next, write a function `mymap` such that `test_map` is automatically verified
def mymap {α β : Type} (f : α -> β) (xs: List α) : List β :=
  match xs with
  | [] => []
  | x :: xs' => f x :: mymap f xs'

theorem test_mymap : mymap (λ x => x * 10) [1,2,3] = [10,20,30] := by rfl

-- (c) Finally, prove the following theorem about `intersp` and `mymap`

theorem map_intersperse : (∀ {α β : Type} (f: α -> β) (y: α) (xs: List α), map f (intersp y xs) = intersp (f y) (map f xs)) := by
  intros α β f y xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons x' xs' => simp [intersp, map, ih]

/- ***********************************************************************************
   Problem 4 (NK: exercise 2.8)
   *********************************************************************************** -/

open Nat

def tail_rec_add (n m: Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => tail_rec_add n' (succ m)

theorem tr_add_succ : ∀ (n m: Nat), tail_rec_add n (succ m) = succ (tail_rec_add n m) := by
  intros n m
  induction n generalizing m with
  | zero => simp [tail_rec_add]
  | succ n' ih => simp +arith [tail_rec_add, ih]

theorem tail_rec_add_eq : ∀ (n m: Nat), tail_rec_add n m = n + m := by
  intros n m
  induction n with
  | zero => simp [tail_rec_add]
  | succ n' ih => simp +arith [tail_rec_add, tr_add_succ, ih]

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
  match e with
  | Var => x
  | Con n => n
  | Exp.Add e1 e2 => eval e1 x + eval e2 x
  | Exp.Mul e1 e2 => eval e1 x * eval e2 x

theorem eval_test : eval poly2 5 = 65 := rfl

-- A "compact" representation of polynomials as a list of coefficients, starting with the constant
-- For example, `[4, 2, 1, 3]` represents the polynomial `4 + 2.x + 1.x^2 + 3.x^3`, and
-- [10,1,2] represents the polynomial `10 + 1.x + 2.x^2` (i.e. `poly2`)

abbrev Poly := List Nat

-- (b) Complete the implementation of `evalp` so that `evalp_test` succeeds automatically
def evalp (p: Poly) (x: Nat) : Nat :=
  match p with
  | [] => 0
  | c :: p' => c + x * evalp p' x

theorem evalp_test : evalp [10, 1, 2] 5 = eval poly2 5 := rfl

-- (c) Complete the implementation of `coeffs` so that `coeffs_test` succeeds automatically
-- HINT: you may need helper functions `addp` and `mulp` which *add* and *multiply* two `Poly`s

def addp : Poly -> Poly -> Poly
  | [], p => p
  | p, [] => p
  | c1 :: p1, c2 :: p2 => (c1 + c2) :: addp p1 p2

def mulvp (v : Nat) (p : Poly) :=
  mymap (λ x => v * x) p

def mulp (p1 p2: Poly) : Poly :=
  match p1, p2 with
  | [], _ => []
  | _, [] => []
  | c1 :: p1', c2 :: p2' => c1 * c2 :: addp (mulvp c1 p2') (mulp p1' p2)

def coeffs (e: Exp) : Poly :=
  match e with
  | Var => [0, 1]
  | Con n => [n]
  | Exp.Add e1 e2 => addp (coeffs e1) (coeffs e2)
  | Exp.Mul e1 e2 => mulp (coeffs e1) (coeffs e2)

theorem coeffs_test : coeffs poly2 = [10, 1, 2] := by rfl

-- (d) Complete the proof of `eval_poly`; HINT: you will likely
-- require helper lemmas e.g. about the helper functions `addp` and `mulp`...

theorem addp_helper : ∀ (p1 p2: Poly) (x: Nat), evalp (addp p1 p2) x = evalp p1 x + evalp p2 x := by
  intros p1 p2 x
  induction p1, p2 using addp.induct
  . case case1 => simp [addp, evalp]
  . case case2 => simp [addp, evalp]
  . case case3 ih => simp +arith [addp, evalp, Nat.mul_add, ih]

theorem mulvp_helper : ∀ (v: Nat) (p: Poly) (x: Nat), evalp (mulvp v p) x = v * evalp p x := by
  intros v p x
  induction p with
  | nil => simp [mulvp, evalp, mymap]
  | cons c cs ih => simp_all [mulvp, evalp, mymap, Nat.mul_add, mul_shuffle]

theorem mulp_helper : ∀ (p1 p2: Poly) (x: Nat), evalp (mulp p1 p2) x = evalp p1 x * evalp p2 x := by
  intros p1 p2 x
  induction p1 with
  | nil =>
      simp [mulp, evalp]
  | cons c1 p1' ih =>
      cases p2 with
      | nil => simp [mulp, evalp]
      | cons c2 p2' =>
          simp_all (arith := true) [mulp, evalp, addp_helper, mulvp_helper, Nat.mul_add, mul_shuffle, Nat.mul_comm]

theorem eval_poly : ∀ (e:Exp) (x:Nat), evalp (coeffs e) x = eval e x := by
  intros e x
  induction e with
  | Var => simp [coeffs, evalp, eval]
  | Con n => simp [coeffs, evalp, eval]
  | Add e1 e2 ih1 ih2 => simp [coeffs, addp_helper, eval, ih1, ih2]
  | Mul e1 e2 ih1 ih2 => simp [coeffs, mulp_helper, eval, ih1, ih2]
