import AutograderLib
set_option pp.fieldNotation false

/- ----------------------------------------------------------------
## Variables, Values and States
We have *two* kinds of values: `Nat` and `Bool`
---------------------------------------------------------------- -/

inductive Val where
  | VNat : Nat -> Val
  | VBool : Bool -> Val
  deriving Repr, BEq

open Val

abbrev Var := String

abbrev State := Var -> Val

-- update state
def upd (s: State) (x: Var) (v: Val) : State :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

/- ----------------------------------------------------------------
## Expressions
We have a *single* kind of `Exp` which will include both arith
and bool operations `Op`
---------------------------------------------------------------- -/

inductive Op where
  | Add
  | Sub
  | And
  | Or
  | Less
  deriving Repr

inductive Exp where
  | num  : Nat -> Exp
  | bool : Bool -> Exp
  | var  : Var  -> Exp
  | bin  : Op   -> Exp -> Exp -> Exp
  deriving Repr

open Exp

class ToExp (a : Type) where
  toExp : a -> Exp

@[simp]
instance : ToExp Nat where
  toExp := num

@[simp]
instance : ToExp String where
  toExp := var

@[simp]
instance : ToExp Exp where
  toExp a := a

@[simp]
instance : OfNat Exp (n: Nat) where
  ofNat := num n

@[simp]
instance : Add Exp where
  add := fun a1 a2 => bin Op.Add a1 a2

@[simp]
instance : HAdd String Exp Exp where
   hAdd := fun s a => bin Op.Add (var s) a

@[simp]
instance : HAdd String Nat Exp where
   hAdd := fun s a => bin Op.Add (var s) (num a)

@[simp]
instance : HAdd String String Exp where
   hAdd := fun s a => bin Op.Add (var s) (var a)

@[simp]
instance : HSub String Nat Exp where
   hSub := fun s a => bin Op.Sub (var s) (num a)


def mkVar (s: String) (i : Nat) : Exp := var (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs







/------------------------------------------------------------------------
## Commands
We now use the same `Exp` for assignments *and* for conditions; so now
you can have `bool` valued expressions and variables.
----------------------------------------------------------------------- -/

inductive Com where
  | Skip      : Com
  | Assign    : Var -> Exp -> Com
  | Seq       : Com -> Com -> Com
  | If        : Exp -> Com -> Com -> Com
  | While     : Exp -> Com -> Com
  deriving Repr

open Com

def bLess (a1 a2 : Exp) : Exp := bin Op.Less a1 a2

infix:10 "<<"  => fun x y => bLess (ToExp.toExp x) (ToExp.toExp y)
infix:10 "&&&" => fun x y => bin Op.And (ToExp.toExp x) (ToExp.toExp y)

infix:10 "<~"  => Com.Assign
infixr:8 ";;"  => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

------------------------------------------------------------------------------------------------
-- SmallStep Semantics
------------------------------------------------------------------------------------------------

-- A relation that defines when an operator can take two values `v1` and `v2` and produce an output `v`
inductive EvalOp : Op -> Val -> Val -> Val -> Prop where

   | Add : ∀ {n1 n2},
            EvalOp Op.Add (VNat n1) (VNat n2) (VNat (n1 + n2))

   | Sub : ∀ {n1 n2},
            EvalOp Op.Sub (VNat n1) (VNat n2) (VNat (n1 - n2))

   | And : ∀ {b1 b2},
            EvalOp Op.And (VBool b1) (VBool b2) (VBool (b1 && b2))

   | Or : ∀ {b1 b2},
            EvalOp Op.Or (VBool b1) (VBool b2) (VBool (b1 || b2))

   | Less : ∀ {n1 n2},
            EvalOp Op.Less (VNat n1) (VNat n2) (VBool (n1 < n2))


-- A relation that defines when an `Exp` can evaluate to a value `v` in some State `s`.
inductive Eval : State -> Exp -> Val -> Prop where

   | Num  : ∀ { s n },
            Eval s (num n) (VNat n)

   | Bool : ∀ { s b },
            Eval s (bool b) (VBool b)

   | Var  : ∀ { s x },
            Eval s (var x) (s x)

   | Bin  : ∀ { s o e1 e2 v1 v2 v },
            Eval s e1 v1 -> Eval s e2 v2 -> EvalOp o v1 v2 v ->
            Eval s (bin o e1 e2) v

abbrev Config := (Com × State)

inductive SmallStep : Config -> Config -> Prop where
   | Assign : ∀ {x a s v},
                Eval s a v ->
                SmallStep (x <~ a, s) (Skip, s [x := v])

   | Seq1   : ∀ {c s},
                SmallStep ((Skip ;; c), s) (c, s)

   | Seq2   : ∀ {c1 c1' c2 s s'},
                SmallStep (c1, s) (c1', s') ->
                SmallStep ((c1 ;; c2) , s) ((c1' ;; c2), s')

   | IfTrue : ∀ {b c1 c2 s},
                Eval s b (VBool true) ->
                SmallStep (IF b THEN c1 ELSE c2, s) (c1, s)

   | IfFalse : ∀ {b c1 c2 s},
                Eval s b (VBool false) ->
                SmallStep (IF b THEN c1 ELSE c2, s) (c2, s)

   | While   : ∀ { b c s },
                SmallStep (Com.While b c, s) (Com.If b (c ;; (Com.While b c)) Skip, s)

notation:12 "⟨" s "," e "⟩" "==>" v => Eval s e v
notation:12 cs "~~>" cs' => SmallStep cs cs'

/- -------------------------------------------------------------------------------------------------
## Problem 1. Determinism of Small-Step semantics
------------------------------------------------------------------------------------------------- -/


@[autogradedProof 10]
theorem evalop_deterministic: ∀ {o va vb v1 v2},
  EvalOp o va vb v1 -> EvalOp o va vb v2 -> v1 = v2
  := by
  sorry

@[autogradedProof 15]
theorem eval_deterministic: ∀ {s e v1 v2},
  (⟨s, e⟩ ==> v1) -> (⟨ s, e ⟩ ==> v2) -> v1 = v2
  := by
  sorry

@[autogradedProof 20]
theorem smallstep_deterministic: ∀ {cs cs1 cs2},
  (cs ~~> cs1) -> (cs ~~> cs2) -> cs1 = cs2
  := by
  sorry

/- -------------------------------------------------------------------------------------------------
## Problem 2. Type Soundness
------------------------------------------------------------------------------------------------- -/

-- A representation for *types* and *environments*

inductive Ty where
  | TNat  : Ty
  | TBool : Ty
  deriving Repr
open Ty

def type_of (v: Val) : Ty :=
  match v with
  | VNat _ => TNat
  | VBool _ => TBool

abbrev Env := Var -> Ty

-- A `s: State` is **well-formed** with respect to an `Γ: Env` if the type
-- of each variable's value in `s` is the same as described in `Γ`.

def Wf (Γ: Env) (s: State) : Prop :=
  ∀ x, Γ x = type_of (s x)

notation:10 Γ " ⊧ " s  => Wf Γ s

/- The relation `Op o t1 t2 t` says that when `o` is given two arguments
   of type `t1` and `t2` it returns a result of type `t`
   FILL IN THE DIFFERENT RULES for `OpTy` so that the ex0 checks; intuitively.
   (a) `Add` and `Sub` should take `TInt` arguments and return a `TInt` result;
   (b) `And` and `Or` should take `TBool` arguments and return a `TBool` result;
   (c) `Less` should take `TInt` arguments and return a `TBool` result.
   When you are done filling the rules for `OpTy` and `ExpTy`
   the `expXXX_is_TTT` theorems below should **automatically** be checked.
-/

inductive OpTy : Op -> Ty -> Ty -> Ty -> Prop

-- The relation `ExpTy Γ e t` says that `e` **has type** `t` in environment `Γ`

inductive  ExpTy : Env -> Exp -> Ty -> Prop where

notation:10 Γ " ⊢ " e " : " τ => ExpTy Γ e τ

@[simp] def x := "x"
@[simp] def y := "y"
@[simp] def z := "z"
@[simp] def b := "?b"


def exp0 : Exp := x#1 + y#1 + z#1 + 5
def exp1 : Exp := x + y
def exp2 : Exp := 2 + (z + 3)
def exp3 : Exp := ((x + 1) << (y - 2)) &&& b

-- #eval exp0

-- An env where every variable starting with `?` is a "bool", and rest are "int"
@[simp] def Γ₀ : Env := fun s => if s.get 0 = '?' then TBool else TNat

@[autogradedProof 20]
theorem exp0_is_nat : Γ₀ ⊢ exp0 : TNat := by
  repeat constructor

@[autogradedProof 20]
theorem exp1_is_nat : Γ₀ ⊢ exp1 : TNat := by
  repeat constructor

@[autogradedProof 20]
theorem exp2_is_nat : Γ₀ ⊢ exp2 : TNat := by
  repeat constructor

@[autogradedProof 20]
theorem exp3_is_bool : Γ₀ ⊢ exp3 : TBool := by
  repeat constructor

/- ------------------------------------------------------------
### Preservation
------------------------------------------------------------ -/


@[autogradedProof 15]
theorem op_preservation : ∀ {o t1 t2 t v1 v2},
  OpTy o t1 t2 t -> type_of v1 = t1 -> type_of v2 = t2 -> EvalOp o v1 v2 v -> type_of v = t
  := by
  sorry

@[autogradedProof 20]
theorem exp_preservation : ∀ {Γ e t s v},
  (Γ ⊧ s) -> (Γ ⊢ e : t) -> (⟨ s , e ⟩ ==> v) -> type_of v = t
  := by
  sorry

/- ------------------------------------------------------------
### Progress
------------------------------------------------------------ -/

theorem nat_val : ∀ {v}, type_of v = TNat <-> (∃n, v = VNat n)
  := by
  intros v; constructor
  . case mp => intros ty; cases v; simp_all; contradiction
  . case mpr => intros val; cases val; simp_all [type_of]

theorem bool_val : ∀ {v}, type_of v = TBool <-> (∃b, v = VBool b)
  := by
  intros v; constructor
  . case mp => intros ty; cases v; simp_all [type_of]; constructor; rfl
  . case mpr => intros val; cases val; simp_all [type_of]

-- HINT: use `nat_val` and `bool_val`

@[autogradedProof 20]
theorem op_progress : ∀ {o t1 t2 t v1 v2},
  OpTy o t1 t2 t -> type_of v1 = t1 -> type_of v2 = t2 -> ∃ v, EvalOp o v1 v2 v
  := by
  sorry

@[autogradedProof 20]
theorem exp_progress : ∀ {Γ e t s},
  (Γ ⊧ s) -> (Γ ⊢ e : t) -> (∃ v, ⟨ s, e ⟩ ==> v)
  := by
  sorry

/- ------------------------------------------------------------
### Soundness = Preservation + Progress
`exp_preservation` and `exp_progress` let us prove the soundness
of typechecking
------------------------------------------------------------ -/

theorem exp_sound : ∀ {Γ e t s},
  (Γ ⊧ s) -> (Γ ⊢ e : t) -> (∃ v, (⟨ s, e ⟩ ==> v) /\ type_of v = t)
  := by
  intros Γ e t s wf ty
  have val : ∃ v, ⟨ s, e ⟩ ==> v := by
    apply exp_progress; repeat assumption
  cases val
  repeat constructor
  assumption
  apply exp_preservation; repeat assumption

/- -------------------------------------------------------------------------------------------------
## Problem 3. Implement a Type Checker
------------------------------------------------------------------------------------------------- -/

def checkOp (o: Op) (t1 t2 : Ty) : Option Ty :=
  match o, t1, t2 with
  | Op.Add , Ty.TNat , Ty.TNat  => some TNat
  | Op.Sub , Ty.TNat , Ty.TNat  => some TNat
  | Op.Less, Ty.TNat , Ty.TNat  => some TBool
  | Op.And , Ty.TBool, Ty.TBool => some TBool
  | Op.Or  , Ty.TBool, Ty.TBool => some TBool
  | _      , _       , _        => none

theorem checkOp_sound : ∀ {o t1 t2 t},
  checkOp o t1 t2 = some t -> OpTy o t1 t2 t
  := by
  intros o t1 t2 t
  cases o <;> cases t1 <;> cases t2 <;> cases t <;>
    simp_all [checkOp]; intros; repeat constructor

-- Use `checkOp` to complete the definition of `checkExp`;
-- when you are done the `checkExpXXX` theorems below should automatically verify.

@[autogradedProof 20]
def checkExp (Γ : Env) (e: Exp) : Option Ty :=
  sorry

@[autogradedProof 5]
theorem checkExp0 : checkExp Γ₀ exp0 = some TNat  := by rfl

@[autogradedProof 5]
theorem checkExp1 : checkExp Γ₀ exp1 = some TNat  := by rfl

@[autogradedProof 5]
theorem checkExp2 : checkExp Γ₀ exp2 = some TNat  := by rfl

@[autogradedProof 5]
theorem checkExp3 : checkExp Γ₀ exp3 = some TBool := by rfl

-- HINT: use the correct "induction" and "generalization" ...

@[autogradedProof 30]
theorem checkExp_sound : ∀ {Γ e t},
  checkExp Γ e = some t -> (Γ ⊢ e : t)
  := by
  sorry


def eqTy (t1 t2 : Ty) : Bool :=
  match t1, t2 with
  | TNat, TNat   => true
  | TBool, TBool => true
  | _, _         => false

-- check if an `e:Exp` is a `t` in `Γ : Env`
def checkTy (Γ : Env) (e : Exp) (t: Ty) : Bool :=
  match checkExp Γ e with
  | some t1 => eqTy t t1
  | _       => false

@[simp] theorem eqTy_eq : ∀ {t1 t2},
  eqTy t1 t2 <-> t1 = t2
  := by
  intros t1 t2
  cases t1 <;> cases t2 <;> simp_all [eqTy]

theorem checkTy_t : ∀ {Γ e t},
  checkTy Γ e t <-> checkExp Γ e = some t
  := by
  intros Γ e _
  constructor
  . case mp =>
    generalize h : checkExp Γ e = te
    simp_all [checkTy]
    cases te <;> simp_all
  . case mpr =>
    intros ch
    simp_all [checkTy]

theorem checkTy_sound : ∀ {Γ e t},
  checkTy Γ e t -> (Γ ⊢ e : t)
  := by
  intros
  apply checkExp_sound
  simp_all [checkTy_t]

/- -------------------------------------------------------------------------------------------------
## Problem 4 [EXTRA-CREDIT-FOR-MIDTERM] Implement a Type Checker ... for Commands
------------------------------------------------------------------------------------------------- -/

-- The relation `ComTy Γ c` says that `c` **is well-typed** in environment `Γ`
-- Fill in the rules for `ComTy`; when you are done, theorem `com0_ok` should automatically verify.

inductive  ComTy : Env -> Com -> Prop where

notation:10 Γ " ⊢ " c  => ComTy Γ c

def com0 : Com :=
  (IF var b THEN x <~ x + 1 ELSE y <~ y + 1) ;;
  (WHILE exp3 DO z <~ z + 10 END)

@[autogradedProof 30]
theorem com0_ok : Γ₀ ⊢ com0 := by
  repeat constructor

@[autogradedProof 30]
theorem com_preservation_c : ∀ {Γ c s c' s'},
  (Γ ⊧ s) -> (Γ ⊢ c) -> ((c, s) ~~> (c', s')) -> (Γ ⊢ c')
  := by
  sorry

@[autogradedProof 30]
theorem com_preservation_s : ∀ {Γ c s c' s'},
  (Γ ⊧ s) -> (Γ ⊢ c) -> ((c, s) ~~> (c', s')) -> (Γ ⊧ s')
  := by
  sorry


-- HINT: use `exp_preservation` and `exp_progress`
@[autogradedProof 30]
theorem eval_bool : ∀ { Γ e s },
  (Γ ⊧ s) -> (Γ ⊢ e : TBool) -> (∃ v, ⟨ s , e ⟩ ==> VBool v)
  := by
  sorry

-- HINT: in the `c1;;c2` case you may need to a `by_cases c1_skip : c1 = Skip` (i.e. to split cases on whether `c1` is `Skip`).
-- HINT: in the `if e c1 c2` case use `eval_bool` to deduce the `Eval s e (VBool b)` and the do a `cases b` to apply SmallStep.IfFalse or SmallStep.IfTrue
@[autogradedProof 30]
theorem com_progress: ∀ {Γ c s},
  (Γ ⊧ s) -> (Γ ⊢ c) -> ¬ (c = Skip) -> (∃ cs', (c, s) ~~> cs')
  := by
  sorry

-- Fill in the definition of `checkCom` which is a *function* that can be run on a `Com` to check if it is well-typed.

@[autogradedProof 30]
def checkCom (Γ : Env) (c: Com) : Bool :=
  sorry

-- When you are done the below should automatically verify
theorem checkCom0 : checkCom Γ₀ com0 = true := by rfl

@[autogradedProof 30]
-- use `checkTy_sound` to prove the below.
theorem checkCom_sound : ∀ {Γ c},
  checkCom Γ c -> (Γ ⊢ c)
  := by
  sorry
