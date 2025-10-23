
import AutograderLib

set_option pp.fieldNotation false

--------------------------------------------------------------------------------
-- | Variables, Values and States ----------------------------------------------
--------------------------------------------------------------------------------
abbrev Val := Nat
abbrev Vname := String

abbrev State := Vname -> Val

-- update state
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if x == y then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

theorem get_upd : ∀ {x s v}, (upd s x v) x = v := by
  intros x s v
  simp [upd]

theorem get_not_upd : ∀ {x y s v}, ¬ (x = y) -> (upd s x v) y = s y := by
  intros x y s v neq
  simp [upd]
  intros eq
  contradiction

--------------------------------------------------------------------------------
-- | Arithmetic Expressions
--------------------------------------------------------------------------------

inductive AExp where
  | num : Val -> AExp
  | var : Vname -> AExp
  | plus : AExp -> AExp -> AExp
  deriving Repr

def aval (a: AExp) (s: State) : Val :=
  match a with
  | AExp.num n => n
  | AExp.var x => s x
  | AExp.plus e1 e2 => aval e1 s + aval e2 s

inductive BExp where
| bool : Bool -> BExp          -- True, False
| not : BExp -> BExp           -- not b
| and : BExp -> BExp -> BExp   -- b1 && b2
| less : AExp -> AExp -> BExp  -- a1 < a2
deriving Repr

namespace BExp
def or (b1 b2: BExp) : BExp := BExp.not (BExp.and (BExp.not b1) (BExp.not b2))

def imp (b1 b2: BExp) : BExp := BExp.or (BExp.not b1) b2
end BExp

def bval (b: BExp) (s: State) : Bool :=
  match b with
  | BExp.bool t => t
  | BExp.not b => not (bval b s)
  | BExp.and b1 b2 => (bval b1 s) && (bval b2 s)
  | BExp.less a1 a2 => (aval a1 s) < (aval a2 s)

--------------------------------------------------------------------------------
-- | Let Expressions
--------------------------------------------------------------------------------

inductive LExp where
| num : Val -> LExp
| var : Vname -> LExp
| plus : LExp -> LExp -> LExp
| llet : Vname -> LExp -> LExp -> LExp
deriving Repr

open LExp

-- | `lval l s` takes a let-bound expression and a State and returns the result
--    of evaluating `l` in `s`:
def lval (e: LExp) (s: State) : Val :=
  match e with
  | num n => n
  | var x => s x
  | plus e1 e2 => lval e1 s + lval e2 s
  | llet x e1 e2 => lval e2 (s [ x := lval e1 s ] )

--------------------------------------------------------------------------------
-- | Q1 : Relations
--------------------------------------------------------------------------------

abbrev Rel (a: Type) := a -> a -> Prop

-- | Paths (as discussed in lecture)
inductive Path {a: Type} (r: Rel a) : a -> a -> Prop where
  | refl : (x: a) -> Path r x x
  | step : (x y z: a) -> r x y -> Path r y z -> Path r x z

-- | paths-are-transitive (as discussed in lecture)
theorem Path_trans : ∀ {a: Type} {r: Rel a} {x y z: a},
  Path r x y -> Path r y z -> Path r x z := by
  intros a r x y z p1 p2
  induction p1
  case refl    => assumption
  case step ih => constructor
                  assumption
                  simp_all []


-- | Right-Paths ... are paths that are extended "on the right"
inductive RPath {a: Type} (r: Rel a) : a -> a -> Prop where
  | rrefl : (x: a) -> RPath r x x
  | rstep : (x y z: a) -> RPath r x y -> r y z -> RPath r x z

/- That is, there are two ways/rules to build a Right-Path `RPath`

  -------------- [rrefl]
    RPath r x x


    RPath r x y     r y z
  ------------------------- [rstep]
        RPath r x z

  That is, `rstep` lets you "extend" the path on the "right" side.

-/

-- | Prove that a single link makes a Path ---------------------------------------------------------

@[autogradedProof 10]
theorem step_is_path : ∀ {a: Type} {r: Rel a} {x y: a}, r x y -> Path r x y := by
  sorry

-- | Prove that a single link makes a Right-Path ---------------------------------------------

@[autogradedProof 10]
theorem rstep_is_path : ∀ {a: Type} {r: Rel a} {x y: a}, r x y -> RPath r x y := by
  sorry

-- | Prove that right-paths are transitive  --------------------------------------------------

@[autogradedProof 20]
theorem RPath_trans : ∀ {a: Type} {r: Rel a} { x y z: a }, RPath r x y -> RPath r y z -> RPath r x z := by
  sorry

-- | Prove that `Path` and `RPath` are "equivalent" ------------------------------------------

@[autogradedProof 15]
theorem RPath_Path : ∀ {a: Type} {r: Rel a} { x y: a }, Path r x y -> RPath r x y := by
  sorry

@[autogradedProof 15]
theorem Path_RPath : ∀ {a: Type} { r: Rel a } {x y: a}, RPath r x y -> Path r x y := by
  sorry


-------------------------------------------------------------------------------
-- | Q2 : Equivalence of evaluators
-------------------------------------------------------------------------------

inductive LvRel : State -> LExp -> Val -> Prop where
| lvRelN : ∀ {s: State} {n: Val},
              LvRel s (num n) n
| lvRelV : ∀ {s: State} {x: Vname},
              LvRel s (var x) (s x)
| lvRelP : ∀ {s: State} {e1 e2 : LExp} {n1 n2 : Val},
              LvRel s e1 n1 -> LvRel s e2 n2 ->
              LvRel s (plus e1 e2) (n1 + n2)
| lvRelL : ∀ {s: State} {x: Vname} {e1 e2: LExp} {n1 n2: Val},
              LvRel s e1 n1 -> LvRel (s [x := n1]) e2 n2 ->
              LvRel s (llet x e1 e2) n2

/- | Rules for Big-Step Evaluation of `LExp`ressions

    -------------------------- [lvRelN]
      LvRel s (num n) n


    --------------------------------- [lvRelV]
      LvRel s (var x) (s x)


        LvRel s e1 n1     LvRel s e2 n2
    --------------------------------------- [lvRelP]
      LvRel s (plus e1 e2) (n1 + n2)


      LvRel s e1 n1       LvRel (s [ x := n1 ] ) e2 n2
    -------------------------------------------------- [lvRelL]
      LvRel s (let x = e1 in e2) n2

-/

-- Prove the equivalence of `LvRel` and `lval` ---------------------------

@[autogradedProof 15]
theorem LvRel_lval: ∀ {s: State} {e: LExp} {n: Val}, LvRel s e n -> lval e s = n := by
  sorry


-- HINT: use induction ... generalizing

@[autogradedProof 25]
theorem lval_LvRel: ∀ {s: State} {e: LExp} {n: Val}, lval e s = n -> LvRel s e n := by
  sorry
