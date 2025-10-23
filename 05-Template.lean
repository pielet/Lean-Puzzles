import AutograderLib
set_option pp.fieldNotation false

/- --------------------------------------------------------------------------------------------
# Simply Typed λ-Calculus

Based on Jeremy Siek's: http://siek.blogspot.com/2013/05/type-safety-in-three-easy-lemmas.html
----------------------------------------------------------------------------------------------- -/

/- @@@
## Syntax
Lets define the syntax of types, terms and values
@@@ -/

/- --------------------------------------------------------------------------------------------
### Types
------------------------------------------------------------------------------------------- -/

inductive Ty where
  | TInt  : Ty
  | TBool : Ty
  | TFun  : Ty -> Ty -> Ty
  deriving Repr
open Ty

/- -----------------------------------------------------------------------------------------
### Terms
------------------------------------------------------------------------------------------ -/

abbrev Vname := String

inductive Op where
  | Add   : Op
  | Equal : Op
  deriving Repr
open Op

inductive Exp where
  | ENum : Int -> Exp
  | EBool: Bool -> Exp
  | EVar : Vname -> Exp
  | EOp  : Op -> Exp -> Exp -> Exp
  | ELam : Vname -> Ty -> Exp -> Exp
  | EApp : Exp -> Exp -> Exp
  | EIf  : Exp -> Exp -> Exp -> Exp
  deriving Repr
open Exp

-- Examples

def eInc := ELam "x" TInt (EOp Add (EVar "x") (ENum 1))

def eChoose := ELam "b" TBool (ELam "x" TInt (ELam "y" TInt (
                EIf (EVar "b")
                  (EOp Add (EVar "x") (ENum 1))
                  (EOp Add (EVar "y") (ENum 1))
              )))

def testIf a b := EApp (EApp (EApp eChoose (EOp Equal (ENum a) (ENum b))) (ENum 100)) (ENum 200)

/- --------------------------------------------------------------------------------------------
## Dynamic Semantics (Interpreter)

Extend the `eval` to work for `EIf` expressions
so `testIf0` and `testIf1` automatically verify.
-------------------------------------------------------------------------------------------- -/

/- @@@
### Results
@@@ -/

inductive Result (α : Type) : Type where
  | Ok      : α -> Result α
  | Stuck   : Result α
  | Timeout : Result α
  deriving Repr

open Result

/- @@@
### Values
@@@ -/

inductive Val where
  | VInt   : Int -> Val
  | VBool  : Bool -> Val
  | VClos  : Vname -> Ty -> Exp -> (Vname -> Val) -> Val

open Val

/- @@@
### Stores
@@@ -/

abbrev Store := Vname -> Val

@[simp]
def upd (s: Vname -> α ) (x: Vname) (v: α ) : Vname -> α :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

/- @@@
### Evaluator
@@@ -/

def combine (r1 : Result Val) (r2 : Result Val) (k : Val -> Val -> Result Val) : Result Val :=
  match r1 with
  | Ok v1 =>
    match r2 with
    | Ok v2 => k v1 v2
    | _ => r2
  | _ => r1

def op_add (v1 : Val) (v2 : Val) : Result Val :=
  match v1, v2 with
  | VInt n1, VInt n2 => Ok (VInt (n1 + n2))
  | _, _ => Stuck

def op_equal (v1 : Val) (v2 : Val) : Result Val :=
  match v1, v2 with
  | VInt n1, VInt n2 => Ok (VBool (n1 == n2))
  | VBool b1, VBool b2 => Ok (VBool (b1 == b2))
  | _, _ => Stuck

def eval_op (o : Op) : Val -> Val -> Result Val :=
  match o with
  | Op.Add   => op_add
  | Op.Equal => op_equal

-- **Problem 1** Complete the implementation of `eval`
-- when you are done, `testIf0` and `testIf1`
-- should automatically verify.

def eval (k : Nat) (ρ : Store) (e : Exp) : Result Val :=
  match k with
  | 0 => Timeout
  | k + 1 =>
    match e with
    | ENum n      => Ok (VInt n)
    | EBool b     => Ok (VBool b)
    | EVar x      => Ok (ρ x)
    | EOp o e1 e2 => combine (eval k ρ e1) (eval k ρ e2) (eval_op o)
    | ELam x τ e  => Ok (VClos x τ e ρ)
    | EApp e1 e2  => combine  (eval k ρ e1) (eval k ρ e2) (fun v1 v2 =>
                       match v1 with
                       | VClos x _ e ρ' => eval k (ρ' [ x := v2 ]) e
                       | _ => Stuck
                     )
    | EIf b e1 e2 => sorry


/- @@@
### Tests!
@@@ -/

def st0 : Store := λ _ => VInt 0
theorem testInc : eval 100 st0 (EApp eInc ( EOp Add (ENum 1) (ENum 2))) = Ok (VInt 4) := rfl

@[autogradedProof 10]
theorem testIf0 : eval 100000 st0 (testIf 1 2) = Ok (VInt 201) := rfl

@[autogradedProof 10]
theorem testIf1 : eval 100000 st0 (testIf 2 2) = Ok (VInt 101) := rfl

/- --------------------------------------------------------------------------------------------
## Static Semantics aka Type Checking
-------------------------------------------------------------------------------------------- -/

def ty_op (o: Op) (τ1 τ2: Ty) : Option Ty :=
  match (o, τ1, τ2) with
  | (Op.Add, TInt, TInt)     => some TInt
  | (Op.Equal, TInt, TInt)   => some TBool
  | (Op.Equal, TBool, TBool) => some TBool
  | _                        => none

/- --------------------------------------------------------------------------------------------
### Type Environments
-------------------------------------------------------------------------------------------- -/

abbrev Env := Vname -> Ty

-- An environment mapping all variables to `Int`
def Γ₀ :Env := fun _ => TInt

/- --------------------------------------------------------------------------------------------
### Well-Typed Expressions
-------------------------------------------------------------------------------------------- -/

-- **Problem 2** Add rules for type checking `EIf` so that when you are done,
-- `tyInc` and `tyChoose` automatically verify.

inductive WT : Env -> Exp -> Ty -> Prop where
  | TNum   : ∀ {n},
             WT Γ (ENum n) TInt

  | TBool  : ∀ {b},
             WT Γ (EBool b) TBool

  | TVar   : ∀ {x},
             WT Γ (EVar x) (Γ x)

  | TOp    : ∀ {o e1 e2 τ1 τ2},
             WT Γ e1 τ1 -> WT Γ e2 τ2 -> ty_op o τ1 τ2 = some τ ->
             WT Γ (EOp o e1 e2) τ

  | TLam   : ∀ {x τ e},
             WT (Γ[ x := τ ]) e τ' ->
             WT Γ (ELam x τ e) (TFun τ τ')

  | TApp   : ∀ {e1 e2 τ τ'},
             WT Γ e1 (TFun τ τ') -> WT Γ e2 τ ->
             WT Γ (EApp e1 e2) τ'


notation:10 Γ "⊢" e ":" t => WT Γ e t

theorem tyInc : Γ₀ ⊢ eInc : TFun TInt TInt
  := by repeat constructor

@[autogradedProof 10]
theorem tyChoose : Γ₀ ⊢ eChoose : TFun TBool (TFun TInt (TFun TInt TInt))
  := by repeat constructor


/- --------------------------------------------------------------------------------------------
## Type Soundness

Aka _Well-typed Expressions don't get stuck_.

**EC** You may need to extend `WV` to handle the new `Val` you introduced for `ERec` above.
-------------------------------------------------------------------------------------------- -/

/- @@@
### Well-Typed Values
@@@ -/


inductive WV : Val -> Ty -> Prop where

  | TVInt   : WV (VInt _) TInt

  | TVBool  : WV (VBool _) TBool

  | TVClos  : (∀ x, WV (ρ x) (Γ x)) -> WT (Γ [ x := τ ]) e τ' ->
              WV (VClos x τ e ρ) (TFun τ τ')


notation:10 "⊢" v ":" t => WV v t

/- @@@
### Well-Typed Results
@@@ -/

inductive WR : Result Val -> Ty -> Prop where

  | TOk      : ∀ {v τ},
               (⊢ v : τ) ->
               WR (Ok v) τ

  | TTimeout : WR Timeout τ

notation:10 "⊢" r ":" t => WR r t

/- @@@
### Well-Typed Stores
@@@ -/

abbrev WS (Γ : Env) (ρ : Store) := ∀ x, (⊢ ρ x : Γ x)

notation:10 Γ "⊢" ρ  => WS Γ ρ

@[simp]
theorem int_val : ∀ {v: Val}, (⊢ v : TInt) <-> (∃ i, v = VInt i)
  := by
  intros v
  apply Iff.intro
  . case mp => intros wv; cases wv; rename_i i; apply Exists.intro; trivial
  . case mpr => intro h ; cases h ; simp_all []; constructor

@[simp]
theorem bool_val : ∀ {v: Val}, (⊢ v : TBool) <-> (∃ b, v = VBool b)
  := by
  intros v
  apply Iff.intro
  . case mp => intros wv; cases wv; rename_i i; apply Exists.intro; trivial
  . case mpr => intro h ; cases h ; simp_all []; constructor

-- **Problem 3** Complete the proof of `op_safe` ------------------------------------

@[autogradedProof 30]
theorem op_safe: ∀ {v1 v2 : Val} {o τ1 τ2},
  (⊢ v1 : τ1) -> (⊢ v2 : τ2) -> some τ = ty_op o τ1 τ2 ->
  ∃ v, eval_op o v1 v2 = Ok v ∧ WV v τ
  := by
  sorry


-- **Problem 4** Complete the proof of `op_safe` ------------------------------------

@[autogradedProof 20]
theorem op_safe_r : ∀ {r1 r2 : Result Val} {τ1 τ2 o},
  (⊢ r1 : τ1) -> (⊢ r2 : τ2) -> some τ = ty_op o τ1 τ2 ->
  (⊢ combine r1 r2 (eval_op o) : τ)
  := by
  sorry

-- lemma 2
theorem lookup_safe : ∀ {Γ ρ x},
  (Γ ⊢ ρ) -> (⊢ ρ x : Γ x)
  := by
  intro Γ ρ x h_ws
  apply h_ws x

theorem ws_upd : ∀ {Γ ρ x τ} {v: Val},
  (Γ ⊢ ρ) -> (⊢ v : τ) -> (Γ [ x := τ ] ⊢ ρ [ x := v ])
  := by
  intros Γ ρ x τ v ws wv
  intro y
  by_cases (y = x) <;> simp_all [upd]

theorem wr_val : ∀ { r τ },
  ¬ (r = Timeout) -> (⊢ r : τ) ->  ∃ v, r = Ok v /\ WV v τ
  := by
  intro r τ not_timeout wr
  cases wr
  . case TOk => apply Exists.intro; trivial
  . case TTimeout => trivial

-- **Problem 5** Complete the proof of `eval_safe` (lemma 3) ------------------------------------

@[autogradedProof 50]
theorem eval_safe: ∀ {Γ e τ ρ k },
  (Γ ⊢ e : τ) -> (Γ ⊢ ρ) -> (⊢ eval k ρ e : τ)
  := by
  sorry

/- @@@ --------------------------------------------------------------------------------------------
## A Type Checker
-------------------------------------------------------------------------------------------- @@@ -/

@[simp] def eqTy (t1 t2: Ty) : Bool :=
  match t1, t2 with
  | TInt, TInt => true
  | TBool, TBool => true
  | TFun t1 t1', TFun t2 t2' => eqTy t1 t2 && eqTy t1' t2'
  | _, _ => false

@[simp] theorem eqTy_eq : ∀ {t1 t2},
  eqTy t1 t2 <-> t1 = t2
  := by
  intros t1 t2; constructor
  . case mp =>
    intros eqTy
    induction t1 generalizing t2 <;> cases t2 <;> simp_all [eqTy]
    rename_i t1 t1' ih1 ih2 t2 t2'
    cases eqTy
    constructor
    apply ih1; trivial
    apply ih2; trivial
  . case mpr =>
    induction t1 generalizing t2 <;> cases t2 <;> simp_all [eqTy]
    rename_i t1 t1' t2 t2' ih ih'
    intros
    simp_all

-- **Problem 6** Complete the definition of `check` so that when you are done
-- `checkInc`, `checkChoose` automatically verify.

@[simp] def check (Γ : Env) (e : Exp) : Option Ty :=
  sorry


@[autogradedProof 10]
theorem checkInc : check Γ₀ eInc = some (TFun TInt TInt) := rfl

@[autogradedProof 10]
theorem checkChoose : check Γ₀ eChoose = some (TFun TBool (TFun TInt (TFun TInt TInt))) := rfl


-- **Problem 7** Complete the proof of `checkOp_sound`

@[autogradedProof 20]
theorem checkOp_sound: ∀ { Γ o e1 e2 t1 t2 t},
  (Γ ⊢ e1 : t1) -> (Γ ⊢ e2 : t2) -> some t = ty_op o t1 t2 -> (Γ ⊢ EOp o e1 e2 : t)
  := by
  sorry

-- **Problem 7** Complete the proof of `check_sound`

@[autogradedProof 20]
theorem check_sound : ∀ { Γ e t },
  some t = check Γ e -> ( Γ ⊢ e : t )
  := by
  sorry
