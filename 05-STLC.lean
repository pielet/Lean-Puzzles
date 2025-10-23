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
  | ENum : Int -> Exp                     -- 0, 1, 2, 3 ...
  | EBool: Bool -> Exp                    -- true, false
  | EVar : Vname -> Exp                   -- x, y, z ...
  | EOp  : Op -> Exp -> Exp -> Exp        -- e1 ⊗ e2
  | ELam : Vname -> Ty -> Exp -> Exp      -- λ x : τ => e
  | EApp : Exp -> Exp -> Exp              -- e1 e2
  | EIf  : Exp -> Exp -> Exp -> Exp       -- if b then e1 else e2
  | ERec : Vname -> Vname -> Ty -> Ty -> Exp -> Exp
                                          -- rec succ (x : int) : int = (if x = 0 then 0 else x + 1)
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

/- **EC** The `ERec f x t t' e` lets us define **recursive functions**
    - named `f`
    - that take a parameter `x` of input type `t`
    - and return an output of type `t'`
    - returned via the body `e`

    For example, see the `eSum` defined below
-/

def eSum := ERec "sum" "n" TInt TInt
              (EIf (EOp Op.Equal (EVar "n") (ENum 0))
                (ENum 0)
                (EOp Op.Add (EVar "n") (EApp (EVar "sum") (EOp Op.Add (EVar "n") (ENum (-1)))))
              )

/- --------------------------------------------------------------------------------------------
## Dynamic Semantics (Interpreter)

Extend the `eval` to work for `EIf` expressions (and `ERec` for **EC**);
so `testIf0` and `testIf1` (and `testSum` for **EC**) automatically verify.

For **EC**, you may need to extend the type `Val` to include a special value
that represents `ERec` (recursive) functions.
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
  | VRec   : Vname -> Vname -> Ty -> Ty -> Exp -> (Vname -> Val) -> Val
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
-- when you are done, `testIf0` and `testIf1` (and `testSum` for **EC**)
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
    | EApp e1 e2  => combine (eval k ρ e1) (eval k ρ e2) (fun v1 v2 =>
                       match v1 with
                       | VClos x _ e ρ' => eval k (ρ' [ x := v2 ]) e
                       | VRec f x _ _ e ρ' => eval k (ρ' [ x := v2 ][ f := v1 ]) e
                       | _ => Stuck
                     )
    | EIf b e1 e2 => match eval k ρ b with
                       | Ok (VBool true)  => eval k ρ e1
                       | Ok (VBool false) => eval k ρ e2
                       | Timeout => Timeout
                       | _ => Stuck
    | ERec f x τ τ' e => Ok (VRec f x τ τ' e ρ)

/- @@@
### Tests!
@@@ -/

def st0 : Store := λ _ => VInt 0
theorem testInc : eval 100 st0 (EApp eInc ( EOp Add (ENum 1) (ENum 2))) = Ok (VInt 4) := rfl

-- @[autogradedProof 10]
theorem testIf0 : eval 100000 st0 (testIf 1 2) = Ok (VInt 201) := rfl

-- @[autogradedProof 10]
theorem testIf1 : eval 100000 st0 (testIf 2 2) = Ok (VInt 101) := rfl

-- **EC**
-- @[autogradedProof 10]
theorem testSum : eval 1000 st0 (EApp eSum (ENum 10)) = Ok (VInt 55) := rfl

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

-- **Problem 2** Add rules for type checking `EIf` (and `ERec` for **EC**) so that when you are done,
-- `tyInc` and `tyChoose` (and `tySum for EC) automatically verify.

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

  | TIf    : ∀ {b e1 e2 τ},
             WT Γ b TBool -> WT Γ e1 τ -> WT Γ e2 τ ->
             WT Γ (EIf b e1 e2) τ

  | TRec   : ∀ {f x τ τ' e},
              WT (Γ [ x := τ ] [ f := TFun τ τ' ]) e τ' ->
              WT Γ (ERec f x τ τ' e) (TFun τ τ')


notation:10 Γ "⊢" e ":" t => WT Γ e t

theorem tyInc : Γ₀ ⊢ eInc : TFun TInt TInt
  := by repeat constructor

-- @[autogradedProof 10]
theorem tyChoose : Γ₀ ⊢ eChoose : TFun TBool (TFun TInt (TFun TInt TInt))
  := by repeat constructor

-- **EC**

-- @[autogradedProof 10]
theorem tySum : Γ₀ ⊢ eSum : TFun TInt TInt
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

  | TVRec   : (∀ x, WV (ρ x) (Γ x)) -> WT (Γ [ x := τ ] [ f := TFun τ τ' ]) e τ' ->
              WV (VRec f x τ τ' e ρ) (TFun τ τ')

  -- **EC** you may need to add cases for the extra `Val` cases defined above.

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

-- @[simp]
theorem int_val : ∀ {v: Val}, (⊢ v : TInt) <-> (∃ i, v = VInt i)
  := by
  intros v
  apply Iff.intro
  . case mp => intros wv; cases wv; rename_i i; apply Exists.intro; trivial
  . case mpr => intro h ; cases h ; simp_all []; constructor

-- @[simp]
theorem bool_val : ∀ {v: Val}, (⊢ v : TBool) <-> (∃ b, v = VBool b)
  := by
  intros v
  apply Iff.intro
  . case mp => intros wv; cases wv; rename_i i; apply Exists.intro; trivial
  . case mpr => intro h ; cases h ; simp_all []; constructor

-- **Problem 3** Complete the proof of `op_safe` ------------------------------------

-- @[autogradedProof 30]
theorem op_safe: ∀ {v1 v2 : Val} {o τ1 τ2},
  (⊢ v1 : τ1) -> (⊢ v2 : τ2) -> some τ = ty_op o τ1 τ2 ->
  ∃ v, eval_op o v1 v2 = Ok v ∧ WV v τ
  := by
  intros v1 v2 o τ1 τ2 wv1 wv2 h_ty_op
  cases o
  . case Add =>
    have τi_t : τ1 = TInt ∧ τ2 = TInt := by
      constructor <;> cases τ1 <;> cases τ2 <;> simp_all [ty_op]
    have τ_t : τ = TInt := by
      cases τi_t; simp_all [ty_op]
    simp_all
    cases wv1; cases wv2
    simp_all [eval_op, op_add]
    constructor
  · case Equal =>
    have τi_int : τ1 = TInt -> τ2 = TInt := by
      intro τ1_int; cases τ2 <;> simp_all [ty_op]
    have τi_bool : τ1 = TBool -> τ2 = TBool := by
      intro τ1_bool; cases τ2 <;> simp_all [ty_op]
    cases τ1 <;> cases τ2 <;> simp_all [ty_op] <;>
    cases wv1 <;> cases wv2 <;>
    simp_all [eval_op, op_equal] <;>
    constructor


-- **Problem 4** Complete the proof of `op_safe` ------------------------------------

-- @[autogradedProof 20]
theorem op_safe_r : ∀ {r1 r2 : Result Val} {τ1 τ2 o},
  (⊢ r1 : τ1) -> (⊢ r2 : τ2) -> some τ = ty_op o τ1 τ2 ->
  (⊢ combine r1 r2 (eval_op o) : τ)
  := by
  intros r1 r2 τ1 τ2 o wr1 wr2 h_ty_op
  cases r1 <;> cases r2 <;> cases wr1 <;> cases wr2 <;> simp_all [combine]
  . case Ok.Ok v1 v2 _ _ =>
    obtain ⟨ v, eval_op_v ⟩ : ∃ v, eval_op o v1 v2 = Ok v ∧ (⊢ v : τ) := by apply op_safe <;> assumption
    cases eval_op_v
    simp_all
    constructor
    assumption
  repeat constructor

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

-- @[autogradedProof 50]
theorem eval_safe: ∀ {Γ e τ ρ k },
  (Γ ⊢ e : τ) -> (Γ ⊢ ρ) -> (⊢ eval k ρ e : τ)
  := by
  intros Γ e τ ρ k h_wt h_ws
  induction k, ρ, e using eval.induct generalizing Γ τ
  . case case1 => simp_all [eval]; constructor  -- k = 0
  . case case2 => cases h_wt; simp_all [eval]; repeat constructor  -- num
  . case case3 => cases h_wt; simp_all [eval]; repeat constructor  -- bool
  . case case4 => cases h_wt; simp_all [eval]; constructor; simp_all  -- var
  . case case5 ih1 ih2 =>  -- op
    cases h_wt
    simp_all [eval]; apply op_safe_r
    apply ih1; repeat assumption
    apply ih2; repeat assumption
    simp_all []
  . case case6 =>  -- lam
    cases h_wt
    simp_all [eval]
    repeat constructor
    repeat assumption
  . case case7 ρ k e1 e2 ih1 ih2 ih3 ih4 =>  -- app
    cases k
    . case zero => simp_all [eval, combine]; constructor
    . case succ k' =>
      cases h_wt
      rename_i τ' wt2 wt1
      have eval_v1 : ¬ (eval (k' + 1) ρ e1 = Timeout) -> ∃ v1, eval (k' + 1) ρ e1 = Ok v1 ∧ (⊢ v1 : TFun τ' τ) := by
        intros; apply wr_val; assumption; apply ih1; repeat assumption
      have eval_v2 : ¬ (eval (k' + 1) ρ e2 = Timeout) -> ∃ v2, eval (k' + 1) ρ e2 = Ok v2 ∧ (⊢ v2 : τ') := by
        intros; apply wr_val; assumption; apply ih2; repeat assumption
      cases r1 : eval (k' + 1) ρ e1 <;> cases r2 : eval (k' + 1) ρ e2 <;> simp_all
      . case TApp.Ok.Ok v1 v2 =>
        cases eval_v1 <;> simp_all [eval.eq_7, combine]
        . case TVClos =>
          apply ih3
          assumption
          apply ws_upd
          repeat assumption
        . case TVRec =>
          apply ih4
          assumption
          apply ws_upd
          apply ws_upd
          assumption
          assumption
          constructor
          assumption
          assumption
      . case TApp.Ok.Timeout =>
        cases eval_v1 <;> simp_all [eval.eq_7, combine] <;> constructor
      . case TApp.Timeout.Ok =>
        simp_all [eval.eq_7, combine]
        constructor
      . case TApp.Timeout.Timeout =>
        simp_all [eval.eq_7, combine]
        constructor
  . case case8 ih =>  -- if true
    cases h_wt
    simp_all [eval]
    apply ih
    repeat assumption
  . case case9 ih => -- if false
    cases h_wt
    simp_all [eval]
    apply ih
    assumption
    assumption
  . case case10 => simp_all [eval]; constructor
  . case case11 ρ k b e1 e2 b_true b_false not_timeout ih =>
    cases h_wt
    rename_i wtb wt1 wt2
    obtain ⟨ bv, eval_b ⟩ : ∃ bv, eval k ρ b = Ok bv ∧ (⊢ bv : TBool) := by
      intros; apply wr_val; assumption; apply ih; repeat assumption
    cases eval_b
    rename_i eval_b bv_t
    rw [bool_val] at bv_t
    simp_all
  . case case12 ρ k f x τ' τ'' e =>
    cases h_wt
    simp_all [eval]
    repeat constructor
    repeat assumption


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
    induction t1 generalizing t2 <;> cases t2 <;> simp_all []
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
-- `checkInc`, `checkChoose` (and for EC `checkSum`) automatically verify.

@[simp] def check (Γ : Env) (e : Exp) : Option Ty :=
  match e with
  | ENum _      => some TInt
  | EBool _     => some TBool
  | EVar x      => some (Γ x)
  | EOp o e1 e2 => do
      match check Γ e1 with
      | some τ1 =>
        match check Γ e2 with
        | some τ2 => ty_op o τ1 τ2
        | _ => none
      | _ => none
  | ELam x τ e  =>
      match check (Γ [ x := τ ]) e with
      | some τ' => some (TFun τ τ')
      | none => none
  | EApp e1 e2  =>
      match check Γ e1, check Γ e2 with
      | some (TFun τ' τ''), some τ =>
          if eqTy τ' τ then some τ'' else none
      | _, _ => none
  | EIf b e1 e2 =>
      match check Γ b with
      | some TBool =>
        match check Γ e1, check Γ e2 with
        | some τ1, some τ2 =>
            if eqTy τ1 τ2 then some τ1 else none
        | _, _ => none
      | _ => none
  | ERec f x τ τ' e =>
      match check (Γ [ x := τ ] [ f := TFun τ τ' ]) e with
      | some τ'' => if eqTy τ' τ'' then some (TFun τ τ') else none
      | _ => none


-- @[autogradedProof 10]
theorem checkInc : check Γ₀ eInc = some (TFun TInt TInt) := rfl

-- @[autogradedProof 10]
theorem checkChoose : check Γ₀ eChoose = some (TFun TBool (TFun TInt (TFun TInt TInt))) := rfl

-- @[autogradedProof 10]
theorem checkSum : check Γ₀ eSum = some (TFun TInt TInt) := rfl


-- **Problem 7** Complete the proof of `checkOp_sound`

-- @[autogradedProof 20]
theorem checkOp_sound: ∀ { Γ o e1 e2 t1 t2 t},
  (Γ ⊢ e1 : t1) -> (Γ ⊢ e2 : t2) -> some t = ty_op o t1 t2 -> (Γ ⊢ EOp o e1 e2 : t)
  := by
  intros Γ o e1 e2 t1 t2 t h_wt1 h_wt2 h_ty_op
  constructor
  assumption
  assumption
  simp_all

-- **Problem 7** Complete the proof of `check_sound`

-- @[autogradedProof 20]
theorem check_sound : ∀ { Γ e t },
  some t = check Γ e -> ( Γ ⊢ e : t )
  := by
  intros Γ e t h_check
  induction Γ, e using check.induct generalizing t
  . case case1 => simp_all; constructor
  . case case2 => simp_all; constructor
  . case case3 => simp_all; constructor
  . case case4 ih1 ih2 => simp_all; constructor; assumption; assumption; simp_all
  . case case5 => simp_all
  . case case6 => simp_all
  . case case7 ih => simp_all; constructor; assumption
  . case case8 => simp_all
  . case case9 ih1 ih2 => simp_all; constructor; repeat assumption
  . case case10 => simp_all
  . case case11 => simp_all
  . case case12 => simp_all; constructor; repeat assumption
  . case case13 => simp_all
  . case case14 => simp_all
  . case case15 => simp_all
  . case case16 r_check _ ih =>  rw [r_check] at ih; simp_all; constructor; assumption
  . case case17 => simp_all
  . case case18 => simp_all
