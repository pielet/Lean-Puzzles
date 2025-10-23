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

--------------------------------------------------------------------------------
-- | Arithmetic Expressions
--------------------------------------------------------------------------------

instance : OfNat Val n where
  ofNat := n

inductive AExp where
| num  : Val -> AExp
| var  : Vname -> AExp
| plus : AExp -> AExp -> AExp
deriving Repr

def aval (e: AExp) (s: State) : Val :=
  match e with
  | AExp.num n => n
  | AExp.var x => s x
  | AExp.plus e1 e2 => aval e1 s + aval e2 s


/- -----------------------------------------------------------------------------------------------------------
   Q1: Prove `asimp_const` folds *all* subexpressions of the form `AExp.plus (AExp.num i) (AExp.num j)`.
   ---------------------------------------------------------------------------------------------------------- -/

-- | `is_opt` defines whether an expression is indeed is_opt, i.e. has no `i + j` sub-terms.
def is_opt (e: AExp) : Bool :=
  match e with
  | AExp.num _ => true
  | AExp.var _ => true
  | AExp.plus (AExp.num _) (AExp.num _) => false
  | AExp.plus e1 e2 => is_opt e1 && is_opt e2

def asimp_const (e: AExp) : AExp :=
  match e with
  | AExp.num e => AExp.num e
  | AExp.var e => AExp.var e
  | AExp.plus e1 e2 =>
    match (asimp_const e1), (asimp_const e2) with
    | AExp.num n1, AExp.num n2 => AExp.num (n1 + n2)
    | e1, e2 => AExp.plus e1 e2

-- Complete the proof of lem_is_opt which states that `is_opt (asimp_const a)`
--@[autogradedProof 20]

/-
x✝ : ∀ (n1 n2 : Val), asimp_const a✝¹ = AExp.num n1 → ¬asimp_const a✝ = AExp.num n2
-/

theorem optimal_asimp_const : ∀ {a: AExp}, is_opt (asimp_const a) = true := by
  intros a
  induction a with
  | num n => simp [asimp_const, is_opt]
  | var x => simp [asimp_const, is_opt]
  | plus e1 e2 ih1 ih2 =>
    simp [asimp_const] <;> split <;> simp_all [is_opt]

/- -------------------------------------------------------------------------------
   Q2: Next we will do a more serious transformation where expressions like
          `(x + 2) + (y + 5)`
        are transformed into a "normal form" that looks like
          `x + (y + 7)`
        That is into a sum of variables plus with all the constants at the end.
-------------------------------------------------------------------------------- -/

-- an "optimized" form of `AExp` where the LHS of `plus` is always a `Var`
inductive AExpOpt where
  | num  : Val -> AExpOpt
  | plus : Vname -> AExpOpt -> AExpOpt

def aval_opt (a: AExpOpt) (s: State) : Val :=
  match a with
  | AExpOpt.num n => n
  | AExpOpt.plus x a' => s x + aval_opt a' s

-- a function that converts optimized expressions back to plain expresssions
def unopt (a: AExpOpt) : AExp :=
  match a with
  | AExpOpt.num n => AExp.num n
  | AExpOpt.plus x a' => AExp.plus (AExp.var x) (unopt a')

-- (a) Write a function that adds a constant to an optimized expression.
def aoplusn (n : Val) (a: AExpOpt) : AExpOpt :=
  match a with
  | AExpOpt.num n' => AExpOpt.num (n + n')
  | AExpOpt.plus x a' => AExpOpt.plus x (aoplusn n a')

-- (b) Next, write a function `aoplus` that adds two optimized expressions
def aoplus (a other: AExpOpt) : AExpOpt :=
  match a with
  | AExpOpt.num n1 => aoplusn n1 other
  | AExpOpt.plus x a' => AExpOpt.plus x (aoplus a' other)

-- (c) Write a function `asimp_opt` that converts plain expressions to optimized expressions.
def asimp_opt (a: AExp) : AExpOpt :=
  match a with
  | AExp.num n => AExpOpt.num n
  | AExp.var x => AExpOpt.plus x (AExpOpt.num 0)
  | AExp.plus e1 e2 => aoplus (asimp_opt e1) (asimp_opt e2)

theorem add_silly : ∀ {x y z : Val}, x + (y + z) = y + (x + z) := by
  intros x y z
  calc
    x + (y + z) = (x + y) + z := by simp [Nat.add_assoc]
    _           = (y + x) + z := by simp [Nat.add_comm]
    _           = y + (x + z) := by simp [Nat.add_assoc]

/- (d) Prove that the `asimp_opt` preserves the meaning of an expression.

   HINT: you may need to use `add_silly` , and prove helper lemmas about the
   relationship between
   (i) `aval_opt` and `aoplusn`,
   (ii) `aval_opt` and `aoplus`,

 -/

theorem aoplusn_helper : ∀ {n : Val} {a : AExpOpt} {s: State},
  aval_opt (aoplusn n a) s = n + aval_opt a s := by
  intros n a s
  induction a with
  | num n' => simp [aoplusn, aval_opt]
  | plus x a' ih => simp [aoplusn, aval_opt, ih, add_silly]

theorem aoplus_helper : ∀ {a1 a2 : AExpOpt} {s: State},
  aval_opt (aoplus a1 a2) s = aval_opt a1 s + aval_opt a2 s := by
  intros a1 a2 s
  induction a1 with
  | num n1 => simp [aoplus, aval_opt, aoplusn_helper]
  | plus x a' ih => simp [aval_opt, aoplus, ih, Nat.add_assoc]

  -- simp +arith [aoplus, aval_opt, ih, Nat.add_assoc]

-- @[autogradedProof 30]
theorem asimp_opt_aval : ∀ {a : AExp} {s: State},
  aval_opt (asimp_opt a) s = aval a s := by
  intros a s
  induction a with
  | num n => simp [asimp_opt, aval_opt, aval]
  | var x => simp [asimp_opt, aval_opt, aval]
  | plus e1 e2 ih1 ih2 =>
    simp [asimp_opt, aval, aoplus_helper, ih1, ih2]


-- @[autogradedProof 10]
theorem unopt_aval : ∀ {a : AExpOpt} {s: State},
  aval (unopt a) s = aval_opt a s := by
  intros a s
  induction a generalizing s with
  | num n => simp [unopt, aval_opt, aval]
  | plus x a' ih => simp [unopt, aval_opt, aval, ih]

-- We can now define the "full simplification" function as
def asimp_full (a : AExp) : AExp := unopt (asimp_opt a)

-- (f) Prove that `asimp_full` yields an expression that
--     is equivalent to the original expression. You should
--     not need any induction, just use the previous lemmas...

-- @[autogradedProof 10]
theorem asimp_full_aval : ∀ {a : AExp} {s: State},
  aval (asimp_full a) s = aval a s := by
  intros a s
  simp [asimp_full, unopt_aval, asimp_opt_aval]


/- -------------------------------------------------------------------------------
   Q3:  Substitution `subst x a e` replaces all occurrences of variable `x` by
        an expression `a` in an expression `e`
   ------------------------------------------------------------------------------- -/

def subst (x: Vname) (a e: AExp) : AExp :=
  match e with
  | AExp.var y => if x == y then a else AExp.var y
  | AExp.num n => AExp.num n
  | AExp.plus e1 e2 => AExp.plus (subst x a e1) (subst x a e2)

/- --------------------------------------------------------------------------
   Prove the so-called "substitution lemma" that says that we can
   either substitute first and evaluate afterwards or evaluate with
   an updated state.
   HINT: Understand what `split` is doing in the `split_example` shown below.
   -------------------------------------------------------------------------- -/

def asgn (x: Vname) (a: AExp) (s: State) : State := upd s x (aval a s)

-- @[autogradedProof 20]
theorem subst_lemma : ∀ {x: Vname} {a e: AExp} {s: State},
  aval (subst x a e) s = aval e (asgn x a s) := by
  intros x a e s
  induction e generalizing s with
  | var y => simp [subst] <;> split <;> simp_all [asgn, aval, upd]
  | num n => simp [subst, aval]
  | plus e1 e2 ih1 ih2 => simp_all [subst, aval]


-- HINT: when you get to the `if` you may want to use the `split` tactic as illustrated below.

def foo(x: Nat) : Nat := if x == 42 then x else 10

theorem split_example: ∀n, foo n > 0 := by
  intros n
  simp [foo]
  split <;> simp_all []


/- -----------------------------------------------------------------------------
   Q4: Let-binders: Consider the following expression language that
       extends AExp with let-bound variables, so you can write expressions

           let x = 10
               y = x + 5
           in  x + y

       which should evaluate to 25
-------------------------------------------------------------------------------- -/

inductive LExp where
| num  : Val   -> LExp
| var  : Vname -> LExp
| plus : LExp  -> LExp -> LExp
| llet : Vname -> LExp -> LExp -> LExp
deriving Repr

/- `lval l s` takes a let-bound expression and a State and returns the result
    of evaluating `l` in `s` -/

def lval (e: LExp) (s: State) : Val :=
  match e with
  | LExp.num n => n
  | LExp.var x => s x
  | LExp.plus e1 e2 => lval e1 s + lval e2 s
  | LExp.llet x e1 e2 => lval e2 (upd s x (lval e1 s)) -- let x = e1 in e2

-- Write a function `inlyne` that converts an `LExp` into a plain `AExp`
-- by "inlining" the let-definitions, i.e. `let x = e1 in e2` should become
-- e2-with-all-occurrences-x-replaced-by-e1

-- @[autogradedProof 15]
def inlyne (e: LExp) : AExp :=
  match e with
  | LExp.num n => AExp.num n
  | LExp.var x => AExp.var x
  | LExp.plus e1 e2 => AExp.plus (inlyne e1) (inlyne e2)
  | LExp.llet x e1 e2 => subst x (inlyne e1) (inlyne e2)

-- Prove that your `inlyne` function is correct; HINT: recall the `subst_lemma`
-- @[autogradedProof 30]
theorem inlyne_sound: ∀ {e : LExp} {s: State}, lval e s = aval (inlyne e) s := by
  intros e s
  induction e generalizing s with
  | num n => simp [inlyne, lval, aval]
  | var x => simp [inlyne, lval, aval]
  | plus e1 e2 ih1 ih2 => simp [inlyne, lval, aval, ih1, ih2]
  | llet x e1 e2 ih1 ih2 => simp_all [inlyne, lval, subst_lemma, asgn]

/- -----------------------------------------------------------------------------
   Q5: Palindromes
   ----------------------------------------------------------------------------- -/

inductive palindrome : List Nat -> Prop where
  | emp : palindrome []
  | sng : ∀ (n : Nat), palindrome [n]
  | cns : ∀ (n : Nat) (ns : List Nat), palindrome ns -> palindrome (n :: ns ++ [n])

-- @[autogradedProof 10]
theorem palindrome_rev : ∀ (ns : List Nat), (palindrome ns) -> List.reverse ns = ns := by
  intros ns pal
  induction pal with
  | emp => rfl
  | sng n => rfl
  | cns n ns' pal' ih => simp_all []

/- -----------------------------------------------------------------------------
   Q6: Even numbers revisited
   ----------------------------------------------------------------------------- -/

-- Recall the inductive proposition that characterized even numbers from lecture.
inductive Ev : Nat -> Prop where
  | evz  : Ev 0
  | evss :  ∀ {n : Nat}, Ev n -> Ev ((n + 1) + 1)

theorem another_add_silly : ∀ {k : Nat}, k + 1 + (k + 1) = ((k + k) + 1 ) + 1 := by
  intros k; simp +arith []

theorem double_ev : ∀ {n : Nat}, (∃ k, n = k + k) -> Ev n := by
  intros n double
  cases double with | intro k n_eq_2k =>
    induction k generalizing n
    . case zero => simp_all []; constructor
    . case succ k ih => simp_all [another_add_silly]; apply Ev.evss; assumption

-- Complete the proof following proof that every `Ev n` is the double of some other `Nat`.
-- HINT: Use the `cases` tactic (as shown above), and the `exists` tactic

-- @[autogradedProof 15]
theorem ev_double : ∀ {n : Nat}, Ev n -> ∃ k, n = k + k := by
  intros n ev
  induction ev with
  | evz => exists 0
  | evss ev' ih =>
    cases ih with | intro k n_eq_2k => exists (k + 1); simp_all [another_add_silly]

/- -----------------------------------------------------------------------------
   Q7: Iteration
   ----------------------------------------------------------------------------- -/

-- Recall the definition of `star` from lecture
inductive star {α : Type} (r: α -> α -> Prop) : α -> α -> Prop where
  | refl : ∀ {a : α}, star r a a
  | step : ∀ {a b c : α}, r a b -> star r b c -> star r a c

-- Here is a variation called `iter` which "counts" the number of `r` steps
inductive iter {α : Type} (r : α -> α -> Prop) : Nat -> α -> α -> Prop where
  | iter_base : ∀ {a : α}, iter r 0 a a
  | iter_step : ∀ {n : Nat} {a b c : α}, r a b -> iter r n b c -> iter r (n + 1) a c

-- Prove that if `star r a b` then there exists n, such that `iter n r a b`
-- HINT: Use the `exists` tactic to let you supply the existential value.

-- @[autogradedProof 15]
theorem star_iter : ∀ {α : Type} {r : α -> α -> Prop} {a b : α},
  star r a b -> ∃ (n : Nat), iter r n a b := by
  intros α r a b star_ab
  induction star_ab with
  | refl => exists 0; apply iter.iter_base
  | step r' _ ih =>
    cases ih with | intro n iter_r'_n_a_b =>
      exists (n + 1)
      apply iter.iter_step
      assumption
      assumption
