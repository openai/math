import OAI.Computability.VPVNP.RAMTapeWordMul
import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# Binary powers for the live bucket exponent

The fixed numerator of the rational exponent is a finite loop bound.
Each iteration copies the base, calls the word multiplier, and restores
the product to its input port for the next call. The word width is supplied
by the stacks and is independent of the number of control states.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputPower

open TapeWord BurstRAM

/-- Ports for the power routine’s base, temporary reversal, and multiplication registers. -/
inductive Port
  | base | tmp | mul (r : Mul.Reg)
  deriving DecidableEq, Fintype

/-- Phases of one power round, from copying the base through multiplication to moving the
product into the next accumulator. -/
inductive Round
  | test | copy | save (b : Bool) | restore | baseBit (b : Bool) | factorBit (b : Bool)
  | mul (s : Mul.State) | reverseProduct | saveProduct (b : Bool)
  | restoreProduct | putProduct (b : Bool)
  deriving DecidableEq, Fintype

/-- Power control carrying a bounded number of remaining rounds and the current multiplication
phase. -/
inductive State (p : ℕ)
  | round (i : Fin (p+1)) (s : Round)
  | done
  deriving DecidableEq, Fintype

/-- Repeat multiplication by a restored copy of the base and transfer each product to the
accumulator for the next round. -/
def code (p : ℕ) : StackCode Port (State p)
  | .done => .halt true
  | .round i s => match s with
    | .test => if i.val = 0 then .goto .done else .goto (.round i .copy)
    | .copy => .pop .base fun b => .round i (b.elim .restore .save)
    | .save b => .push .tmp b (.round i .copy)
    | .restore => .pop .tmp fun b => .round i (b.elim (.mul .init) .baseBit)
    | .baseBit b => .push .base b (.round i (.factorBit b))
    | .factorBit b => .push (.mul .multiplicand) b (.round i .restore)
    | .mul .done => .goto (.round i .reverseProduct)
    | .mul s => (Mul.code s).rename Port.mul (fun q => .round i (.mul q))
    | .reverseProduct => .pop (.mul .accumulator) fun b => .round i (b.elim .restoreProduct .saveProduct)
    | .saveProduct b => .push .tmp b (.round i .reverseProduct)
    | .restoreProduct => .pop .tmp fun b => b.elim
        (.round ⟨i.val - 1, by omega⟩ .test) (fun v => .round i (.putProduct v))
    | .putProduct b => .push (.mul .multiplier) b (.round i .restoreProduct)

/-- Initialize the base and temporary stack together with the accumulator, factor, and product
of the embedded multiplier. -/
def store (base tmp acc factor product : List Bool) : Stacks Port
  | .base => base
  | .tmp => tmp
  | .mul r => Mul.store acc factor product [] [] r

private theorem set_store (base tmp a f v l : List Bool) (k : Port) :
    Function.update (store base tmp a f v) k l = match k with
      | .base => store l tmp a f v
      | .tmp => store base l a f v
      | .mul .multiplier => store base tmp l f v
      | .mul .multiplicand => store base tmp a l v
      | .mul .accumulator => store base tmp a f l
      | .mul _ => Function.update (store base tmp a f v) k l := by
  cases k with
  | base | tmp => funext j; cases j <;> simp [store]
  | mul r =>
    cases r <;> first | rfl | (funext j; cases j with
      | base | tmp => simp [store]
      | mul u => cases u <;> simp [store, Mul.store])

local macro "power_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, Mul.store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, set_store])

variable {p : ℕ} (i : Fin (p+1))

private theorem copy_run (x t a : List Bool) :
    StackRuns (code p) (2 * x.length + 1) (.round i .copy) (store x t a [] [])
      (.round i .restore) (store [] (x.reverse ++ t) a [] []) := by
  induction x generalizing t with
  | nil => power_step; exact .nil ..
  | cons b x ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    power_step
    power_step
    exact ih (b :: t)

private theorem restore_run (x t a f : List Bool) :
    StackRuns (code p) (3 * t.length + 1) (.round i .restore) (store x t a f [])
      (.round i (.mul .init)) (store (t.reverse ++ x) [] a (t.reverse ++ f) []) := by
  induction t generalizing x f with
  | nil => power_step; exact .nil ..
  | cons b t ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    power_step
    power_step
    power_step
    exact ih (b :: x) (b :: f)

private theorem reverse_run (x t a : List Bool) :
    StackRuns (code p) (2 * a.length + 1) (.round i .reverseProduct) (store x t [] [] a)
      (.round i .restoreProduct) (store x (a.reverse ++ t) [] [] []) := by
  induction a generalizing t with
  | nil => power_step; exact .nil ..
  | cons b a ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    power_step
    power_step
    exact ih (b :: t)

private theorem put_run (x t a : List Bool) :
    StackRuns (code p) (2 * t.length + 1) (.round i .restoreProduct) (store x t a [] [])
      (.round ⟨i.val - 1, by omega⟩ .test) (store x [] (t.reverse ++ a) [] []) := by
  induction t generalizing a with
  | nil => power_step; exact .nil ..
  | cons b t ih =>
    simp only [List.length_cons, Nat.mul_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    power_step
    power_step
    exact ih (b :: a)

private theorem mul_run {w : ℕ} (x a : Word w) :
    StackRuns (code p) (8*w^2+9*w+4) (.round i (.mul .init))
      (store (wordBits x) [] (wordBits a) (wordBits x) []) (.round i (.mul .done))
      (store (wordBits x) [] [] [] (wordBits (x*a))) := by
  have hinj : Function.Injective Port.mul := fun _ _ h => Port.mul.inj h
  let base := store (wordBits x) [] [] [] []
  have h := (Mul.multiply_word_run x a).lift Port.mul hinj (fun s => State.round i (.mul s)) base
    (target := code p) (by intro q h; cases q <;> first | rfl | simp [Mul.code] at h)
  have hstore (u v t : List Bool) :
      installStacks Port.mul base (Mul.store u v t [] []) = store (wordBits x) [] u v t := by
    funext k
    cases k with
    | mul r => rw [installStacks_at hinj]; rfl
    | base | tmp => rw [installStacks_outside _ _ (by intro r; simp)]; rfl
  have he : PrivateRAM.BinaryOp.mul.eval x a = x * a := by apply Fin.ext; rfl
  simpa only [hstore, he] using h

/-- One round costs a quadratic number of bit operations and leaves the base available. -/
theorem round_run {w : ℕ} (x a : Word w) (hi : i.val ≠ 0) :
    StackRuns (code p) (8*w^2+18*w+10) (.round i .test) (store (wordBits x) [] (wordBits a) [] [])
      (.round ⟨i.val-1, by omega⟩ .test) (store (wordBits x) [] (wordBits (x*a)) [] []) := by
  have h₁ := copy_run i (wordBits x) [] (wordBits a)
  have h₂ := restore_run i [] (wordBits x).reverse (wordBits a) []
  have h₃ := mul_run i x a
  have h₄ := reverse_run i (wordBits x) [] (wordBits (x*a))
  have h₅ := put_run i (wordBits x) (wordBits (x*a)).reverse []
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse, length_wordBits] at h₁ h₂ h₄ h₅
  have ht := (h₁.trans h₂).trans (h₃.trans
    (StackRuns.cons (StackStep.goto (show code p (.round i (.mul .done)) = _ from rfl)) (h₄.trans h₅)))
  convert StackRuns.cons (StackStep.goto (show code p (.round i .test) =
    .goto (.round i .copy) by simp [code, hi])) ht using 1
  ring

/-- The full fixed power loop works at every bit width, including zero width. -/
theorem power_run {w : ℕ} (x a : Word w) :
    StackRuns (code p) (i.val * (8*w^2+18*w+10) + 1) (.round i .test)
      (store (wordBits x) [] (wordBits a) [] []) .done
      (store (wordBits x) [] (wordBits (Fin.ofNat (2^w) (x.val^i.val*a.val))) [] []) := by
  obtain ⟨k, hk⟩ := i
  induction k generalizing a with
  | zero =>
    have he : Fin.ofNat (2^w) (x.val^0*a.val) = a := by apply Fin.ext; simp [Fin.ofNat, Nat.mod_eq_of_lt a.isLt]
    simpa only [he, Nat.zero_mul, Nat.zero_add] using StackRuns.cons (StackStep.goto (show code p (.round ⟨0,hk⟩ .test) =
      .goto .done by simp [code])) (StackRuns.nil (code := code p) .done (store (wordBits x) [] (wordBits a) [] []))
  | succ k ih =>
    have h := (round_run (⟨k+1,hk⟩ : Fin (p+1)) x a (by simp)).trans (ih (x*a) (by omega))
    convert h using 1
    · change (k+1)*_+1 = _ + (k*_+1)
      ring
    · congr 2
      apply Fin.ext
      change (x.val ^ (k+1) * a.val) % _ = (x.val ^ k * ((x.val * a.val) % (2^w))) % _
      rw [Nat.mul_mod_mod, pow_succ, Nat.mul_assoc]

end RAMTape.InputPower

end VPVNP
end Computability
end OAI
