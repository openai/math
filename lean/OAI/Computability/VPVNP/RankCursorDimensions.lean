import OAI.Computability.VPVNP.RankCursorDepth
import OAI.Computability.VPVNP.RankQueryGramReadSpace

/-! # Initializing a rank scan from the two binary matrix dimensions

Register one supplies the row count and register three supplies the column
count. The machine adds and multiplies them to compute the inner scan bound
`(n + m) * n`. The preceding logarithm pass initializes the balanced Schur
depth from the row-count word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch UniversalCountStack

variable {K : Type} [DecidableEq K]

/-- The two physical dimension words supplied by the caller. -/
def dimensionRegs (w n m : ℕ) : Regs Registers.R w :=
  Registers.initial (Fin.ofNat _ m) (Fin.ofNat _ n) 0

private def dimensionsCode : RegCode Registers.R :=
  .seq (.op (Registers.arg 2) .add (Registers.arg 1) (Registers.arg 3))
    (.seq (.op (Registers.arg 2) .mul (Registers.arg 2) (Registers.arg 1))
      (.copy (Registers.arg 3) (Registers.arg 2)))

/-- Cursor registers after computing the inner index and its bound as the word product `(n + m)
* n` in `w`-bit arithmetic. The outer register holds the word for `n`. -/
def startRegs (w n m : ℕ) := dimensionsCode.exec (dimensionRegs w n m)

private theorem arg_inj : Function.Injective Registers.arg := fun _ _ h => Fin.ext (congrArg (Fin.val : Fin Registers.R → ℕ) h)

theorem startRegs_stores {w : ℕ} (n m : ℕ) (hadd : n+m < 2^w) (hmul : (n+m)*n < 2^w) :
    Registers.Stores (startRegs w n m) ((n+m)*n) n ((n+m)*n) := by
  let rs := dimensionRegs w n m
  let sum := Arith.add.word (rs (Registers.arg 1)) (rs (Registers.arg 3))
  let prod := Arith.mul.word sum (rs (Registers.arg 1))
  have hn : n < 2^w := by omega
  have hm : m < 2^w := by omega
  have hstored := Registers.initial_stores (Fin.ofNat (2^w) m) (Fin.ofNat (2^w) n) (0 : Word w)
  have hx : (rs (Registers.arg 1)).val = n := by
    have h : (rs (Registers.arg 1)).val = (Fin.ofNat (2^w) n).val := hstored 1 (by decide)
    exact h.trans (Nat.mod_eq_of_lt hn)
  have hy : (rs (Registers.arg 3)).val = m := by
    have h : (rs (Registers.arg 3)).val = (Fin.ofNat (2^w) m).val := hstored 3 (by decide)
    exact h.trans (Nat.mod_eq_of_lt hm)
  have hs : sum.val = n+m := by
    change (Arith.add.word _ _).val = _
    have h : Arith.add.eval (rs (Registers.arg 1)).val (rs (Registers.arg 3)).val < 2^w := by
      change (rs (Registers.arg 1)).val + (rs (Registers.arg 3)).val < _
      rwa [hx, hy]
    have v := Arith.word_val .add _ _ h
    change _ = (rs (Registers.arg 1)).val + (rs (Registers.arg 3)).val at v
    rwa [hx, hy] at v
  have hp : prod.val = (n+m)*n := by
    change (Arith.mul.word _ _).val = _
    have h : Arith.mul.eval sum.val (rs (Registers.arg 1)).val < 2^w := by
      change sum.val * (rs (Registers.arg 1)).val < _
      rwa [hs, hx]
    have v := Arith.word_val .mul _ _ h
    change _ = sum.val * (rs (Registers.arg 1)).val at v
    rwa [hs, hx] at v
  have hfinal : startRegs w n m =
      Function.update (Function.update rs (Registers.arg 2) prod) (Registers.arg 3) prod := by
    simp [startRegs, dimensionsCode, RegCode.exec, arg_inj.eq_iff, prod, sum, rs]
  intro i hi
  rw [hfinal]
  by_cases h₂ : i = 2
  · subst i; simpa [arg_inj.eq_iff, input] using hp
  by_cases h₃ : i = 3
  · subst i; simpa [input] using hp
  rw [Function.update_of_ne (arg_inj.ne h₃), Function.update_of_ne (arg_inj.ne h₂)]
  have h := hstored i hi
  fin_cases i <;> first | exact hx | exact h | contradiction

private def arithmeticPort (i : ISA.Port Registers.R 0) : ScanPort K := .cursor (.isa i)

/-- Prepare the balanced-product depth from the row count and compute the inner scan bound from
the two dimension registers. -/
def initializeDimensions : FiniteRoutine (ScanPort K) :=
  prepareDepth.followedBy (dimensionsCode.compile.onPorts arithmeticPort)

/-- Step bound for computing the logarithmic depth and initializing the dimension registers
before the first rank query. -/
def startupClock (w : ℕ) := depthClock w + 5 * (100*(w+1)^2)

/-- Stack-height bound during rank initialization, accounting for the work bank, the w-bit
registers, and the existing flag stack. -/
def startupSpace (A w flags : ℕ) := max (max w flags) A + startupClock w

omit [DecidableEq K] in
private theorem bank_length {w : ℕ} (n : ℕ) (persist : Word w) (rs : Regs Registers.R w)
    (flags : List Bool) (work : Stacks (Engine.Port K)) (A : ℕ) (ha : ∀ i, (work i).length ≤ A)
    (k : ScanPort K) : (scanBank n persist rs flags work [] k).length ≤ max (max w flags.length) A := by
  cases k with
  | cursor j => exact (Registers.bank_length persist rs flags j).trans (le_max_left ..)
  | engine j => exact (ha j).trans (le_max_right ..)
  | rows | depth => exact (length_digits ..).le.trans ((le_max_left ..).trans (le_max_left ..))
  | scratch => exact Nat.zero_le _

/-- From encoded row and column counts, prepare the cursor and Schur root
constants and return the correct initial cursor registers. -/
theorem initialize_bounded {w A : ℕ} (n m : ℕ) (hn : n < 2^w)
    (persistent : Word w) (flags : List Bool) (work : Stacks (Engine.Port K))
    (ha : ∀ i, (work i).length ≤ A) :
    ∃ t ≤ startupClock w, initializeDimensions.BoundedRun (startupSpace A w flags.length) t
      (Function.update (scanBank n persistent (dimensionRegs w n m) flags work) ScanPort.depth [])
      (scanBank n persistent (startRegs w n m) flags work) := by
  obtain ⟨t₁,h₁,depth⟩ := prepareDepth_bounded n hn persistent (dimensionRegs w n m) flags work ha
  obtain ⟨t₂,h₂,arith⟩ := dimensionsCode.compile_runs Fin.elim0 persistent (dimensionRegs w n m)
  change t₂ ≤ 5 * (100*(w+1)^2) at h₂
  have run : (dimensionsCode.compile.onPorts (arithmeticPort (K := K))).Runs t₂
      (scanBank n persistent (dimensionRegs w n m) flags work)
      (scanBank n persistent (startRegs w n m) flags work) := by
    apply FiniteRoutine.runs_onPorts_framed _ (fun _ _ h => Registers.Port.isa.inj (ScanPort.cursor.inj h))
      arith (fun _ => rfl) (fun _ => rfl)
    intro k hk; cases k with
    | cursor j => cases j with | isa i => exact (hk i rfl).elim | flag => rfl
    | _ => rfl
  have hd : max (max w flags.length) A + depthClock w ≤ startupSpace A w flags.length :=
    Nat.add_le_add_left (Nat.le_add_right ..) _
  have hr : (dimensionsCode.compile.onPorts (arithmeticPort (K := K))).BoundedRun (startupSpace A w flags.length) t₂
      (scanBank n persistent (dimensionRegs w n m) flags work)
      (scanBank n persistent (startRegs w n m) flags work) :=
    spaceRun_of_steps run (fun k => Nat.add_le_add (bank_length n persistent _ flags work A ha k)
      (h₂.trans (Nat.le_add_left ..)))
  exact ⟨_, Nat.add_le_add h₁ h₂, (depth.enlarge hd).followedBy hr⟩

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
