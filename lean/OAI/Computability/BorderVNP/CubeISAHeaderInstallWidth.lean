import OAI.Computability.BorderVNP.RoutingISATableState
import OAI.Computability.BorderVNP.RoutingISARegisterFrame
import OAI.Computability.BorderVNP.RoutingISABlockAppend
import OAI.Computability.BorderVNP.RoutingISAOrdinaryCost
import Mathlib.Data.Nat.Log

/-! # Native binary widths for the cube declaration header

The width of a field with `n` choices is the number of bits in `n - 1`.
The loop counts successive unsigned divisions by two, including when the
original input occupies the entire word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.HeaderInstall

open VPVNP.BurstRAM

private def widthSetup : Code := .block [
  .constant 46 0, .constant 47 0, .constant 48 1, .constant 49 2,
  .ifLt 47 45 (.binary .sub 45 45 48) .nop]

private def widthStep : Code := .seq (.binary .div 45 45 49) (.binary .add 46 46 48)

/-- Read the field cardinality from register 45 and return its ceiling binary
logarithm in register 46. Registers 47 through 49 hold zero, one and two. -/
def width : Code := .seq widthSetup (.whileLt 47 45 widthStep)

/-- The width calculation executes only ordinary deterministic instructions. -/
theorem width_deterministic : width.deterministic = true := by decide

private theorem atom_length {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (run : Runs pub mac c s m es t mt) (atomic : c.isAtom = true) :
    es.length = 1 := by
  cases run <;> first | rfl | cases atomic

private theorem setup_cost {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} (run : Runs pub mac widthSetup s m es t mt) : traceCost es = 6 := by
  rw [run.deterministic_cost (by decide)]
  simp only [widthSetup, Code.block, Runs.seq_iff] at run
  rcases run with ⟨_, _, _, _, rfl, r₁, _, _, _, _, rfl, r₂, _, _, _, _, rfl, r₃,
    _, _, _, fs, rfl, r₄, guard⟩
  have tail : fs.length = 2 := by
    cases guard with
    | atom h _ _ => cases h
    | ifLt branch =>
      split at branch <;> simp [atom_length branch rfl]
  simp [atom_length r₁ rfl, atom_length r₂ rfl, atom_length r₃ rfl, atom_length r₄ rfl, tail]

private theorem step_cost {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es t mt} (run : Runs pub mac widthStep s m es t mt) : traceCost es = 2 := by
  rw [run.deterministic_cost (by decide)]
  obtain ⟨_, _, _, _, rfl, halve, inc⟩ := Runs.seq_iff.mp run
  simp [atom_length halve rfl, atom_length inc rfl]

private theorem half_clog {n : ℕ} (hn : 0 < n) :
    Nat.clog 2 (n + 1) = Nat.clog 2 (n / 2 + 1) + 1 := by
  rw [Nat.clog_of_one_lt (by decide : 1 < 2) (by omega : 1 < n + 1)]
  congr 2
  omega

private theorem width_loop {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (n k : ℕ) (s : Bank w) (m : Memory w)
    (hn : readings s 45 = n) (hk : readings s 46 = k)
    (hz : readings s 47 = 0) (ho : readings s 48 = 1) (ht : readings s 49 = 2)
    (fit : k + Nat.clog 2 (n + 1) < 2 ^ w) :
    ∃ es t, Runs pub macros (.whileLt 47 45 widthStep) s m es t m ∧
      traceCost es = 1 + 3 * Nat.clog 2 (n + 1) ∧
      readings t 46 = k + Nat.clog 2 (n + 1) := by
  by_cases pos : 0 < n
  · have halves := half_clog pos
    have inc : k + 1 < 2 ^ w := by omega
    have safe : widthStep.safeReadOnly w (readings pub) (readings m) (readings s) := by
      simp (config := {decide := true}) [widthStep, Code.safeReadOnly, Code.evalNat,
        addressOpFits, hk, ho, ht, inc]
    obtain ⟨es,t,r,_,eq⟩ := widthStep.runReadOnly pub macros m s safe
    have next (j : Reg) := congrFun eq j
    obtain ⟨fs,u,loop,cl,ret⟩ := width_loop pub macros (n / 2) (k + 1) t m
      (by simpa (config := {decide := true}) [widthStep, Code.evalNat, addressOp, hn, ht]
        using next 45)
      (by simpa (config := {decide := true}) [widthStep, Code.evalNat, addressOp, hk, ho]
        using next 46)
      (by simpa (config := {decide := true}) [widthStep, Code.evalNat, hz] using next 47)
      (by simpa (config := {decide := true}) [widthStep, Code.evalNat, ho] using next 48)
      (by simpa (config := {decide := true}) [widthStep, Code.evalNat, ht] using next 49)
      (by omega)
    have guard : s 47 < s 45 := show readings s 47 < readings s 45 by omega
    refine ⟨_,u,.whileStep guard r loop,?_,by omega⟩
    change 1 + traceCost (es ++ fs) = _
    rw [show traceCost (es ++ fs) = traceCost es + traceCost fs from
      VPVNP.RAMBuckets.cost_append ..]
    rw [step_cost r, cl, halves]
    omega
  · have zero : n = 0 := by omega
    have guard : ¬ s 47 < s 45 := show ¬ readings s 47 < readings s 45 by omega
    exact ⟨_,s,.whileDone guard,by change 1 = _; simp [zero],by simp [zero,hk]⟩
termination_by n
decreasing_by omega

private theorem width_keeps (j : Reg) (hj : j.val < 45 ∨ 50 < j.val) : width.keeps j = true := by
  have ne (k : Reg) (h : 45 ≤ k.val ∧ k.val ≤ 50) : j ≠ k := by
    rintro rfl
    omega
  simp [width,widthSetup,widthStep,Code.block,Code.keeps,ne 45 (by decide),
    ne 46 (by decide),ne 47 (by decide),ne 48 (by decide),ne 49 (by decide)]

/-- The returned width and the exact trace cost of the deterministic calculation. -/
theorem width_exact {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hw : 2 < 2 ^ w) :
    ∃ es t, Runs pub macros width s m es t m ∧
      traceCost es = 7 + 3 * Nat.clog 2 (readings s 45) ∧
      readings t 46 = Nat.clog 2 (readings s 45) := by
  let n := readings s 45
  have safe : widthSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [widthSetup, Code.block, Code.safeReadOnly, Code.evalNat,
      addressOpFits]
    exact ⟨fun h => by simp [h] at hw, hw, fun h => h⟩
  obtain ⟨es,t,first,_,eq⟩ := widthSetup.runReadOnly pub macros m s safe
  have setup : readings t 45 = n - 1 ∧ readings t 46 = 0 ∧ readings t 47 = 0 ∧
      readings t 48 = 1 ∧ readings t 49 = 2 := by
    rw [eq]
    by_cases hp : 0 < readings s 45
    · simp (config := {decide := true}) [n,widthSetup,Code.block,Code.evalNat,addressOp,hp]
    · have z : readings s 45 = 0 := by omega
      simp (config := {decide := true}) [n,widthSetup,Code.block,Code.evalNat,z]
  obtain ⟨pred,zero,h47,h48,h49⟩ := setup
  have log : Nat.clog 2 ((n - 1) + 1) = Nat.clog 2 n := by cases n <;> simp
  have bound : Nat.clog 2 n ≤ w := Nat.clog_le_of_le_pow (s 45).isLt.le
  obtain ⟨fs,u,loop,cl,ret⟩ := width_loop pub macros (n - 1) 0 t m pred zero h47 h48 h49
    (by rw [log, Nat.zero_add]; exact bound.trans_lt Nat.lt_two_pow_self)
  refine ⟨_, u, first.seq loop, ?_, by simpa [log,n] using ret⟩
  change traceCost (es ++ fs) = 7 + 3 * Nat.clog 2 n
  rw [show traceCost (es ++ fs) = traceCost es + traceCost fs from
    VPVNP.RAMBuckets.cost_append .., setup_cost first, cl, log]
  omega

/-- Four constants and a guarded decrement take six ticks, each halving takes
three ticks including the loop guard, and the final guard takes one tick. -/
theorem width_ticks {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {s m es t mt} (hw : 2 < 2 ^ w) (run : Runs pub macros width s m es t mt) :
    traceCost es = 7 + 3 * Nat.clog 2 (readings s 45) := by
  obtain ⟨_, _, witness, cost, _⟩ := width_exact pub macros s m hw
  rw [(run.unique_of_deterministic width_deterministic witness).1, cost]

/-- The fixed machine computes the ceiling binary logarithm within a linear
number of ticks in the resulting field width. Its memory and the caller's
registers outside the reserved scratch interval retain their exact readings. -/
theorem width_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (hw : 2 < 2 ^ w) :
    BoundedRun pub macros width s m (12 + 4 * Nat.clog 2 (readings s 45))
      (fun z => z.reg 46 = Nat.clog 2 (readings s 45) ∧ z.mem = readings m ∧
        ∀ j : Reg, (j.val < 45 ∨ 50 < j.val) → z.reg j = readings s j) := by
  obtain ⟨es,t,run,cost,ret⟩ := width_exact pub macros s m hw
  refine ⟨es, t, m, run, by omega, ret, rfl, ?_⟩
  intro j hj
  exact congrArg Fin.val (run.keepsReg (width_keeps j hj))

end RoutingISA.HeaderInstall

end BorderVNP
end Computability
end OAI
