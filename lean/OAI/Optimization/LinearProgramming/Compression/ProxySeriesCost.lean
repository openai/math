import OAI.Optimization.LinearProgramming.Compression.ProxySeries
import OAI.Optimization.LinearProgramming.FieldTransfer.Execution

/-! Fixed-program RAM evaluation of the logarithm truncation and generation of dyadic bits over ordered fields. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer
open scoped BigOperators

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Input data register 0 holds `z`. Address register 0 holds the term count.
The accumulated sum is stored in data register 5. -/
def logSeriesProgram : Program := [
  .const 1 1, .const 2 2, .sub 3 0 1, .add 4 0 1, .div 3 3 4, .mul 4 3 3,
  .const 5 0, .copy 6 1, .addrConst 1 0,
  .branchAddrLT 1 0 10 16,
  .div 7 3 6, .add 5 5 7, .mul 3 3 4, .add 6 6 2, .incr 1 1, .jump 9,
  .mul 0 5 2, .halt 0]

def oddPartial (x : K) (i : ℕ) :=
  ∑ j ∈ Finset.range i, x ^ (2 * j + 1) / (2 * (j : K) + 1)

def SeriesHead (s : State K) (x : K) (M i : ℕ) : Prop :=
  s.pc = 9 ∧ s.output = none ∧ s.index 0 = M ∧ s.index 1 = i ∧
  s.data 2 = 2 ∧ s.data 3 = x ^ (2 * i + 1) ∧ s.data 4 = x ^ 2 ∧
  s.data 5 = oddPartial x i ∧ s.data 6 = 2 * (i : K) + 1

theorem series_init (z : K) (M : ℕ) (hz : 1 ≤ z) (a : State K)
    (ha : a.pc = 0) (ho : a.output = none) (hd : a.data 0 = z) (hm : a.index 0 = M) :
    ∃ s, runExactly logSeriesProgram a 9 = some s ∧
      SeriesHead s ((z - 1) / (z + 1)) M 0 := by
  have h : z + 1 ≠ 0 := by linarith
  simp [runExactly, step, logSeriesProgram, execInstr, State.putData, State.putIndex,
    Function.update, ha, ho, hd, hm, h, SeriesHead, oddPartial, pow_two]

theorem series_body {s : State K} {x : K} {M i : ℕ}
    (hs : SeriesHead s x M i) (hi : i < M) :
    ∃ t, runExactly logSeriesProgram s 7 = some t ∧ SeriesHead t x M (i + 1) := by
  obtain ⟨hpc, hgo, hM, hi', h₂, h₃, h₄, h₅, h₆⟩ := hs
  have hden : 2 * (i : K) + 1 ≠ 0 := by positivity
  have hpow : x ^ (2 * (i + 1) + 1) = x ^ (2 * i + 1) * x ^ 2 := by
    rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 2 by omega, pow_add]
  have hrat : 2 * ((i : K) + 1) + 1 = (2 * (i : K) + 1) + 2 := by ring
  simp [runExactly, step, logSeriesProgram, execInstr, State.putData, State.putIndex,
    Function.update, hpc, hgo, hM, hi', h₂, h₃, h₄, h₅, h₆, hden, hi, SeriesHead,
    oddPartial, Finset.sum_range_succ, hpow, hrat]

private theorem series_finish {s : State K} {x : K} {M : ℕ} (hs : SeriesHead s x M M) :
    ∃ t, runExactly logSeriesProgram s 3 = some t ∧ t.data 0 = 2 * oddPartial x M ∧
      t.output = some 0 := by
  obtain ⟨hpc, hgo, hM, hi', h₂, _, _, h₅, _⟩ := hs
  simp [runExactly, step, logSeriesProgram, execInstr, State.putData, Function.update,
    hpc, hgo, hM, hi', h₂, h₅, mul_comm]

theorem runExactly_add_series (p : Program) (s : State K) (i j : ℕ) :
    runExactly p s (i + j) = (runExactly p s i).bind (fun a => runExactly p a j) := by
  induction j with
  | zero => simp [runExactly]
  | succ j ih => simp [runExactly, ih, Option.bind_assoc]

/-- One fixed rational-constant RAM program computes the specified partial sum in exactly
`7M + 12` instructions, counting comparisons, register updates, branches and halt. -/
theorem logSeriesProgram_exec {z : K} (hz : 1 ≤ z) (M : ℕ) :
    ∃ t : Fin (9 + 7 * M + 3 + 1) → State K,
      Trace logSeriesProgram (start [M] [z]) (9 + 7 * M + 3) t ∧
      (t (Fin.last _)).output = some 0 ∧ (t (Fin.last _)).data 0 = logTruncation z M := by
  let x := (z - 1) / (z + 1)
  have hloop (i : ℕ) (hi : i ≤ M) :
      ∃ s, runExactly logSeriesProgram (start [M] [z]) (9 + 7 * i) = some s ∧
        SeriesHead s x M i := by
    induction i with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero] using series_init z M hz (start [M] [z]) rfl rfl rfl rfl
    | succ i ih =>
      obtain ⟨s, hs, hs'⟩ := ih (by omega)
      obtain ⟨t, ht, ht'⟩ := series_body hs' (by omega)
      refine ⟨t, ?_, ht'⟩
      rw [show 9 + 7 * (i + 1) = 9 + 7 * i + 7 by omega,
        runExactly_add_series, hs, Option.bind_some]
      exact ht
  obtain ⟨s, hs, hs'⟩ := hloop M le_rfl
  obtain ⟨u, hu, hu', hout⟩ := series_finish hs'
  have hend : runExactly logSeriesProgram (start [M] [z]) (9 + 7 * M + 3) = some u := by
    rw [runExactly_add_series, hs, Option.bind_some]
    exact hu
  obtain ⟨t, H, Hlast⟩ := (runExactly_iff_trace _).mp hend
  exact ⟨t, H, Hlast ▸ hout, Hlast ▸ hu'⟩

/-- The next digit chosen by the comparison at level `j`, in most-significant
digit first order. -/
def gridDigit (q : K) (j : ℕ) : Bool :=
  dyadicTest q (2 * (dyadicSearch (dyadicTest q) j).1 + 1) (j + 1)

/-- A fixed RAM loop materializes the dyadic grid numerator one comparison
bit at a time. Data registers starting at 8 store the observed bits; register
0 holds the final quotient and registers 3 and 4 retain its two integers. -/
def dyadicGridProgram : Program := [
  .const 1 1, .const 2 2, .const 3 0, .copy 4 1, .copy 5 0,
  .addrConst 1 0, .addrConst 2 8, .branchAddrLT 1 0 8 23,
  .mul 5 5 2, .mul 4 4 2, .mul 3 3 2, .add 6 3 1, .branchLT 5 6 16 13,
  .copy 3 6, .copy 7 1, .jump 19,
  .copy 3 3, .const 7 0, .jump 19,
  .store 2 7, .incr 2 2, .incr 1 1, .jump 7,
  .div 0 3 4, .halt 0]

def GridHead (s : State K) (q : K) (M i : ℕ) : Prop :=
  s.pc = 7 ∧ s.output = none ∧ s.index 0 = M ∧ s.index 1 = i ∧ s.index 2 = 8 + i ∧
  s.data 1 = 1 ∧ s.data 2 = 2 ∧ s.data 3 = ((dyadicSearch (dyadicTest q) i).1 : K) ∧
  s.data 4 = 2 ^ i ∧ s.data 5 = 2 ^ i * q ∧
  ∀ j < i, s.data (8 + j) = ((gridDigit q j).toNat : K)

theorem grid_init (q : K) (M : ℕ) (a : State K) (ha : a.pc = 0)
    (ho : a.output = none) (hd : a.data 0 = q) (hm : a.index 0 = M) :
    ∃ s, runExactly dyadicGridProgram a 7 = some s ∧ GridHead s q M 0 := by
  simp [runExactly, step, dyadicGridProgram, execInstr, State.putData, State.putIndex,
    Function.update, ha, ho, hd, hm, GridHead, dyadicSearch]

theorem grid_body {s : State K} {q : K} {M i : ℕ}
    (hs : GridHead s q M i) (hi : i < M) :
    ∃ t, runExactly dyadicGridProgram s 13 = some t ∧ GridHead t q M (i + 1) := by
  obtain ⟨hpc, hgo, hm, hi', hw, h₁, h₂, h₃, h₄, h₅, hbits⟩ := hs
  let p := (dyadicSearch (dyadicTest q) i).1
  change s.data 3 = (p : K) at h₃
  have hguard : (2 ^ i * q * 2 < (p : K) * 2 + 1) ↔
      ¬(((2 * p + 1 : ℕ) : K) ≤ 2 ^ (i + 1) * q) := by
    push_cast
    rw [pow_succ, not_le]
    constructor <;> intro h <;> linarith
  have hdigit : dyadicTest q (2 * p + 1) (i + 1) = gridDigit q i := rfl
  have hnext : ((dyadicSearch (dyadicTest q) (i + 1)).1 : K) =
      (p : K) * 2 + ((gridDigit q i).toNat : K) := by
    simp [dyadicSearch, gridDigit, p, mul_comm]
  have hbits' (j : ℕ) (hj : j < i + 1) :
      (if j = i then ((gridDigit q i).toNat : K) else s.data (8 + j)) =
        ((gridDigit q j).toNat : K) := by
    by_cases hji : j = i
    · simp [hji]
    · simp [hji, hbits j (by omega)]
  have addr_ne (j r : ℕ) (hr : r < 8) : 8 + j ≠ r := by omega
  have ne_addr (j r : ℕ) (hr : r < 8) : r ≠ 8 + j := by omega
  have hmul : 2 ^ i * q * 2 = 2 ^ i * 2 * q := by ring
  by_cases h : ((2 * p + 1 : ℕ) : K) ≤ 2 ^ (i + 1) * q
  · have hcmp : ¬(2 ^ i * q * 2 < (p : K) * 2 + 1) := fun ht => (hguard.1 ht) h
    have hb : gridDigit q i = true := hdigit ▸ decide_eq_true h
    simp (config := { maxSteps := 50000 }) [runExactly, step, dyadicGridProgram, execInstr, State.putData,
      State.putIndex, Function.update, hpc, hgo, hm, hi', hw, h₁, h₂, h₃, h₄, h₅, hi,
      hcmp, GridHead, hnext, hb, pow_succ]
    simp (disch := decide) [addr_ne, ne_addr, Nat.add_assoc, hmul]
    simpa [hb] using hbits'
  · have hcmp := hguard.2 h
    have hb : gridDigit q i = false := hdigit ▸ decide_eq_false h
    simp (config := { maxSteps := 50000 }) [runExactly, step, dyadicGridProgram, execInstr, State.putData,
      State.putIndex, Function.update, hpc, hgo, hm, hi', hw, h₁, h₂, h₃, h₄, h₅, hi,
      hcmp, GridHead, hnext, hb, pow_succ]
    simp (disch := decide) [addr_ne, ne_addr, Nat.add_assoc, hmul]
    simpa [hb] using hbits'

private theorem grid_finish {s : State K} {q : K} {M : ℕ} (hs : GridHead s q M M) :
    ∃ t, runExactly dyadicGridProgram s 3 = some t ∧ t.output = some 0 ∧
      t.data 0 = ((dyadicSearch (dyadicTest q) M).1 : K) / 2 ^ M ∧
      ∀ j < M, t.data (8 + j) = ((gridDigit q j).toNat : K) := by
  obtain ⟨hpc, hgo, hm, hi', _, _, _, h₃, h₄, _, hbits⟩ := hs
  simp (config := { maxSteps := 50000 }) [runExactly, step, dyadicGridProgram, execInstr, State.putData,
    Function.update, hpc, hgo, hm, hi', h₃, h₄]
  exact hbits


/-- Grid kernel entry specification, allowing caller-owned scratch registers. -/
theorem grid_run_from (q : K) (M : ℕ) (a : State K) (hpc : a.pc = 0)
    (hgo : a.output = none) (hd : a.data 0 = q) (hm : a.index 0 = M) :
    ∃ u, runExactly dyadicGridProgram a (7 + 13 * M + 3) = some u ∧
      u.output = some 0 ∧ u.data 0 = ((dyadicSearch (dyadicTest q) M).1 : K) / 2 ^ M ∧
      ∀ j < M, u.data (8 + j) = ((gridDigit q j).toNat : K) := by
  have hloop (i : ℕ) (hi : i ≤ M) :
      ∃ s, runExactly dyadicGridProgram a (7 + 13 * i) = some s ∧
        GridHead s q M i := by
    induction i with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero] using grid_init q M a hpc hgo hd hm
    | succ i ih =>
      obtain ⟨s, hs, hs'⟩ := ih (by omega)
      obtain ⟨t, ht, ht'⟩ := grid_body hs' (by omega)
      refine ⟨t, ?_, ht'⟩
      rw [show 7 + 13 * (i + 1) = 7 + 13 * i + 13 by omega,
        runExactly_add_series, hs, Option.bind_some]
      exact ht
  obtain ⟨s, hs, hs'⟩ := hloop M le_rfl
  obtain ⟨u, hu, hout, hv, hbits⟩ := grid_finish hs'
  have hend : runExactly dyadicGridProgram a (7 + 13 * M + 3) = some u := by
    rw [runExactly_add_series, hs, Option.bind_some]
    exact hu
  exact ⟨u, hend, hout, hv, hbits⟩

/-- On any scalar ratio (with no access to its bits), the fixed grid program
performs exactly `13M + 10` steps and exposes all the bits of the dyadic
numerator in separately addressable registers. -/
theorem dyadicGridProgram_exec (q : K) (M : ℕ) :
    ∃ t : Fin (7 + 13 * M + 3 + 1) → State K,
      Trace dyadicGridProgram (start [M] [q]) (7 + 13 * M + 3) t ∧
      (t (Fin.last _)).output = some 0 ∧
      (t (Fin.last _)).data 0 = ((dyadicSearch (dyadicTest q) M).1 : K) / 2 ^ M ∧
      ∀ j < M, (t (Fin.last _)).data (8 + j) = ((gridDigit q j).toNat : K) := by
  obtain ⟨u, hend, hout, hv, hbits⟩ := grid_run_from q M (start [M] [q]) rfl rfl rfl rfl
  obtain ⟨t, H, Hlast⟩ := (runExactly_iff_trace _).mp hend
  exact ⟨t, H, Hlast ▸ hout, Hlast ▸ hv, Hlast ▸ hbits⟩

/-- The straight-line series kernel can be linked at its final address before
executing its standalone halt instruction. -/
theorem series_run_until_halt {z : K} (hz : 1 ≤ z) (M : ℕ) (a : State K)
    (hpc : a.pc = 0) (hgo : a.output = none) (hd : a.data 0 = z) (hm : a.index 0 = M) :
    ∃ u, runExactly logSeriesProgram a (9 + 7 * M + 2) = some u ∧
      u.pc = 17 ∧ u.output = none ∧ u.data 0 = logTruncation z M := by
  let x := (z - 1) / (z + 1)
  have hloop (i : ℕ) (hi : i ≤ M) :
      ∃ s, runExactly logSeriesProgram a (9 + 7 * i) = some s ∧ SeriesHead s x M i := by
    induction i with
    | zero => simpa only [Nat.mul_zero, Nat.add_zero] using series_init z M hz a hpc hgo hd hm
    | succ i ih =>
      obtain ⟨s, hs, hs'⟩ := ih (by omega)
      obtain ⟨t, ht, ht'⟩ := series_body hs' (by omega)
      refine ⟨t, ?_, ht'⟩
      rw [show 9 + 7 * (i + 1) = 9 + 7 * i + 7 by omega,
        runExactly_add_series, hs, Option.bind_some]
      exact ht
  obtain ⟨s, hs, hs'⟩ := hloop M le_rfl
  obtain ⟨hpc', hgo', hm', hi', h₂, _, _, h₅, _⟩ := hs'
  rw [runExactly_add_series, hs, Option.bind_some]
  simp [runExactly, step, logSeriesProgram, execInstr, State.putData, Function.update,
    hpc', hgo', hm', hi', h₂, h₅, x, logTruncation, oddPartial, mul_comm]

/-- The series kernel does not touch the caller registers used to retain
the precision, stage flag, and first numerator. -/
theorem series_caller_registers {s t : State K} {k : ℕ}
    (h : runExactly logSeriesProgram s k = some t) :
    t.data 9 = s.data 9 ∧ t.index 3 = s.index 3 ∧ t.index 4 = s.index 4 ∧
      t.index 5 = s.index 5 ∧ t.index 0 = s.index 0 := by
  have hstep {u v : State K} (hv : step logSeriesProgram u = some v) :
      v.data 9 = u.data 9 ∧ v.index 3 = u.index 3 ∧ v.index 4 = u.index 4 ∧
        v.index 5 = u.index 5 ∧ v.index 0 = u.index 0 := by
    unfold step at hv
    cases hgo : u.output <;> rw [hgo] at hv
    · cases ha : logSeriesProgram[u.pc]? with
      | none => simp [ha] at hv
      | some op =>
        rw [ha] at hv
        have his := List.mem_of_getElem? ha
        simp [logSeriesProgram] at his
        rcases his with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst op <;>
          simp only [execInstr] at hv <;>
          (try split at hv) <;> simp_all only [Option.some.injEq, reduceCtorEq]
        all_goals rw [← hv]; simp [State.putData, State.putIndex, Function.update]
    · simp at hv
  induction k generalizing t with
  | zero =>
    change some s = some t at h
    cases Option.some.inj h
    simp
  | succ k ih =>
    change (runExactly logSeriesProgram s k).bind (step logSeriesProgram) = some t at h
    cases hu : runExactly logSeriesProgram s k with
    | none => simp [hu] at h
    | some u =>
      obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := ih hu
      obtain ⟨g₁,g₂,g₃,g₄,g₅⟩ := hstep (by simpa [hu] using h)
      exact ⟨g₁.trans h₁, g₂.trans h₂, g₃.trans h₃, g₄.trans h₄, g₅.trans h₅⟩

end Compression
end LinearProgramming
end Optimization
end OAI
