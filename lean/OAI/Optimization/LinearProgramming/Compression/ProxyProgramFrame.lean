import OAI.Optimization.LinearProgramming.Compression.ProxySeriesCost

/-! Register frames for linking the logarithm series and dyadic search kernels. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

/-- Every scalar register from `d` onwards and every address register from `a`
onwards retains its caller value. -/
def PreservesRegisters {K : Type*} (d a : ℕ) (s t : State K) : Prop :=
  (∀ j, d ≤ j → t.data j = s.data j) ∧ (∀ j, a ≤ j → t.index j = s.index j)

theorem PreservesRegisters.trans {K : Type*} {d a : ℕ} {s t u : State K}
    (hst : PreservesRegisters d a s t) (htu : PreservesRegisters d a t u) :
    PreservesRegisters d a s u :=
  ⟨fun j hj => (htu.1 j hj).trans (hst.1 j hj), fun j hj => (htu.2 j hj).trans (hst.2 j hj)⟩

theorem PreservesRegisters.weaken {K : Type*} {d a d' a' : ℕ} {s t : State K}
    (h : PreservesRegisters d a s t) (hd : d ≤ d') (ha : a ≤ a') :
    PreservesRegisters d' a' s t :=
  ⟨fun j hj => h.1 j (hd.trans hj), fun j hj => h.2 j (ha.trans hj)⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Any legal prefix of the fixed series kernel only changes scalar registers
0–7 and address registers 0–1. -/
theorem logSeriesProgram_frame {s t : State K} {k : ℕ}
    (h : runExactly logSeriesProgram s k = some t) : PreservesRegisters 8 2 s t := by
  have stepFrame {u v : State K} (hv : step logSeriesProgram u = some v) :
      PreservesRegisters 8 2 u v := by
    unfold step at hv
    cases hgo : u.output <;> rw [hgo] at hv
    · cases ha : logSeriesProgram[u.pc]? with
      | none => simp [ha] at hv
      | some op =>
        rw [ha] at hv
        have his := List.mem_of_getElem? ha
        simp [logSeriesProgram] at his
        rcases his with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst op <;>
          simp only [execInstr] at hv <;> (try split at hv) <;>
          simp_all only [Option.some.injEq, reduceCtorEq]
        all_goals
          rw [← hv]
          constructor <;> intro j hj <;>
            simp (disch := omega) only [State.putData, State.putIndex, Function.update_of_ne]
    · simp at hv
  induction k generalizing t with
  | zero =>
    change some s = some t at h
    cases Option.some.inj h
    exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ k ih =>
    change (runExactly logSeriesProgram s k).bind (step logSeriesProgram) = some t at h
    cases hu : runExactly logSeriesProgram s k with
    | none => simp [hu] at h
    | some u => exact (ih hu).trans (stepFrame (by simpa [hu] using h))

private theorem grid_entry_frame {s t : State K} {M : ℕ} (hpc : s.pc = 0)
    (hgo : s.output = none) (ht : runExactly dyadicGridProgram s 7 = some t) :
    PreservesRegisters (8+M) 3 s t := by
  simp [runExactly, step, dyadicGridProgram, execInstr, State.putData, State.putIndex,
    Function.update, hpc, hgo] at ht
  rw [← ht]
  constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

private theorem grid_round_frame {s t : State K} {M i : ℕ} {q : K}
    (hh : GridHead s q M i) (hi : i < M)
    (ht : runExactly dyadicGridProgram s 13 = some t) : PreservesRegisters (8+M) 3 s t := by
  obtain ⟨hpc, hgo, hm, hi', hw, h₁, h₂, _, _, _, _⟩ := hh
  by_cases hc : s.data 5 * 2 < s.data 3 * 2 + 1 <;>
    simp (config := { maxSteps := 50000 }) [runExactly, step, dyadicGridProgram, execInstr,
      State.putData, State.putIndex, Function.update, hpc, hgo, hm, hi', hw, h₁, h₂, hi, hc] at ht
  all_goals
    rw [← ht]
    constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

/-- Enter the grid kernel at instruction zero. It returns immediately before
the halt, with all high caller slots preserved and the construction bits written. -/
theorem grid_run_until_halt (q : K) (M : ℕ) (a : State K) (hpc : a.pc = 0)
    (hgo : a.output = none) (hd : a.data 0 = q) (hm : a.index 0 = M) :
    ∃ u, runExactly dyadicGridProgram a (7 + 13 * M + 2) = some u ∧
      u.pc = 24 ∧ u.output = none ∧
      u.data 0 = ((dyadicSearch (dyadicTest q) M).1 : K) / 2 ^ M ∧
      (∀ j < M, u.data (8+j) = ((gridDigit q j).toNat : K)) ∧
      PreservesRegisters (8+M) 3 a u := by
  have hloop (i : ℕ) (hi : i ≤ M) :
      ∃ s, runExactly dyadicGridProgram a (7 + 13 * i) = some s ∧
        GridHead s q M i ∧ PreservesRegisters (8+M) 3 a s := by
    induction i with
    | zero =>
      obtain ⟨u, hu, hh⟩ := grid_init q M a hpc hgo hd hm
      exact ⟨u, by simpa only [Nat.mul_zero, Nat.add_zero] using hu,
        hh, grid_entry_frame hpc hgo hu⟩
    | succ i ih =>
      obtain ⟨s, hs, hh, hf⟩ := ih (by omega)
      obtain ⟨t, ht, hh'⟩ := grid_body hh (by omega)
      refine ⟨t, ?_, hh', hf.trans (grid_round_frame hh (by omega) ht)⟩
      rw [show 7 + 13 * (i + 1) = 7 + 13 * i + 13 by omega,
        runExactly_add_series, hs, Option.bind_some]
      exact ht
  obtain ⟨s, hs, hh, hf⟩ := hloop M le_rfl
  obtain ⟨hpc', hgo', hm', hi', _, _, _, h₃, h₄, _, hbits⟩ := hh
  rw [runExactly_add_series, hs, Option.bind_some]
  simp [runExactly, step, dyadicGridProgram, execInstr, State.putData, Function.update,
    hpc', hgo', hm', hi', h₃, h₄]
  refine ⟨hbits, hf.trans ?_⟩
  constructor <;> intro j hj <;> simp (disch := omega) only [Function.update_of_ne]

end Compression
end LinearProgramming
end Optimization
end OAI
