import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotPhysical
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotScaledInstall

/-! # Packed input and the scaled physical multiplication driver

A fixed positive multiplier sets the reach of the common fence on every
candidate tape. The prelude installs it from the packed input before the
geometric scheduler begins.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.IndexedSlot.Source
open IntegerMultiplication TM ScheduleMachine SlotLayout

variable {A Q I : Type}

def scaledLower (D n : ℕ) (_ : I) : ℤ := -((D*(2*n+1) : ℕ) : ℤ)
def scaledUpper (D n : ℕ) (_ : I) : ℤ := ((D*(2*n+1) : ℕ) : ℤ)

/-- Width of all the fixed intervals, charged against the input length. -/
theorem scaled_widths (I : Type) [Fintype I] (D n : ℕ) :
    (∑ j : I, (scaledUpper D n j+1-scaledLower D n j).toNat) ≤
      ((4*D+1)*Fintype.card I)*(n+1) := by
  have width (j : I) : (scaledUpper D n j+1-scaledLower D n j).toNat = 2*(D*(2*n+1))+1 := by
    suffices ∀ k : ℕ, ((k : ℤ)+1-(-(k : ℤ))).toNat=2*k+1 from this _
    intro k
    omega
  simp only [width,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  calc
    Fintype.card I*(2*(D*(2*n+1))+1) ≤ Fintype.card I*((4*D+1)*(n+1)) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    _ = _ := by ring

variable (s : Source A Q I) [Fintype I] [DecidableEq I] [DecidableEq A]

noncomputable def physicalDriver_scaled (D : ℕ) :=
  s.driver (scaledLower D) (scaledUpper D)
    (SlotBlank.rule (SlotBlank.perm s.blank (literal s.blank))
      (SlotBoot.rule s.blank (SlotScaledInstall.rule D s.inp s.idx s.blank))) (some (SlotScaledInstall.start D))

open private packed packed_length loaded_input plain_input from
  OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstallDriver

/-- Reach the scheduler's initialized layout, including the origin-stamping
transition, in at most `(40*D+1)*(n+1)` physical transitions. -/
theorem prepare_scaled (D : ℕ) (hD : 0<D) (n : ℕ) (x : Input n)
    (letters : (∀ b, s.bit b ≠ s.blank) ∧ s.sep ≠ s.blank) (distinct : s.idx ≠ s.inp) :
    let d := s.physicalDriver_scaled D
    ∃ t z, t ≤ (40*D+1)*(n+1) ∧
      Trace (advance d.setup) (d.initial n x) t z ∧ advance d.setup z=none ∧
      z.tape = counters d.blank d.mark 0 0 (d.work n x) := by
  let w := packed s n x
  have len : w.length = 2*n+1 := packed_length s n x
  have clean : s.blank ∉ w := by
    simp only [w,packed,List.mem_append,List.mem_map,List.mem_singleton]
    rintro ((⟨b,_,he⟩ | he) | ⟨b,_,he⟩)
    · exact letters.1 b he
    · exact letters.2 he.symm
    · exact letters.1 b he
  obtain ⟨run,stop⟩ := SlotScaledInstall.install D s.inp s.idx s.blank w distinct.symm hD (by omega) clean
  have raw : SlotInstall.loaded s.inp s.blank w = s.input n x := loaded_input s n x
  have plain : SlotInstall.plain s.inp s.blank w = fun j => unmarked (s.input n x j) := plain_input s n x
  rw [plain] at run
  obtain ⟨z,run',stop',ready⟩ := initialize_frame s n x (scaledLower D) (scaledUpper D) distinct _ _ run stop (by
    simp [raw,len,scaledLower,scaledUpper])
  refine ⟨_,z,?_,run',stop',ready⟩
  have k := SlotScaledInstall.time_le D w.length hD
  rw [len] at k
  change SlotScaledInstall.time D w.length+1 ≤ _
  rw [len]
  nlinarith

variable [Finite A]

/-- One fixed search machine for every source that meets the scaled comparison
bounds, with setup, slot overhead and a common space coefficient. -/
theorem physical_implementation_scaled (D : ℕ) (hD : 0<D) {K p : ℕ}
    (runs : s.Runs (scaledLower D) (scaledUpper D) K p) :
    (s.physicalDriver_scaled D).Implements (40*D+1)
      (SlotCost.coefficient I ((4*D+1)*Fintype.card I) 2) 120 K p := by
  have c : s.Comparison (scaledLower D) (scaledUpper D) ((4*D+1)*Fintype.card I) K p :=
    { runs with
      origin := by intro n j; simp [scaledLower,scaledUpper]
      widths := scaled_widths I D }
  exact s.implementation (scaledLower D) (scaledUpper D) c _ _
    (fun n x => s.prepare_scaled D hD n x ⟨fun b => (runs.letters.2.1 b).2,runs.letters.2.2⟩ runs.separate.2.2)

/-- A finite indexed source with a fixed positive fence coefficient realizes
the literal single-machine multiplication specification. -/
theorem uniformMultiplicationSpec_scaled [Finite Q] (D : ℕ) (hD : 0<D) {K p : ℕ}
    (runs : s.Runs (scaledLower D) (scaledUpper D) K p) : UniformMultiplicationSpec :=
  (s.physicalDriver_scaled D).uniformMultiplicationSpec (s.physical_implementation_scaled D hD runs)

end Uniform.IndexedSlot.Source

end NearSquareRoot
end Computability
end OAI
