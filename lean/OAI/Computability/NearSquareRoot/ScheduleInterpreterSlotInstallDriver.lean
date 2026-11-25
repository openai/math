import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInitial
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstall

/-! # The fixed packed-input prelude for the uniform multiplication driver

An input of two `n`-bit words has one separating symbol. The installer reads
the entire packed input, so the shared signed radius is exactly `2*n+1`.
The physical setup includes the stationary transition that stamps rollback
origins and initializes the two scheduler heads.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.IndexedSlot.Source
open IntegerMultiplication TM ScheduleMachine SlotLayout

variable {A Q I : Type}

def lower (n : ℕ) (_ : I) : ℤ := -((2*n+1 : ℕ) : ℤ)
def upper (n : ℕ) (_ : I) : ℤ := ((2*n+1 : ℕ) : ℤ)

theorem widths (I : Type) [Fintype I] (n : ℕ) :
    (∑ j : I, (upper n j+1-lower n j).toNat) ≤ (4*Fintype.card I)*(n+1) := by
  have width (j : I) : (upper n j+1-lower n j).toNat = 4*n+3 := by
    dsimp [upper,lower]
    omega
  simp only [width,Finset.sum_const,Finset.card_univ,smul_eq_mul]
  calc
    Fintype.card I*(4*n+3) ≤ Fintype.card I*(4*(n+1)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

variable (s : Source A Q I) [Fintype I] [DecidableEq I] [DecidableEq A]

noncomputable def physicalDriver :=
  s.driver lower upper
    (SlotBlank.rule (SlotBlank.perm s.blank (literal s.blank))
      (SlotBoot.rule s.blank (SlotInstall.rule s.inp s.idx s.blank))) (some SlotInstall.start)

private def packed (n : ℕ) (x : Input n) := (xbits x).map s.bit ++ [s.sep] ++ (ybits x).map s.bit

omit [Fintype I] [DecidableEq I] [DecidableEq A] in
private theorem packed_length (n : ℕ) (x : Input n) : (packed s n x).length=2*n+1 := by
  simp [packed]
  omega

omit [Fintype I] [DecidableEq A] in
private theorem loaded_input (n : ℕ) (x : Input n) :
    SlotInstall.loaded s.inp s.blank (packed s n x) = s.input n x := by
  funext j
  by_cases h : j=s.inp <;> simp [SlotInstall.loaded,input,initialConfig,h,packed]

omit [Fintype I] [DecidableEq A] in
private theorem plain_input (n : ℕ) (x : Input n) :
    SlotInstall.plain s.inp s.blank (packed s n x) = fun j => unmarked (s.input n x j) := by
  rw [←loaded_input]
  funext j
  unfold SlotInstall.plain SlotInstall.loaded
  apply congrArg (Tape.mk 0)
  funext p
  cases p with
  | negSucc => rfl
  | ofNat k =>
    simp only [Tape.loaded,List.getElem?_map]
    cases (if j=s.inp then packed s n x else [])[k]? <;> rfl

/-- The actual fixed driver reaches the full common scheduler layout in
at most `16*(n+1)` physical transitions. -/
theorem prepare (n : ℕ) (x : Input n)
    (letters : (∀ b, s.bit b ≠ s.blank) ∧ s.sep ≠ s.blank) (distinct : s.idx ≠ s.inp) :
    let d := s.physicalDriver
    ∃ t z, t ≤ 16*(n+1) ∧
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
  obtain ⟨run,stop⟩ := SlotInstall.install s.inp s.idx s.blank w distinct.symm (by omega) clean
  have raw : SlotInstall.loaded s.inp s.blank w = s.input n x := loaded_input s n x
  have plain : SlotInstall.plain s.inp s.blank w = fun j => unmarked (s.input n x j) := plain_input s n x
  rw [plain] at run
  obtain ⟨z,run',stop',ready⟩ := initialize_frame s n x lower upper distinct _ _ run stop (by
    simp only [raw,len,lower,upper])
  exact ⟨_,z,by omega,run',stop',ready⟩

end Uniform.IndexedSlot.Source

end NearSquareRoot
end Computability
end OAI
