import OAI.Computability.VPVNP.CompressorPayloadCall
import OAI.Computability.VPVNP.PrimedCounterKernel
import OAI.Computability.VPVNP.LiveEvaluatorRAM

/-!
# Execution time of the stored motif choice

A successful stored payload call fits the published fuel bound from any register
file, memory and public input. The word reader runs its loop once per bit.
The remaining instructions are straight-line code apart from the dispatch on
zero repetitions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PayloadWrite

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM
open MotifChoiceRAM LiveEvaluatorRAM

variable {n w : ℕ}

private theorem guess_exec_length {r k : ℕ} (reg : Fin 3 ↪ Fin r)
    {pub : Fin k → Word w} {st rs m es out mem}
    (h : Flow.Exec pub st (PrimedCounter.GuessWord.flow reg) rs m es out mem) :
    es.length ≤ 4*w+4 := by
  let o : Output w r := ⟨es, out, mem, []⟩
  have hg := (guess_kernel_exec (w := w) (k := k) reg (bits := choiceBits es) (o := o)).mpr
    ⟨h, (List.append_nil _).symm⟩
  exact (guess_refine reg).bounded hg

private theorem coordinate_exec_length (i : Fin n) {pub : Fin n → Word w} {st rs m es out mem}
    (h : Flow.Exec pub st (coordinate i) rs m es out mem) : es.length ≤ 4*w+10 := by
  cases h with
  | seq guess compute =>
    have hg := guess_exec_length _ guess
    have hc := length_le_of_loopFree compute rfl
    change _ ≤ 6 at hc
    rw [List.length_append]
    omega

private theorem scan_exec_length (is : List (Fin n)) {pub : Fin n → Word w} {st rs m es out mem}
    (h : Flow.Exec pub st (scan is) rs m es out mem) : es.length ≤ is.length*(4*w+10)+1 := by
  induction is generalizing rs m es with
  | nil =>
    change Flow.Exec _ _ (.line _) _ _ _ _ _ at h
    cases h
    simp
  | cons i is ih =>
    cases h with
    | seq coord rest =>
      have hc := coordinate_exec_length i coord
      have hr := ih rest
      rw [List.length_append, List.length_cons, Nat.succ_mul]
      omega

private theorem prepareBounds_loopFree (d factor denominator : ℕ) :
    loopFree (prepareBounds d factor denominator) = true := by
  have digits {r k : ℕ} (dst src : Fin r) (bs : List Bool) :
      loopFree (scaleDigits (k := k) dst src bs) = true := by
    induction bs with
    | nil => rfl
    | cons b bs ih => cases b <;> simp [scaleDigits, loopFree, ih]
  simp [prepareBounds, scaleFixed, loopFree, digits]

private theorem unitSlots_loopFree {n : ℕ} (is : List (Fin n)) :
    loopFree (unitSlots is) = true := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [unitSlots, loopFree, ih]

private theorem unitSlots_length {n : ℕ} (is : List (Fin n)) :
    (unitSlots is).length = is.length + 1 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp [unitSlots, Flow.length, ih]; omega

private theorem writePayload_loopFree (n : ℕ) : loopFree (writePayload n) = true := by
  have slots (is : List (Fin n)) : loopFree (writeSlots is) = true := by
    induction is with
    | nil => rfl
    | cons i is ih => simp [writeSlots, loopFree, ih]
  simp [writePayload, loopFree, slots]

private theorem writePayload_length (n : ℕ) : (writePayload n).length = 2*n+3 := by
  have slots (is : List (Fin n)) : (writeSlots is).length = 2*is.length+1 := by
    induction is with
    | nil => rfl
    | cons i is ih => simp [writeSlots, Flow.length, ih]; omega
  simp [writePayload, Flow.length, slots]; omega

private theorem choosePayload_exec_length {pub : Fin n → Word w} {st rs m es out mem}
    (h : Flow.Exec pub st (choosePayload n) rs m es out mem) : es.length ≤ n*(4*w+10)+2 := by
  cases h with
  | ifEqYes _ unit =>
    have hu := length_le_of_loopFree unit (unitSlots_loopFree _)
    rw [unitSlots_length, List.length_finRange] at hu
    have hn := Nat.le_mul_of_pos_right n (show 0 < 4*w+10 by omega)
    rw [List.length_cons]
    omega
  | ifEqNo _ scan =>
    have hs := scan_exec_length _ scan
    rw [List.length_finRange] at hs
    rw [List.length_cons]
    omega

open MotifGrid MotifBlocks MotifConversion MotifSelector

variable {k : Type*} [Field k] {J D S : Type} [Fintype J] [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}

/-- Every finite execution of the stored choice fits the standalone call's fuel,
including the fuel unit needed at its accept continuation. -/
theorem storedCall_exec_length_lt (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')
    {pub : Fin n → BurstRAM.Word w} {base rs m es out mem}
    (run : Flow.Exec pub base (storedCall n (B.scale*B.radius.num.natAbs) (MotifAdmission.denominator q))
      rs m es out mem) : es.length < storedFuel B n w := by
  cases run with
  | seq setup store =>
    cases setup with
    | seq load prep =>
      cases store with
      | seq choose write =>
        have hl := length_le_of_loopFree load rfl
        change _ ≤ 4 at hl
        have hp := length_le_of_loopFree prep (prepareBounds_loopFree ..)
        have hc := choosePayload_exec_length choose
        have hw := length_le_of_loopFree write (writePayload_loopFree _)
        rw [writePayload_length] at hw
        simp only [List.length_append]
        change _ < (4+(prepareBounds n (B.scale*B.radius.num.natAbs) (MotifAdmission.denominator q)).length) +
          (n*(4*w+10)+3+(2*n+3))
        omega

end CompressorRecords.PayloadWrite

end VPVNP
end Computability
end OAI
