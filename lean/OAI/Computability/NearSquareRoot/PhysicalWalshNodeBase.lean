import OAI.Computability.NearSquareRoot.PhysicalWalshNodeSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshBaseField
import OAI.Computability.NearSquareRoot.PhysicalWalshPadding

/-! # Terminal command of the selected-bit Walsh interpreter

Starting with the compact recursion descriptor and the single ordered stream,
the command mints its strided two-bit rulers, evaluates all four-point fibers,
and returns the same compact descriptor with the transformed stream. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code
open PhysicalWalshBase (storedAt ordinalStoredBounded fieldHeader fieldVolume)

theorem flat_size (A : ℕ) (s : Shape) (x : Data s) :
    size (flat A s x) = count A s * (4*(s.w+1)+4)+1 := by
  rw [flat, ← List.map_map, PhysicalWalsh.Padding.marks_size, List.length_map, List.length_range]

theorem base_count (A : ℕ) (s : Shape) (h : s.level=0) : count A s = s.pref*4*s.suff := by
  simp [count,inner,grow,h,Nat.mul_assoc]

/-- The stored result agrees with the guarded recursive semantics on every
occupied ordinal of the terminal piece. -/
theorem base_flat_stored (A : ℕ) (s : Shape) (x : Data s) (zero : s.level=0) (room : baseGuard s x) :
    flat A s (storedAt s.suff x) = flat A s (base s x) := by
  apply List.map_congr_left
  intro n mem
  have hn := List.mem_range.mp mem
  rw [base_count A s zero] at hn
  have hp : n/s.suff/4 < s.pref := (Nat.div_lt_iff_lt_mul (by decide : 0 < 4)).2
    ((Nat.div_lt_iff_lt_mul s.suff_pos).2 hn)
  have h := room ⟨_,hp⟩ ⟨_,Nat.mod_lt n s.suff_pos⟩ ⟨n/s.suff%4,Nat.mod_lt _ (by decide)⟩
  exact congrArg Dusk.mark (PhysicalWalshGrid.packed_eq_rounded _ _ (KernelPassMix.divA_fits _ _ _ h))

private abbrev BaseWire := (Tally × Tally) × Tally

private def keep (z : Header.Wire × List Dusk.Pair) := (z,z.1)
private def returnWire (z : (BaseWire × List Dusk.Pair) × Header.Wire) := (z.2,z.1.2)

/-- One fixed bounded command for any family of terminal calls, retaining the
compact descriptor expected by the recursive caller. -/
theorem baseBounded {I : Type} (A : ℕ) (s : I → Shape) (x : (i : I) → Data (s i))
    (zero : ∀ i, (s i).level=0) (room : ∀ i, baseGuard (s i) (x i)) : ∃ d : ℕ,
    let b i := (count A (s i)+1)*((s i).w+1) + (Header.scale A (s i)+1)^d
    Space.BoundedTask b b (fun i => send (Header.wire A (s i),flat A (s i) (x i)))
      (fun i => send (Header.wire A (s i),flat A (s i) (base (s i) (x i)))) := by
  obtain ⟨d,C,mint⟩ := Header.base_bounded A
  let row i := flat A (s i) (x i)
  let out i := flat A (s i) (base (s i) (x i))
  let hd i := Header.wire A (s i)
  have init := (show Easy keep by unfold keep; fun_prop).on (fun i => (hd i,row i))
  have rulers := ((mint.on s).forget.left (send ∘ row)).left (send ∘ hd)
  have ops := (ordinalStoredBounded (Shape.pref ∘ s) (Shape.suff ∘ s) (Shape.w ∘ s) x).forget
  have step : Task (fieldVolume (Shape.pref ∘ s) (Shape.suff ∘ s) (Shape.w ∘ s))
      (fun i => send (Header.baseHeader (s i),row i))
      (fun i => send (Header.baseHeader (s i),out i)) := by
    have eq (i : I) := base_flat_stored A (s i) (x i) (zero i) (room i)
    unfold flat at eq
    simpa only [fieldHeader,Header.baseHeader,row,out,flat,Function.comp_apply,
      ← base_count A _ (zero _),eq] using ops
  have last := (show Easy returnWire by unfold returnWire; fun_prop).on
    (fun i => ((Header.baseHeader (s i),out i),hd i))
  have chain := ((init.compose rulers).compose (step.left (send ∘ hd))).compose last
  refine ⟨d+1,?_⟩
  apply (Space.BoundedTask.of_time chain).bound (C+60) (C+60) <;> intro i
  all_goals
    have hp := (s i).pref_pos
    have hs := (s i).suff_pos
    have pr := Nat.mul_le_mul_left (s i).pref hs
    have su := Nat.mul_le_mul_right (s i).suff hp
    have pd := Nat.one_le_pow d (Header.scale A (s i)+1) (by omega)
    have pows := Nat.mul_le_mul_right (Header.scale A (s i)+1) pd
    have mon := Nat.mul_le_mul_left ((Header.scale A (s i)+1)^d) (Nat.le_add_left 1 (Header.scale A (s i)))
    have cm := Nat.mul_le_mul_left C mon
    simp only [Nat.mul_one, Nat.one_mul] at pr su pows mon
    have pw := Nat.mul_le_mul_right (s i).w pr
    have sw := Nat.mul_le_mul_right (s i).w su
    have sz : size (Header.wire A (s i)) = Header.scale A (s i) := rfl
    have totalSize : (send (Header.wire A (s i), flat A (s i) (x i))).count =
        size (Header.wire A (s i), flat A (s i) (x i)) := rfl
    simp only [row,out,hd,fieldVolume,Function.comp_apply,totalSize,size_prod,Header.baseHeader,
      size_tally,tally_length,flat_size,base_count A _ (zero i),pow_succ,sz]
    ring_nf at pr su pw sw pows mon cm ⊢
    omega

/-- Terminal transition for a family of legal invocations of the closed
recursive interpreter, expressed in its input/output and allowance types. -/
theorem invocationBaseBounded {I : Type} {a W : ℕ} (hw : 0 < W) (p : KernelPass.Plan (a+1) W W)
    (v : I → Invocation hw p) (zero : ∀ i, (v i).shape.level=0) : ∃ d : ℕ,
    let b i := allowance (a+1) d (v i).shape
    Space.BoundedTask b b (fun i => buffer (a+1) (v i).shape (v i).row)
      (fun i => buffer (a+1) (v i).shape (run hw p (v i).shape (v i).row)) := by
  obtain ⟨d,h⟩ := baseBounded (a+1) (fun i => (v i).shape) (fun i => (v i).row) zero
    (fun i => good_base hw p (zero i) (v i).representable)
  refine ⟨d,?_⟩
  simp only [buffer,run_base hw p _ (zero _)]
  apply h.mono <;> intro i <;> apply Nat.add_le_add_right <;> apply Nat.mul_le_mul_left <;> omega

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
