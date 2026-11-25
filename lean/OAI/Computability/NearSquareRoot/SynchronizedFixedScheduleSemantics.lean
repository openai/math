import OAI.Computability.NearSquareRoot.SynchronizedFixedSchedule
import OAI.Computability.NearSquareRoot.SynchronizedFixedSemantics
import OAI.Computability.NearSquareRoot.SynchronizedScheduleStages

/-! # Fourier action of the synchronized physical instruction stream

The polynomial-time schedule generator operates on the unary radix exponents
alone. Interpreting its rows with the calibrated tables for the requested
moduli gives the full tensor of restored local Fourier transforms.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedLayers.ScheduleProgram

open IntegerMultiplication.Code ShortFourier ShortFourier.AxisWord SynchronizedPadding

/-- The two interpretations of an emitted opcode agree on its physical slot. -/
theorem fixedSlot_kind_of_mem {a k : ℕ} [NeZero a] {x : Inst} (hx : x ∈ fixedWord (tally k)) :
    (fixedSlot a k x).kind = instructionKind x := by
  have hn := fixedWord_tag_ne_fourteen _ hx
  rw [fixedSlot_kind, instructionKind]
  split_ifs <;> first | rfl | omega

/-- Matrix of a serialized row using the per-axis tables and the designated
half selector at each block. -/
noncomputable def radixRowMatrix {n : ℕ} (a k : Fin n → ℕ) [∀ i, NeZero (a i)] (r : Row Inst) :=
  rowMatrix (fun i x => (fixedSlot (a i) (k i) x).matrix dilationAddress) r

/-- The word emitted by the fixed setup machine computes the normalized
transform on each participating fiber and the identity on its borrowed cells. -/
theorem radixPlan_correct {n : ℕ} (a k : Fin n → ℕ) [∀ i, NeZero (a i)] (L : ℕ)
    (hk : ∀ i, k i ≤ L) (hr : ∀ i, 2 * a i - 1 ≤ 2 ^ k i) (har : ∀ i, a i ≤ 2 ^ k i) :
    let rows := radixPlan (List.ofFn (fun i => tally (k i)), tally L)
    (rows.map (radixRowMatrix a k)).prod =
        tensorMatrix (fun i => extend (activeFiber (har i)) (normalizedFourier (a i))) ∧
      (∀ r ∈ rows, GlobalStage (fun i => dilationAddress (ι := Fin (2 ^ k i))) (radixRowMatrix a k r)) ∧
        rows.length = 54 * (1032 * L + 1549) := by
  let w (i : Fin n) := fixedWord (tally (k i))
  let D := (radixBudget (tally L)).length
  have hd (i : Fin n) : (w i).length ≤ D := by
    apply (fixedWord_length_le _).trans
    have hi := hk i
    simp [D]
    omega
  have hs := plan_correct instructionKind (fun i => dilationAddress (ι := Fin (2 ^ k i)))
    (fun i x => (fixedSlot (a i) (k i) x).matrix dilationAddress) w hd
    (fun i x hx => ⟨fixedSlot (a i) (k i) x, fixedSlot_kind_of_mem hx, rfl⟩)
  have he : radixPlan (List.ofFn (fun i => tally (k i)),tally L) =
      plan instructionKind (List.ofFn w,tally D) := by
    simp only [radixPlan, List.map_ofFn, D, recover_tally]
    rfl
  dsimp only
  refine ⟨?_, ?_, by simp [radixPlan_length]⟩
  · rw [he]
    calc
      _ = tensorMatrix (fun i => ((w i).map (fun x => (fixedSlot (a i) (k i) x).matrix dilationAddress)).prod) := hs.1
      _ = _ := congrArg tensorMatrix (funext (fun i => fixedWord_correct (hr i) (har i)))
  · rw [he]
    exact hs.2.1

end SynchronizedLayers.ScheduleProgram

end NearSquareRoot
end Computability
end OAI
