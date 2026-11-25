import OAI.Computability.NearSquareRoot.PrecisionMixedPass
import OAI.Computability.NearSquareRoot.PrecisionGridStreamTask
import OAI.Computability.NearSquareRoot.PrecisionPhaseAddress
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # A tensor diagonal from its local tables

A single framed program expands all the tensor coefficients and consumes that
stream in a mixed-width product pass. The exact diagonal entries below are
ordered by the same lexicographic address traversal as the tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedPoint

open IntegerMultiplication Code PhaseStream

variable {I α : Type} (k d : I → ℕ) (t : I → ℕ → List α)
    (store : (i : I) → α → Record (guardedK (k i)))
    (x : (i : I) → PhaseAddress k i → Record (k i))

def tensorTableQuery (i : I) : Tree := .fork
  (send ((List.range (d i)).map fun j =>
    tableWords (fractionBits (guardedK (k i))) ((t i j).map (store i))))
  (send (prefixWords [digitRecord (guardedK (k i)) 1]))

def tensorPassQuery (i : I) : Tree := .fork
  (send (List.ofFn fun j => Dusk.mark (x i j)))
  (tensorTableQuery k d t store i)

/-- The emitted data array approximates exactly the tensor of the unit phases
in the local tables. The time includes construction of every coefficient and
the peak space covers both streamed arrays and the scalar multiplier's scratch. -/
theorem tensorPass (ideal : I → α → ℂ) (hk : ∀ i, 1 ≤ k i)
    (hd : ∀ i, d i ≤ k i) (ht : ∀ i j, j < d i → 2 ≤ (t i j).length)
    (hbox : ∀ i, ((List.range (d i)).map (fun j => (t i j).length)).prod = 2 ^ k i)
    (hunit : ∀ i j, j < d i → ∀ a ∈ t i j, ‖ideal i a‖ = 1)
    (herr : ∀ i j, j < d i → ∀ a ∈ t i j,
      ‖value _ (store i a) - ideal i a‖ ≤ 1 / (2 : ℝ) ^ (70 * guardedK (k i)))
    (hx : ∀ i, ‖recordArray (x i)‖ ≤ (2 : ℝ)^(13*k i)) :
    ∃ (out : (i : I) → PhaseAddress k i → Record (k i))
      (phase : (i : I) → PhaseAddress k i → ℂ) (hu : ∀ i j, ‖phase i j‖ = 1),
      (∀ i, List.ofFn (phase i) =
        (addresses ((List.range (d i)).map (t i))).map (fun xs => (xs.map (ideal i)).prod)) ∧
      Space.BoundedTask (fun i => (2^k i+1)*GridTask.recordCost (k i))
        (fun i => (2^k i+1)*(k i+1)) (tensorPassQuery k d t store x)
        (fun i => send (List.ofFn fun j => Dusk.mark (out i j))) ∧
      ∀ i, ‖recordArray (out i) - phaseLayerIsometry (phase i) (hu i) (recordArray (x i))‖ ≤
        1 / (2 : ℝ)^(50*k i) := by
  let records i := phaseStreamRecords (k i) (t i) (store i) (d i)
  let targets i := (addresses ((List.range (d i)).map (t i))).map (fun xs => (xs.map (ideal i)).prod)
  have hr i : (records i).length = 2 ^ k i := (phaseStreamRecords_count ..).trans (hbox i)
  obtain ⟨⟨run,_⟩,matchRows⟩ := physicalPhaseStream k d t store ideal hd ht hunit herr
  change ∀ i, List.Forall₂ _ (records i) (targets i) at matchRows
  have hp i : (targets i).length = 2 ^ k i := (matchRows i).length_eq.symm.trans (hr i)
  let coeff i := indexed (records i) (hr i)
  let phase i := indexed (targets i) (hp i)
  have hu i j : ‖phase i j‖ = 1 := by
    have hmem : phase i j ∈ targets i := List.getElem_mem _
    obtain ⟨xs,hs,rfl'⟩ := List.mem_map.mp hmem
    rw [← rfl']
    apply norm_tensor_entry _ _ _ hs
    intro table htable a ha
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp htable
    exact hunit i l (List.mem_range.mp hl) a ha
  refine ⟨phaseOutput k x coeff, phase, hu, fun i => ofFn_indexed .., ?_, ?_⟩
  · let data i := send (List.ofFn fun j => Dusk.mark (x i j))
    let raw i := send (prefixWords (records i))
    let formed i := Tree.fork (data i) (raw i)
    have endpt i : formed i = send (List.ofFn (fun j => Dusk.mark (x i j)), List.ofFn (fun j => Dusk.mark (coeff i j))) := by
      dsimp only [formed, data, raw, prefixWords]
      have he : (records i).map Dusk.mark = List.ofFn (fun j => Dusk.mark (coeff i j)) := calc
        _ = (List.ofFn (coeff i)).map Dusk.mark := congrArg _ (ofFn_indexed ..).symm
        _ = _ := List.map_ofFn
      rw [he]
      rfl
    have generate := run.right data
    have app := phasePassSeparate k x coeff
    rw [← funext endpt] at app
    have both := generate.compose app
    unfold tensorPassQuery
    apply both.bound 1000 1000
    · intro i
      have hw := ProductPass.streamSize (fun j => Dusk.mark (x i j))
        (fun j => (record_size _ _).le)
      change size (List.ofFn _) ≤ _ at hw
      have hc := GridTask.width_le_recordCost (k i)
      change (data i).count + (records i).length * _ + _ + 1 ≤ _
      change (data i).count ≤ _ at hw
      rw [hr]
      nlinarith only [hw, Nat.mul_le_mul_left (2 ^ k i + 1) hc,
        Nat.one_le_pow (k i) 2 (by decide), hc, Nat.zero_le (2 ^ k i)]
    · intro i
      have hw := ProductPass.streamSize (fun j => Dusk.mark (x i j))
        (fun j => (record_size _ _).le)
      change (data i).count ≤ _ at hw
      change max ((records i).length * (k i+1) + GridTask.recordCost (k i) +
        (data i).count) _ + 1 ≤ _
      apply (Nat.add_le_add_right (max_le (b := (2^k i+1)*(k i+1))
        (c := 999*((2^k i+1)*(k i+1)+1)) ?_ ?_) 1).trans (by omega)
      · rw [hr]
        have hscratch := phasePeak_on_box (k i)
        nlinarith only [hw, hscratch, Nat.zero_le (2^k i * (k i+1))]
      · omega
  · intro i
    apply applyPhase_error (hk i) (Fintype.card_fin _) _ _ _ (hu i) (hx i)
    exact fun j => indexed_rel (matchRows i) (hr i) j

end FixedPoint

end

end NearSquareRoot
end Computability
end OAI
