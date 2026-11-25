import OAI.Computability.NearSquareRoot.PrecisionLayerReadout
import OAI.Computability.NearSquareRoot.PrecisionDigitInput
import OAI.Computability.NearSquareRoot.PrecisionRulers
import OAI.Computability.NearSquareRoot.BoundedProgram

/-! # Readout from the original length ruler and the inverse-routed grid

The length header is re-encoded in binary to calculate the logarithmic radix
and address widths. All four readout rulers are produced in the linear budget,
with the array parked alongside the operation. The same program then compacts
the grid and emits the exact fixed-width product.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate

open IntegerMultiplication Code Bits Brief DigitPacking FixedPoint
open ResidueFourier SynchronizedPadding

noncomputable section

/-- The stack cost and the serialized input volume together bound stack height
and frame depth throughout a linear-time readout. -/
private theorem linearBounded {I : Type} (n : I → ℕ) {q r : I → Tree}
    (h : Carries (measure n) q r) : Space.BoundedTask n n q r := by
  obtain ⟨_,b,run,C,hC⟩ := h.runs
  have task := run.bound (b' := n) C fun i => by
    have hh := hC i
    change (b i : ℝ)+1 ≤ C*((n i : ℝ)+1) at hh
    exact_mod_cast hh
  obtain ⟨D,hD⟩ := h.small
  apply (Space.BoundedTask.of_time task).bound 1 (D+1)
  · intro i; simp
  · intro i
    have hh := hD i
    change ((q i).count : ℝ) ≤ D*((n i : ℝ)+1) at hh
    have hh' : (q i).count ≤ D*(n i+1) := by exact_mod_cast hh
    rw [Nat.add_mul]; omega

private def rulers (n : ℕ) : Tally × Tally × Tally × Tally :=
  (tally (addressBits n), tally n, tally (width n), tally (fractionBits (addressBits n)))

private theorem makeRulers {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Carries (measure n) (fun i => send (tally (n i))) (fun i => send (rulers (n i))) := by
  have volume : Volume (measure n) (fun i => send (tally (n i))) := by
    refine ⟨3, fun i => ?_⟩
    change (size (tally (n i)) : ℝ) ≤ 3*((n i : ℝ)+1)
    rw [size_tally,tally_length]
    push_cast; linarith
  have binary : Carries (measure n) (fun i => send (tally (n i))) (journals n).header := by
    have h := Carries.func (y := fun i => tally (n i)) (here n) volume _ Carry.easy_chart
    change Carries _ _ (fun i => send (Carry.born (n i)))
    simpa only [tally_length] using h
  have radix := Strip.Regime.Small.cooked (wealthy n) (guide_city n).amount_.short_log
  have radix' := radix.times (here n) 8 (fun i => by
    have h := Param.load_below (n i)
    have g := Param.amount_l (n i)
    change ((Param.load (n i) : ℕ) : ℝ) ≤ 8*((n i : ℝ)+1)
    exact_mod_cast (by omega : Param.load (n i) ≤ 8*(n i+1)))
  have b : Carries (measure n) (fun i => send (tally (n i))) (fun i => send (tally (width (n i)))) :=
    binary.chain radix'
  have k := binary.chain (header_addressBits n hn)
  have p := k.chain (Carries.func (y := fun i => tally (addressBits (n i))) (here n) k.out
    _ (easyAffine 70 1))
  simp only [affine_tally] at p
  exact k.twice ((Carries.idles (here n) volume).twice (b.twice p))

private def attachRecords (z : (Tally × Tally × Tally × Tally) × List Dusk.Pair) :=
  (z.1.1, z.1.2.1, z.1.2.2.1, z.1.2.2.2, z.2)

private theorem rowsVolume {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (v : (i : I) → Fin (capacity (n i)) → Record (addressBits (n i))) :
    Volume (measure n) (fun i => send (List.ofFn (fun j => Dusk.mark (v i j)))) := by
  refine ⟨20000,fun i => ?_⟩
  change (size _ : ℝ) ≤ 20000*((n i : ℝ)+1)
  have sizeRows := markedListSize (List.ofFn (v i))
  rw [List.map_ofFn, List.length_ofFn] at sizeRows
  simp only [Function.comp_def] at sizeRows
  rw [sizeRows]
  have hk : 1 ≤ addressBits (n i) := by
    have := width_pos (hn i)
    have := width_le_twice_addressBits (hn i)
    omega
  have hc := (packed_volume (hn i)).2
  have hs := (Nat.mul_le_mul_left (capacity (n i)) hk : _)
  rw [Nat.mul_one] at hs
  exact_mod_cast (show capacity (n i)*(4*(componentBits (addressBits (n i))+1)+4)+1 ≤
      20000*(n i+1) by unfold componentBits; nlinarith)

/-- Compute and attach all rulers from the input length while retaining the
complete marked inverse-routed record list. -/
theorem prepareReadout {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (v : (i : I) → Fin (capacity (n i)) → Record (addressBits (n i))) :
    Carries (measure n) (fun i => send (tally (n i), List.ofFn (fun j => Dusk.mark (v i j))))
      (fun i => send (tally (addressBits (n i)), decodePacket (n i) (width (n i))
        (fractionBits (addressBits (n i))) (v i))) := by
  let data i := List.ofFn (fun j => Dusk.mark (v i j))
  have hdr := (makeRulers n hn).first (rowsVolume n hn v)
  have pack : Easy attachRecords := by unfold attachRecords; fun_prop
  exact hdr.chain (Carries.func (y := fun i => (rulers (n i), data i)) (here n) hdr.out _ pack)

/-- One bounded readout command uses only the unary input length and the
post-inverse-routing grid. The word is in most-significant-first order. -/
theorem readout {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hv : ∀ i, ValidDirectory (addressBits (n i))) (x y : I → Word)
    (v : (i : I) → Fin (capacity (n i)) → Record (addressBits (n i)))
    (hx : ∀ i, (x i).length = n i) (hy : ∀ i, (y i).length = n i)
    (layers : ∀ i,
      let box := CoprimeBox.box (addressBits (n i))
      letI := BoxFin.modulus_neZero (hv i)
      letI : NeZero (boxVolume box) := ⟨Finset.prod_ne_zero_iff.mpr fun j _ => NeZero.ne (BoxFin.modulus box j)⟩
      ∃ F J : ProductRecovery.Layers (PaddedBox (BoxFin.modulus box) (BoxFin.padding box)) (addressBits (n i)),
        F.Approximates (paddedIsometry _ _).toLinearIsometry ∧
        J.Approximates (paddedIsometry _ _).symm.toLinearIsometry ∧
        v i = scaledLayerRecords (hv i) F J (x i) (y i)) :
    ∃ z : I → Word, (∀ i, (z i).length = 2*n i ∧ bitValue (z i) = bitValue (x i)*bitValue (y i)) ∧
      Space.BoundedTask n n
        (fun i => send (tally (n i), List.ofFn (fun j => Dusk.mark (afterInverseCRT (hv i) (v i) j))))
        (fun i => send (z i)) := by
  obtain ⟨z,hz,task,_⟩ := packedLayerToProduct n hn hv x y v hx hy layers
  refine ⟨z,hz,linearBounded n ?_⟩
  apply (prepareReadout n hn (fun i => afterInverseCRT (hv i) (v i))).sequence
  refine ⟨here n, n, task, 1, fun i => ?_⟩
  simp [Brief.measure]

end
end FixedCandidate

end NearSquareRoot
end Computability
end OAI
