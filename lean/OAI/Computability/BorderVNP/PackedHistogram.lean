import OAI.Computability.BorderVNP.PackedHistogramNetwork
import Mathlib.Order.Preorder.Finite

/-! # Deterministic simultaneous weighted bucket queries

The first sort orders by address and source/query tag. The running total is
then copied beside its unique original ordinal, and the second sort returns
it to that ordinal. This is valid for repeated requests and empty buckets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistogram

open ParseBatchLookup ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork

variable {b k w : ℕ}

private theorem restore {σ : Type*} [Fintype σ] (f : Frame σ (Pins b (w+b))) (x : σ → Bool)
    (π : Equiv.Perm (Fin (2^b))) (v : Fin (2^b) → Fin w → Bool)
    (hw : ∀ i j, f.eval x (i,j) = prepend ((numberWords b).symm (π i)) (v i) j)
    (i : Fin (2^b)) (d : Fin w) :
    (phases b le_rfl f).eval x (i,lowPin b d) = v (π.symm i) d := by
  obtain ⟨τ, ht⟩ := phases_order f x
  have get (l j) : (phases b le_rfl f).eval x (l,j) =
      prepend ((numberWords b).symm (π (τ l))) (v (τ l)) j := (ht l j).trans (hw _ _)
  have hmono : Monotone fun l => π (τ l) := by
    intro l m hlm
    have h := Nat.div_le_div_right (c := 2^w) (phases_monotone f x hlm)
    simp only [get, ordinal_of_return, value_encode] at h
    exact h
  have hid := (hmono.strictMono_of_injective (π.injective.comp τ.injective)).eq_id
  have hτ : τ i = π.symm i := π.eq_symm_apply.mpr (congrFun hid i)
  simpa only [prepend_low, hτ] using get i (lowPin b d)

/-- Under a per-bin capacity bound, each query in the original row order receives the
sum of all source weights at its address. Addresses and values may depend on input bits. -/
theorem frame_value (x : Raw b k w → Bool)
    (zero : ∀ u, isQuery x u = true → weightValue x u = 0)
    (fits : ∀ a, bucket (keyValue x) (weightValue x) a < 2^w)
    (i : Fin (2^b)) (query : isQuery x i = true) :
    value (fun j => (frame b k w).eval x (i,j)) =
      bucket (keyValue x) (weightValue x) (keyValue x i) := by
  let first := phases b le_rfl (expanded b k w)
  let s := first.eval x
  obtain ⟨π, hπ⟩ := phases_order (expanded b k w) x
  have wire (l j) : s (l,j) = rawWord x (π l) j := (hπ l j).trans (expanded_eval x _ _)
  let ks := PackedScan.read s (addressWires b k w)
  let ws := PackedScan.read s (weightWires b k w)
  let flag := isQuery x ∘ π
  have key (l : Fin (2^b)) : ks l.val = keyValue x (π l) := by
    simp [ks, PackedScan.read, addressWires, Function.comp_def, wire, rawWord, keyValue]
  have weight (l : Fin (2^b)) : ws l.val = weightValue x (π l) := by
    simp [ws, PackedScan.read, weightWires, Function.comp_def, wire, rawWord, weightValue]
  have order : Monotone (fun l : Fin (2^b) => 2*ks l.val + (flag l).toNat) := by
    intro l m hlm
    have h := Nat.div_le_div_right (c := 2^(w+b)) (phases_monotone (expanded b k w) x hlm)
    change value (fun j => s (l,j)) / 2^(w+b) ≤ value (fun j => s (m,j)) / 2^(w+b) at h
    simpa only [wire, rawWord, record, bits_key, key, keyValue, flag, Function.comp_apply] using h
  have bins (a : ℕ) : bucket (fun l : Fin (2^b) => ks l.val) (fun l => ws l.val) a =
      bucket (keyValue x) (weightValue x) a := by
    simpa only [Function.comp_def, key, weight] using bucket_perm (keyValue x) (weightValue x) π a
  have hf (j : ℕ) (hj : j < 2^b) : PackedScan.segmentTotal ks ws j < 2^w := by
    let l : Fin (2^b) := ⟨j,hj⟩
    have h := segment_le_bucket ks ws (key_mono _ flag order) l
    rw [bins] at h
    exact lt_of_le_of_lt h (fits _)
  let v := fun l : Fin (2^b) => fun d : Fin w => (totals b k w).eval s (l,d)
  have ret (l j) : (returnRows b k w).eval x (l,j) =
      prepend ((numberWords b).symm (π l)) (v l) j := by
    rw [returnRows, Frame.subst_eval, returnBlock_eval]
    change prepend (fun d => s (l,ordinalPin k w d)) (v l) j = _
    simp only [wire, rawWord, record_ordinal]
  have returned (j : Fin w) : (frame b k w).eval x (i,j) = v (π.symm i) j := by
    rw [frame, Frame.select_eval]
    exact restore _ x π v ret i j
  simp only [returned]
  change value (fun d => (PackedScan.scan _ _ _).eval s (π.symm i,d)) = _
  rw [PackedScan.scan_value _ _ _ s hf (π.symm i)]
  change PackedScan.segmentTotal ks ws (π.symm i).val = _
  have hq : flag (π.symm i) = true := by simpa [flag] using query
  have hz (l : Fin (2^b)) (hl : flag l = true) : ws l.val = 0 := (weight l).trans (zero _ hl)
  rw [segment_eq_bucket ks ws flag order hz _ hq, bins, key, π.apply_symm_apply]

end PackedHistogram

end BorderVNP
end Computability
end OAI
