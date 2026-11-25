import OAI.Computability.NearSquareRoot.InterchangeBoundedFatRecursion
import OAI.Computability.NearSquareRoot.InterchangeNodeSpace
import OAI.Computability.NearSquareRoot.InterchangeBoundedMain

/-! # The physical recursive interchange of two radix fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open Filter IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeFrame
  NearSquareRoot.Interchange NearSquareRoot.Interchange.StageKernel

private theorem wide_bank (p k m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) : 3 ≤ bankWidth p k m := by
  let N := Fintype.card (HammingLabels p k)
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨fun _ _ => ⟨0,by positivity⟩⟩
  have lead : 3 ≤ 2^m := (by decide : 3 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) hm)
  have side : 0 < (SwapRepair.order m)^OAI.LinearAlgebra.FiniteFourier.primeClockDigits 2 m (SwapRepair.order m) := by
    unfold SwapRepair.order OAI.LinearAlgebra.FiniteFourier.countPencilOrder
    positivity
  have basis : 0 < componentWidth m := by
    simp only [componentWidth,SwapRepair.BasisIndex,Fintype.card_fin]
    positivity
  exact (((lead.trans (Nat.le_mul_of_pos_right _ side)).trans
    (Nat.le_mul_of_pos_right _ basis)).trans (Nat.le_mul_of_pos_right _ hN))

/-- At the selected fixed radix and ground field, one recursive tape command
interchanges every pair of equal-width fields with bounded spectator radices,
including all inputs above the common payload-padding threshold, with linear
peak stack space. Each ground-field digit has a fixed injective representation. -/
theorem exists_bounded_radix_interchange {α : ℝ} (hα : 1/2 < α) (threshold : ℕ) :
    ∃ p b : ℕ, p.Prime ∧ 2 < p ∧ b.Prime ∧ threshold < b ∧
      ∀ digit : ZMod p → Tree, Function.Injective digit → ∃ k : ℕ,
        Space.BoundedTask (fun x : ThickRequest (b:=b) (Packed digit) k =>
            ⌈(x.val.recordVolume : ℝ) * (x.val.width : ℝ)^α⌉₊)
          (fun x => x.val.recordVolume)
          (fun x => (job b).issue x.val) (fun x => (job b).reply x.val) := by
  let γ : ℝ := (α+1/2)/2
  obtain ⟨p,hp,odd,select⟩ := exists_configured_batch
    (show 1/2 < γ from by dsimp [γ]; linarith) (show γ < α from by dsimp [γ]; linarith)
  let := hp
  obtain ⟨m,sel,hm⟩ := (select.and (eventually_ge_atTop (2:ℕ))).exists
  obtain ⟨k,K,atlas,radix⟩ := sel
  let a := hammingReserve p k
  let W := bankWidth p k m
  obtain ⟨b,hb,big,_,_,⟨frame⟩,_,contract⟩ := radix threshold ∅
  let : NeZero b := ⟨hb.ne_zero⟩
  have above : W < b := (le_max_right _ _).trans_lt big
  have base : 2 ≤ b := hb.two_le
  let n := positions a m
  have hn : 0 < n := by dsimp [n,positions]; omega
  let C := K.calls atlas
  let θ : ℝ := (↑(C*BatchRows.groups b W) : ℝ)/b + (2*a:ℕ)
  have theta : θ < (m:ℝ)^α := by
    simpa only [θ,W,C,a,bankWidth,Nat.cast_mul,Nat.cast_ofNat] using contract
  refine ⟨p,b,hp.out,odd,hb,(le_max_left _ _).trans_lt big,?_⟩
  intro digit injective
  let valid := Packed (b:=b) digit
  let I := Internal valid n
  let xs (i : I) := i.val.val
  have ins (i : I) : n < (xs i).width := i.property
  have ok (i : I) : valid (xs i) := i.val.property
  have all := packed_manifest digit (fun a : Subtype valid => a.val) (fun a => a.property)
  apply close_bounded_fat_recursion valid base (fun _ h => h.1) (fun _ h => h.2.1) all m n α θ
    (by omega) (by dsimp [n,positions]; omega) (by linarith) (by dsimp [θ]; positivity) theta
  apply internal_bounded_ledger a m xs digit W C (wide_bank p k m hm) above hn ins ok
  have hp' := (shapes_told xs fun i => (ok i).1).1
  have hs := center_told xs base (fun i => (ok i).1) n
  intro v hv good
  exact K.bounded_main_admissible frame (fun i => (xs i).before) (aisle a m xs) (south a m xs) (localWidth a m xs)
    above (lane_has xs n) hp' hs.2.1 hs.2.2 (fun i => Series.natural (xs i).recordWidth)
    (by simp) digit injective v hv good

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
