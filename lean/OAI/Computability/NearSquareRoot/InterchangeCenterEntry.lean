import OAI.Computability.NearSquareRoot.InterchangeCenterBody

/-! # Local entry into a mixed-volume recursive interchange

A local tape program returns before the centered operation begins. Its
temporary work is charged only to the local side of the peak bound.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace.CenterBody

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom
  NearSquareRoot.Space

/-- Prepend a local transformation while preserving the exact recursive
ledgers and the full-volume parking allowance. -/
theorem preceded {I X : Type} {r : Regime I} {n l park : I → ℕ} {job : Job X}
    {small full : I → List X} {input center output : I → Tree}
    (h : CenterBody r n l job small full park center output)
    (entry : Rip r n l input center) : CenterBody r n l job small full park input output := by
  obtain ⟨k,C,cmd,run⟩ := h.build
  obtain ⟨j,p,E,pre⟩ := rip_bounded entry
  refine ⟨max j k,E+C+3,p.join cmd,?_⟩
  intro i parent env time data depth ih deck base hc
  let M := massNat r n l (max j k) i + 1
  let L := (E+C+3)*M
  let T := E*(massNat r n l j i+1)
  let S := C*(massNat r n l k i+1)
  have hj := Nat.mul_le_mul_left E (Nat.add_le_add_right (massNat_mono r n l (le_max_left j k) i) 1)
  have hk := Nat.mul_le_mul_left C (Nat.add_le_add_right (massNat_mono r n l (le_max_right j k) i) 1)
  have cost : T + S + 2 ≤ L := by
    change E*(massNat r n l j i+1) + C*(massNat r n l k i+1) + 2 ≤ (E+C+3)*M
    change _ ≤ E*M at hj
    change _ ≤ C*M at hk
    have : 1 ≤ M := Nat.succ_pos _
    rw [Nat.add_mul,Nat.add_mul]
    omega
  have s : S ≤ L := by omega
  have tp : T + 1 ≤ L := by omega
  have raw := pre i (parent::env) deck base hc
  let cap := max (L + childPeak data (small i)) (park i + childPeak data (full i))
  let ret := max (L + childPeak depth (small i)) (1 + childPeak depth (full i))
  have hdata : L ≤ cap := (Nat.le_add_right ..).trans (le_max_left ..)
  have hret : L ≤ ret := (Nat.le_add_right ..).trans (le_max_left ..)
  have left := raw.mono le_rfl (Nat.add_le_add_left (show T ≤ cap by omega) base) le_rfl
  have right := (run i parent env time data depth ih deck base hc).mono le_rfl
    (Nat.add_le_add_left (max_le_max_right _ (Nat.add_le_add_right s _)) base)
    (max_le_max_right _ (Nat.add_le_add_right s _))
  exact (left.join right (show T+1 ≤ ret from tp.trans hret)).mono (by
    change T + (S + _) + 2 ≤ L + _
    omega) le_rfl le_rfl

end InterchangeSpace.CenterBody

end NearSquareRoot
end Computability
end OAI
