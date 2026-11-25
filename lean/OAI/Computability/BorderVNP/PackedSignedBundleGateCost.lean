import OAI.Computability.BorderVNP.PackedSignedBundleOutput
import OAI.Computability.BorderVNP.PackedBundleHeaderBankCost
import OAI.Computability.BorderVNP.PackedTerminalSignedHeaderDepth

/-! # Total gate charge when the two resident bundle banks follow the signed packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Retained

open Crossing Packing Packing.BottomReports RoutingISA VPVNP.VerifierNetwork CellAddressCircuit

variable {Γ σ : Type} [Fintype Γ] [Fintype σ] {s m n d k w J o H E A ctl R : ℕ}
    (Fst : Frame Γ (Fin o × Fin w)) (src : Frame Γ σ)
    (banks : CellBanks.Layout) (F : Fields s m n banks.cells d k w σ)
    (old : Fin J → Fin s) (desc gap : ℕ) (shapes : Fin J → BundleSort.Shape)
    (ready : σ)

local notation "b" => BundleSort.markedDepth banks.cells J
local notation3 (prettyPrint := false) "head₀" => BundleSort.headerBanks banks F b old desc gap shapes (Frame.initial (fun _ : Unit => ready))

/-- Joint emitted gates and bits, including the second physical evaluation
of the staged field bus used by the header banks. No previous-output lookup
is charged to the clock a second time. -/
theorem appendBundle_charge (hpos : 1 ≤ H) (sizeW : w = H^(E+2))
    (rows : 1+count s m n banks.cells+J+n ≤ R)
    (widths : d ≤ w ∧ k ≤ w ∧ Nat.clog 2 R ≤ w)
    (prefixCost : Fst.size+o*w ≤ (8*(11920000+16008100*A+ctl))*R*H^(4*(E+2)))
    (sourceCost : src.size ≤ 433004*R*(w+1)^3) :
    (appendWords Fst ((head₀).subst src)).size+(o+(2^b+2^b))*w ≤
      (8*(11920000+1500000+16008100*A+ctl))*R*H^(4*(E+2)) := by
  let u := E+2
  have bank := BundleSort.headerBanks_bits banks F old desc gap shapes (Frame.initial (fun _ : Unit => ready)) rows
    ⟨widths.1,widths.2.1,le_rfl,widths.2.2⟩
  simp only [Frame.initial_size,Nat.zero_add] at bank
  change (head₀).size+(2^b+2^b)*w ≤ 1000032*R*(w+1)^3 at bank
  have wcub : (w+1)^3 ≤ 8*H^(4*u) := by
    have room : w+1 ≤ 2*H^u := by
      change w+1 ≤ 2*H^(E+2)
      rw [sizeW]
      have positive : 1 ≤ H^(E+2) := Nat.pow_pos hpos
      omega
    apply (Nat.pow_le_pow_left room 3).trans
    rw [mul_pow,←pow_mul]
    exact Nat.mul_le_mul_left 8 (Nat.pow_le_pow_right hpos (by omega))
  have tail : src.size+(head₀).size+(2^b+2^b)*w ≤ 1500000*R*(w+1)^3 := by
    have slack : 433004*R*(w+1)^3+1000032*R*(w+1)^3 ≤ 1500000*R*(w+1)^3 := by
      rw [←Nat.add_mul,←Nat.add_mul]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    omega
  have tailCost := tail.trans (Nat.mul_le_mul_left (1500000*R) wcub)
  have sum := Nat.add_le_add prefixCost tailCost
  rw [appendWords_size,Frame.subst_size,Nat.add_mul]
  calc
    _ = (Fst.size+o*w)+(src.size+(head₀).size+(2^b+2^b)*w) := by omega
    _ ≤ _ := sum.trans_eq (by dsimp only [u]; ring)

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
