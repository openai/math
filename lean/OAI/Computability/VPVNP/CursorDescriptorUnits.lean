import OAI.Computability.VPVNP.CursorBranchBudget
import OAI.Computability.VPVNP.PairSimulationSelectorBounds

/-!
# Number of descriptor visits on the selected cursor branch

The units of the descriptor scans count the old sites, old slots and encoded
outer-term bits along the actual compressor execution. The number of blocks
and the binary length of every intermediate field are logarithmic in the
input length. Both logarithms enter the visit bound in Appendix E.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open Filter Compression CursorBounds PairSimulation.LocalHistory

variable {k : Type*} [Field k] {S : BlockSchedule k}

/-- The actual number of old site visits, old slot visits, and selector bits
on a branch of the chosen iterated compressor. -/
noncomputable def descriptorUnits (B : S.Templates) {A : Type*} [CommRing A] (f : B.Entry → A)
    (hf : B.IsSolution f) {lanes : ℕ} (T : ℕ) (h : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T h X).Choices) : ℕ :=
  scanUnits (B.execute f hf T h X) _
    (repeatReaders (blockReaders B f hf) _ T lanes (Nat.add_sub_of_le h).symm X) z

/-- Uniform constant multiplying the quadratic logarithmic visit bound. -/
noncomputable def descriptorUnitConstant (B : S.Templates) : ℕ :=
  (S.steps + 1) * scanConstant B * (scanConstant B + 1)

/-- The threshold precedes all lane labelings, scalar specializations, and
outer term choices. Both site and slot scans count the old level's order. -/
theorem eventually_descriptorUnits (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) : ∀ᶠ n : ℕ in atTop,
    ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let X := pairInput S labels hD
      let T := blockCount (u.θ : ℝ) n
      ∀ z : (B.execute f hf T hT X).Choices,
        descriptorUnits B f hf T hT X z ≤
          descriptorUnitConstant B * initialPositions b n * (n.log2 + 1) ^ 2 := by
  filter_upwards [eventually_pairBranchBounds B u b hb, eventually_ge_atTop 2] with n hbranch hn
  intro base lanes labels hD hT A _ f hf X T z
  let L := n.log2 + 1
  let K := scanConstant B
  let width := B.growthConstant ^ T * (X.maxWireWidth + 1)
  have hwidth := (hbranch.2.2 labels hD hT A f hf z).2.2.2.2.2.1
  change (width : ℝ) ≤ (n : ℝ) ^ (3/10 : ℝ) at hwidth
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hw : width ≤ n := by
    have h : (width : ℝ) ≤ n := hwidth.trans (by
      simpa using (Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (3/10:ℝ) ≤ 1)))
    exact_mod_cast h
  have hbits : Nat.clog 2 (width + 1) ≤ L := by
    apply (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
    have hp : n < 2 ^ L := Nat.lt_log2_self
    omega
  have htθ : (u.θ : ℝ) ≤ 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
    norm_num at this
    linarith
  have hTlog : T ≤ L := by
    apply le_trans _ (BurstRAM.clog_le_log2_succ n)
    rw [show T = blockCount (u.θ : ℝ) n from rfl, blockCount, ← Real.natCeil_logb_natCast 2 n]
    exact (Nat.floor_le_floor (mul_le_of_le_one_left (Real.logb_nonneg (by norm_num) hn₁) htθ)).trans
      (Nat.floor_le_ceil _)
  have hp := pairInput_positions S labels hD
  change X.positions = initialPositions b n at hp
  have hbound := execute_scanUnits B f hf T hT X z
  change descriptorUnits B f hf T hT X z ≤ ((S.steps+1)*T) * (X.positions*K*(K+Nat.clog 2 (width+1))) at hbound
  have hK : K + Nat.clog 2 (width + 1) ≤ (K + 1) * L := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (Nat.le_mul_of_pos_right K (Nat.succ_pos _)) hbits
  apply hbound.trans
  calc
    _ ≤ ((S.steps + 1) * L) * (X.positions * K * ((K + 1) * L)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hTlog) (Nat.mul_le_mul_left _ hK)
    _ = _ := by rw [hp]; dsimp [descriptorUnitConstant, K, L]; ring

end CursorNetwork

end VPVNP
end Computability
end OAI
