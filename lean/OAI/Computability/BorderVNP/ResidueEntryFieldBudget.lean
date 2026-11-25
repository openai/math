import OAI.Computability.BorderVNP.ResidueEntryFieldGuess

/-! # Bit budget of residue-field arithmetic

The finite-field cardinality bound in §10.2 controls the limb width and the extension
degree simultaneously. The actual Boolean gate budget is polynomial in this bit bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryField

variable {p m s k d w : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Fintype K]
  [Algebra (ZMod p) K]

/-- The characteristic and the number of basis limbs are both controlled by the field's
binary size. The extra bit accommodates the literal modulus also at characteristic two. -/
theorem dimensions_le (B : Module.Basis (Fin d) (ZMod p) K)
    (hcard : Fintype.card K ≤ 2^m) :
    d ≤ m ∧ Nat.clog 2 p + 1 ≤ m + 1 ∧ p < 2^(Nat.clog 2 p + 1) := by
  have hc : p^d = Fintype.card K := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := K), ZMod.card,
      Module.finrank_eq_card_basis B, Fintype.card_fin]
  have htwo := (Fact.out : Nat.Prime p).two_le
  have hd : 2^d ≤ 2^m := ((Nat.pow_le_pow_left htwo d).trans_eq hc).trans hcard
  have hp : p ≤ 2^m := by
    have h := Fintype.card_le_of_injective _ (algebraMap (ZMod p) K).injective
    rw [ZMod.card] at h
    exact h.trans hcard
  refine ⟨(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hd,
    Nat.succ_le_succ (Nat.clog_le_of_le_pow hp), ?_⟩
  have h := Nat.le_pow_clog (by decide : 1 < 2) p
  exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

omit [Fact p.Prime] in
/-- The cost of an extension-field gate, including two advised constants, grows at most
as the sixth power of the binary size parameter. -/
theorem stepCost_le (hd : d ≤ m) (hw : w ≤ m+1) :
    stepCost d w ≤ 20000 * (m+2)^6 := by
  calc
    _ ≤ stepCost m (m+1) := by
      unfold stepCost fieldGateCost productLimbCost limbCost
      gcongr
    _ ≤ _ := by
      unfold stepCost fieldGateCost productLimbCost limbCost
      ring_nf
      omega

/-- Concrete short-path bound for an arbitrary shared arithmetic DAG on a field with at
most `m` bits per element. Each output bit can be selected as an AND/NOT circuit. -/
theorem compile_count_of_card (B : Module.Basis (Fin d) (ZMod p) K) (C : VPVNP.Circuit K (Fin s) k)
    (hcard : Fintype.card K ≤ 2^m) :
    (compile B (dimensions_le B hcard).2.2 C).net.count ≤ (k+1)*20000*(m+2)^6 := by
  obtain ⟨hd,hw,_⟩ := dimensions_le B hcard
  have h := compile_count B (dimensions_le B hcard).2.2 C
  have hc := stepCost_le hd hw
  have hconst : d*(Nat.clog 2 p+1)*(Nat.clog 2 p+1) ≤ stepCost d (Nat.clog 2 p+1) := by
    unfold stepCost
    omega
  calc
    _ ≤ (k+1)*stepCost d (Nat.clog 2 p+1) := by rw [Nat.add_mul, one_mul]; omega
    _ ≤ (k+1)*(20000*(m+2)^6) := Nat.mul_le_mul_left _ hc
    _ = _ := by ring

end ResidueEntryField

end BorderVNP
end Computability
end OAI
