import OAI.Computability.BorderVNP.CellLocalSweepFields
import OAI.Computability.BorderVNP.CellBoxSpanWidth

/-! # Width of the real scalar fields passed to each compact box visit -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit.Local

/-- Bounds on the actual binary fields of the three prepared sweep parameters. -/
def ParamsWidth (x : Params) (W : ℕ) : Prop :=
  x.1.size+1 ≤ W ∧ x.2.1.size+1 ≤ W ∧ x.2.2.size+1 ≤ W

/-- Joint maximum of the raw scalar values and the three prepared parameters. -/
def visitMax (U : ℕ) (x : Params) : ℕ := max U (max x.1 (max x.2.1 x.2.2))

/-- The independently prepared parameters and the raw field bound are covered by the joint maximum. -/
theorem visitMax_bounds (U : ℕ) (x : Params) : U ≤ visitMax U x ∧ ParamsBound x (visitMax U x) := by
  unfold visitMax ParamsBound
  omega

/-- Cubing the joint field maximum to cover every cumulative occurrence ordinal
still requires only linearly many binary digits. -/
theorem visitMax_cube_width {U W : ℕ} {x : Params} (hu : U.size+1 ≤ W) (hp : ParamsWidth x W) :
    ((visitMax U x+1)^3).size+1 ≤ 3*W+2 := by
  obtain ⟨h₁,h₂,h₃⟩ := hp
  have hmax : visitMax U x < 2^W := max_lt (Nat.size_le.mp (by omega)) (max_lt
    (Nat.size_le.mp (by omega)) (max_lt (Nat.size_le.mp (by omega)) (Nat.size_le.mp (by omega))))
  have hpow := Nat.size_le_size (Nat.pow_le_pow_left (show visitMax U x+1 ≤ 2^W by omega) 3)
  rw [← pow_mul,Nat.size_pow] at hpow
  omega

/-- The complete source and resolved sweep span only depend on the widths of the
prepared parameters and of the raw fields. -/
theorem sweepSpan_static_width (D : Directory) (p : ℕ) (params : Params) {A M U W : ℕ}
    (hs : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2) (h : RawFields D p U)
    (hu : U.size+1 ≤ W) (hp : ParamsWidth params W) :
    sweepSpan (params,D)+1 ≤ (300*(8*A+4)+8*A+8)*(M+1)^2*W := by
  obtain ⟨h₁,h₂,h₃⟩ := hp
  have hP : (paramsCode params).length+1 ≤ 8*W := by
    simp only [paramsCode,ExactQuantumFactoring.BitStackProgram.prodCode,
      ExactQuantumFactoring.BitStackProgram.pairBits_length,Nat.size_eq_bits_len]
    omega
  have hb := (blockSpan_static_width D p hs hstore h).trans (Nat.mul_le_mul_left _ hu)
  have hw : W ≤ (M+1)^2*W := Nat.le_mul_of_pos_left _ (by positivity)
  change (paramsCode params).length+blockSpan D+1 ≤ _
  calc _ ≤ 8*W+(300*(8*A+4)+8*A)*(M+1)^2*W := by omega
       _ ≤ 8*((M+1)^2*W)+(300*(8*A+4)+8*A)*(M+1)^2*W := by gcongr
       _ = _ := by ring

end CellSparse.Packet.Emit.Local

end BorderVNP
end Computability
end OAI
