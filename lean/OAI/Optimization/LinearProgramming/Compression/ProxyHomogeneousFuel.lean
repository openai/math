import OAI.Optimization.LinearProgramming.Compression.ProxyFuelQueries

/-! The initialized proxy cutoff also covers homogeneous dyadic comparison rows,
including their common integer scale and the additional proxy-denominator factor. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The available rounding reserve dominates the extra copy of a dyadic grid denominator. -/
theorem manuscript_homogeneous_grid_fuel (N d : ℕ) (hd : d ≤ paperWidth N+1) :
    let p := paperRadius N+7
    p + (2*p+8*d+30) ≤ manuscriptProxyFuel N := by
  let w := (N+1)^6
  let B := 100*(N+1)^3
  let m := proxyRoundingInputFormula w B
  let u := 4*((w+2)+1)+m+6
  let Q := proxyQueryWidthFormula (w+2) m
  have hm : 4*w+2*B+40 ≤ m := by unfold m proxyRoundingInputFormula; dsimp only; omega
  have hu : m ≤ u := by dsimp [u]; omega
  have hprod : u ≤ u*((w+2)+2) := Nat.le_mul_of_pos_right _ (by omega)
  have hQ : u*((w+2)+2) ≤ Q := by unfold Q proxyQueryWidthFormula; dsimp only [u]; omega
  change d ≤ w+1 at hd
  change (B+7)+(2*(B+7)+8*d+30) ≤ (B+7)+(w+2)+Q+(4*w+2*B+40)
  omega

/-- Consequently even the actual rescaled integer L¹ row, multiplied by the scale
required by the proxy service, fits inside the fixed power budget. -/
theorem manuscript_homogeneous_grid_l1 (N d : ℕ) (hd : d ≤ paperWidth N+1) (rowBound : ℤ)
    (hrow : rowBound ≤ (2:ℤ)^(2*(paperRadius N+7)+8*d+30)) :
    (2:ℤ)^(paperRadius N+7)*rowBound ≤ (2:ℤ)^manuscriptProxyFuel N := by
  calc
    _ ≤ (2:ℤ)^(paperRadius N+7)*2^(2*(paperRadius N+7)+8*d+30) :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = (2:ℤ)^((paperRadius N+7)+(2*(paperRadius N+7)+8*d+30)) := (pow_add ..).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (manuscript_homogeneous_grid_fuel N d hd)

end Compression
end LinearProgramming
end Optimization
end OAI
