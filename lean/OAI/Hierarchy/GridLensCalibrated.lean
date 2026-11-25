import OAI.Hierarchy.GridBandwidth
import OAI.Hierarchy.GridLensRealization

namespace OAI
/-! # The strict mounted lens estimate at the common dyadic scales -/

namespace Hierarchy.UniversalGrid.Grid

open LinearAlgebra.SpectralBooks GridLens GridScale Filter
noncomputable section

variable {F : Type*} [Field F] {k : ℕ}

/-- All codes and all replication counts under the common envelope use the
same side and radius. The calibrated error bound pays both the transverse
length of the rails and the selector and cell counts of the actual grid. -/
theorem calibrated_strict {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D)
    (A : ℕ) (hk : 0 < k) (P : SpectralPlacementPrices F (Space k)) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w →
    let a := overhead Q D w
    let R : ℝ := radius k a
    ∀ (G : Grid F k) [Nonempty (Fin G.rails)],
      G.rails ≤ external k a (pairs A w q) → G.g ≤ side a →
      G.selectorBits ≤ selector k w a →
      G.replacement.Gap (Catalyst.tickProduct G.tick G.copies) (D w / 2) →
      ∀ code : Bits G.codeBits, (∀ s W, G.wiring code s = some W →
        Nonempty (Placement G.replacement W G.direction R
          (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) (side a - 1))) →
      G.exactGrid code - G.accelerated code = 0 ∨
        P.price (GridDiagonal.raw (G.exactGrid code - G.accelerated code))
          (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) <
        P.price (GridDiagonal.raw (GridDiagonal.identity F))
          (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) := by
  let _ : NeZero k := ⟨hk.ne'⟩
  filter_upwards [diagonal_slack env k A hk, bounds env] with w budget saved
  intro q hq top a R G _ rails cells selectors gap code mount
  have slack := budget q hq top
  have rpos : 0 < R := by
    change (0:ℝ)<((2^((10*k+16)*a):ℕ):ℝ)
    exact_mod_cast Nat.two_pow_pos ((10*k+16)*a)
  have dnonneg : 0 ≤ D w / 2 :=
    div_nonneg ((by positivity : 0 ≤ (2:ℝ)^(w-a)).trans saved.2.1) (by norm_num)
  have sidePos : 1 ≤ side a := Nat.two_pow_pos _
  have sideEq : ((side a - 1 : ℕ) : ℝ) + 1 = (side a : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel sidePos
  have far : 8*(((side a - 1 : ℕ):ℝ)+1) ≤ R := by
    rw [sideEq]
    change 8*(side a:ℝ)≤((radius k a:ℕ):ℝ)
    exact_mod_cast (show 8*side a≤radius k a from slack.1)
  apply G.mounted_strict P R (D w / 2) (side a - 1) rpos dnonneg gap far _ code mount
  rw [sideEq, Nat.cast_add, Nat.cast_pow]
  refine lt_of_le_of_lt (add_le_add ?_ ?_) slack.2
  · apply div_le_div_of_nonneg_right _ rpos.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast rails) (by positivity)) (sq_nonneg _)
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add (by exact_mod_cast selectors)
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast cells) k)


/-- An honestly distributed controller is impossible on a grid whose
selector wirings are all mounted within the calibrated lens budget. -/
theorem calibrated_excludes {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D)
    (A : ℕ) (hk : 0 < k) (P : SpectralPlacementPrices F (Space k)) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0 < q → q ≤ Q w →
    let a := overhead Q D w
    let R : ℝ := radius k a
    ∀ (G : Grid F k) [Nonempty (Fin G.rails)],
      G.rails ≤ external k a (pairs A w q) → G.g ≤ side a →
      G.selectorBits ≤ selector k w a →
      G.replacement.Gap (Catalyst.tickProduct G.tick G.copies) (D w / 2) →
      (∀ code s W, G.wiring code s = some W →
        Nonempty (Placement G.replacement W G.direction R
          (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) (side a - 1))) →
      ∀ code : Bits G.codeBits, G.Distributed code → False := by
  filter_upwards [calibrated_strict env A hk P] with w strict
  intro q hq top a R G _ rails cells selectors gap mounted code trace
  exact G.excludes P _ (fun c => strict q hq top G rails cells selectors gap c (mounted c)) code trace

end
end Hierarchy.UniversalGrid.Grid

end OAI
