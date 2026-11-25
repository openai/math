import OAI.Hierarchy.GridLensContraction
import OAI.Hierarchy.GridPrice

namespace OAI
/-! # Applying the lens budget to all settings of a mounted controller -/

namespace Hierarchy.UniversalGrid.Grid
open LinearAlgebra.SpectralBooks GridLens
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {k : ℕ} (G : Grid F k)
variable [Nonempty (Fin G.rails)] [Nontrivial (Fin k × Bool)]

/-- A valid selector pays the rail budget once and the discount once for every
changed cell. Invalid selectors contribute zero. -/
theorem mounted_error_price (P : SpectralPlacementPrices F (Space k)) (R D : ℝ)
    (n : ℕ) (hR : 0 < R)
    (gap : G.replacement.Gap (Catalyst.tickProduct G.tick G.copies) D)
    (far : 8*((n:ℝ)+1)≤R) (a : Bits G.codeBits)
    (mount : ∀ s W, G.wiring a s = some W →
      Nonempty (Placement G.replacement W G.direction R
        (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) n))
    (z : Bits G.selectorBits × Changed (G.g^k)) (nz : G.errorTerm a z ≠ 0) :
    P.price (GridDiagonal.raw (G.errorTerm a z))
      (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) ≤
        2*R*G.rails + 18*((k-1:ℕ):ℝ)*G.rails*((n:ℝ)+1)^2/R - (z.2.val.card:ℝ)*D := by
  classical
  cases choice : G.wiring a z.1 with
  | none => exact (nz (by funext x; simp [errorTerm,choice])).elim
  | some W =>
    obtain ⟨m⟩ := mount z.1 W choice
    let data := Catalyst.tickProduct G.tick G.copies
    let cells := selected G.replacement data z.2.val
    have iden : G.errorTerm a z = -(W.mixedEval cells) := by
      change (fun x => (G.wiring a z.1).elim 0
        (fun X => X.errorTerm G.exactCell G.replacement.coeff z.2 x)) = _
      rw [choice]
      exact W.errorTerm_eq_neg_mixedEval G.exactCell G.replacement.coeff z.2
    have real : W.mixedEval cells ≠ 0 := by
      intro zero
      exact nz (by rw [iden,zero,neg_zero])
    let y : (Fin k × Bool) ↪ Space k := ⟨GridDiagonal.focus R,GridDiagonal.focus_injective hR⟩
    let atSite : GridDiagonal.Ends (Fin G.rails) → Fin k × Bool := fun u => (G.direction u.1,u.2)
    let : Nonempty W.Sites :=
      ⟨GridAddress.outputSite (Classical.ofNonempty : GridDiagonal.Ends (Fin G.rails))⟩
    rw [iden]
    change P.price (CorrectionProducts.raw (-(W.mixedEval cells))) (y ∘ atSite) ≤ _
    rw [Wiring.price_neg]
    exact m.mixed_price P data gap z.2.val real far

/-- The strict comparison at the foci uses the controller's actual selector
count, actual rail placements and the ordinary sum of its error terms. -/
theorem mounted_strict (P : SpectralPlacementPrices F (Space k)) (R D : ℝ) (n : ℕ)
    (hR : 0 < R) (hD : 0 ≤ D)
    (gap : G.replacement.Gap (Catalyst.tickProduct G.tick G.copies) D)
    (far : 8*((n:ℝ)+1)≤R)
    (margin : 18*((k-1:ℕ):ℝ)*G.rails*((n:ℝ)+1)^2/R +
      2*k*R*(G.selectorBits + (G.g^k : ℕ) : ℕ) < D)
    (a : Bits G.codeBits)
    (mount : ∀ s W, G.wiring a s = some W →
      Nonempty (Placement G.replacement W G.direction R
        (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) n)) :
    G.exactGrid a - G.accelerated a = 0 ∨
      P.price (GridDiagonal.raw (G.exactGrid a - G.accelerated a))
          (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) <
        P.price (GridDiagonal.raw (GridDiagonal.identity F))
          (fun u => GridDiagonal.focus R (G.direction u.1,u.2)) := by
  apply G.price_strict P R D _ hR a _ margin
  intro z nz
  have paid := G.mounted_error_price P R D n hR gap far a mount z nz
  have count : (1:ℝ) ≤ z.2.val.card := by
    exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr z.2.property))
  linarith [mul_le_mul_of_nonneg_right count hD]

end
end Hierarchy.UniversalGrid.Grid

end OAI
