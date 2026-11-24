import OAI.Computability.VPVNP.DegreeRefreshIncidence
import OAI.Computability.VPVNP.DegreeRefreshWidths

/-!
# Incident external words in the degree refresh

In Section 7.3 of *VP and VNP differ over every field*, each destination slot
receives all its segments in one external word, ordered by the original source
ports. This gives a local evaluator of the two segment lists at every port and
identifies the widths used by its internal tensor with the widths in the energy
estimate.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.Refresh

variable {H L V : Type*} {d : ℕ} [AddCommGroup H] [AddCommGroup L]
  (G : LiftedSlots V d (H × L)) (port : H ≃ Fin d)

/-- The destination slot determines the incoming bundle. Invert its port
translation to recover the segment's position in the source ordering. -/
theorem oldPortMatching_symm_apply (b : (V × L) × Fin d) (j : Fin d) :
    (oldPortMatching G port).symm (b,j) =
      ((bundleTarget G).symm b, (bundlePort G port ((bundleTarget G).symm b)).symm j) := by
  apply (oldPortMatching G port).injective
  simp only [oldPortMatching_apply, Equiv.apply_symm_apply]

/-- Every old port in the same external word reaches the same block and slot. -/
theorem oldPortMatching_bundle (a : Arc (V × L) d) :
    (oldPortMatching G port a).1 = bundleTarget G a.1 := rfl

/-- At an actual port the segment lists in the old tensor can be read from the
two incident external words, using the same local reader as the kernel step. -/
theorem portSegments_eq_incident (w : Arc (V × L) d → ℕ) (z : External w)
    (b : (V × L) × Fin d) :
    portSegments (oldPortMatching G port) w z b.1 b.2 =
      incidentPortSegments (oldPortMatching G port) (bundleTarget G) (oldPortMatching_bundle G port)
        w b (z b) (z ((bundleTarget G).symm b)) :=
  (incidentPortSegments_external _ _ _ _ _ _).symm

variable {dH d₀ : ℕ} (P : SlotGraph (Fin d) dH) (hD : 1 < d) (hd : dH + 1 ≤ d₀)

open DegreeRefresh in
omit [AddCommGroup H] in
/-- The actual refreshed matching sends the outgoing external word at a port
to the unique incoming external slot in the translated block. -/
theorem actualTarget_external_bundle (b : (V × L) × Fin d) :
    (degreeRefresh G P hD hd).actualTarget
        (refreshedCoordinates.symm (b, refreshSlots hd (.inl 0))) =
      refreshedCoordinates.symm (bundleTarget G b, refreshSlots hd (.inl 0)) := by
  rcases b with ⟨⟨v,g⟩,i⟩
  exact congrArg (fun t : ((V × Fin d) × L) × Fin d₀ ↦ ((t.1.1,t.2),t.1.2))
    (degreeRefresh_external G P hD hd (v,i) g)

open DegreeRefresh in
omit [AddCommGroup H] in
/-- The incoming word used by the local evaluator belongs to the actual arc
ending at the port's external slot. -/
theorem actualTarget_symm_external_bundle (b : (V × L) × Fin d) :
    (degreeRefresh G P hD hd).actualTarget.symm
        (refreshedCoordinates.symm (b, refreshSlots hd (.inl 0))) =
      refreshedCoordinates.symm ((bundleTarget G).symm b, refreshSlots hd (.inl 0)) := by
  apply (degreeRefresh G P hD hd).actualTarget.injective
  rw [Equiv.apply_symm_apply, actualTarget_external_bundle, Equiv.apply_symm_apply]

open DegreeRefresh in
omit [AddCommGroup H] [AddCommGroup L] in
/-- The external arc's actual width is the sum of the widths in its word. -/
theorem actualWidth_external_bundle (w : (V × Fin d) × (H × L) → ℕ)
    (u : (V × L) → Fin d × Fin dH → ℕ) (b : (V × L) × Fin d) :
    actualWidths hd port w u (refreshedCoordinates.symm (b, refreshSlots hd (.inl 0))) =
      ∑ j, bundleWidths port w b j := by
  simp [actualWidths, newWidths]

/-- For the actual matching, every internal tensor factor has the bit width
charged to the corresponding tie by the energy inequality. -/
theorem internalWidth_eq_tieWidth (w : Arc (V × L) d → ℕ) (s : V × L) (e : DegreeRefresh.Tie d) :
    internalWidth (oldPortMatching G port) w s e =
      DegreeRefresh.tieWidth (bundleTarget G) (bundlePort G port) (fun b j ↦ w (b,j)) s e := by
  simp only [internalWidth, DegreeRefresh.tieWidth, DegreeRefresh.incoming, tieTarget, tieSource,
    oldPortMatching_symm_apply]

end Compression.Refresh

end VPVNP
end Computability
end OAI
