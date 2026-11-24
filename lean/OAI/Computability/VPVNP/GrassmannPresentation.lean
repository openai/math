import OAI.Computability.VPVNP.GrassmannFrameDimensions
import OAI.Computability.VPVNP.IndependentCompletion
import OAI.Computability.VPVNP.SubspaceOrbits

/-!
# A frame presentation for any Grassmannian pair

Two planes of type `r` have a presentation by two independent `r`-column
blocks and a shared completion of `m-r` columns. We transport one independent
frame by an ambient linear automorphism carrying its two planes to the given
pair.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

/-- Every ordered pair of type `r` admits the independent column presentation
used in the opposite-side rigidity proof of Lemma 5.3. -/
theorem HasType.exists_frame {m r : ℕ} {a b : Plane m} (hab : HasType r a b) (hr : r ≤ m) :
    ∃ (v : Fin (r + r) → Space m) (w : Fin (m - r) → Space m),
      LinearIndependent (ZMod 2) (Sum.elim v w) ∧
      a.val = completedBlock v w (leftIndices r) ∧
      b.val = completedBlock v w (rightIndices r) := by
  have hdim : Module.finrank (ZMod 2) (Space m) = 2*m := by simp [Space]
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (show r + r ≤ Module.finrank (ZMod 2) (Space m) by omega)
  obtain ⟨w, hw⟩ := exists_independent_completion hv (k := m - r) (by simp; omega)
  have hm : (m - r) + r = m := Nat.sub_add_cancel hr
  let l := leftPlane v w hm hw
  let u := rightPlane v w hm hw
  have htype : HasType r l u := hasType_framePlanes v w hm hw
  obtain ⟨g, gl, gu⟩ := exists_pair_linearEquiv (K := ZMod 2) (V := Space m) l.val u.val
    a.val b.val (l.property.trans a.property.symm) (u.property.trans b.property.symm)
    (htype.trans hab.symm)
  have hind : LinearIndependent (ZMod 2) (g.toLinearMap ∘ Sum.elim v w) :=
    (g.toLinearMap.linearIndependent_iff g.ker).mpr hw
  have hf : g.toLinearMap ∘ Sum.elim v w = Sum.elim (g ∘ v) (g ∘ w) := by
    funext i
    cases i <;> rfl
  refine ⟨g ∘ v, g ∘ w, hf ▸ hind, ?_, ?_⟩
  · exact gl.symm.trans (completedBlock_map v w (leftIndices r) g)
  · exact gu.symm.trans (completedBlock_map v w (rightIndices r) g)

end Grassmann

end VPVNP
end Computability
end OAI
