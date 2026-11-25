import OAI.Hierarchy.DescentGroupedColonyScore
import OAI.Hierarchy.DescentWinningRows
import OAI.Hierarchy.DescentAffineColors

namespace OAI
/-! # Affine scores are preserved by collecting the disconnected host components

The row for each grouped site, component, and dyadic interval has the same
filtered load as its row in the single flattened host. Thus the total affine
score and its candidate order are unchanged by this representation.
-/
namespace Hierarchy.DescentColonies.GroupedScan
open DescentGL DescentBinaryField DescentAffineColors WinningSlabs
open scoped BigOperators Classical
noncomputable section
variable {G H k : ℕ}

private def singleSite (G H : ℕ) : (Fin G × Fin H) ≃ (Fin 1 × Fin (G*H)) where
  toFun z := (0,finProdFinEquiv z)
  invFun z := finProdFinEquiv.symm z.2
  left_inv := fun z=>finProdFinEquiv.symm_apply_apply z
  right_inv := fun z=>Prod.ext (Subsingleton.elim _ _) (finProdFinEquiv.apply_symm_apply z.2)

/-- Preserve the interval key when readdressing a grouped slot in the single
flat directory. This also accounts for rows that have zero outgoing load. -/
def slabSlots (G H k : ℕ) : Slot G H k ≃ Slot 1 (G*H) k :=
  ((directory G H k).symm.trans ((singleSite G H).prodCongr (Equiv.refl _))).trans (directory 1 (G*H) k)

theorem slabSlots_at (g : Fin G) (v : Fin H) (q : Fin (keys k).length) :
    slabSlots G H k (directory G H k ((g,v),q))=directory 1 (G*H) k ((0,site g v),q) := by
  simp [slabSlots,singleSite,site,product]

abbrev groupedSlabs (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :=
  worldValue (Selected.winningRows inc W D cap a μ) (Selected.winningAmounts amt a μ)

abbrev singleSlabs (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) :=
  worldValue (Selected.winningRows (neighbors G inc) (fun _ : Fin 1=>flat W) D cap a μ)
    (Selected.winningAmounts (fun _ : Fin 1=>flat amt) a μ)

theorem slab_value (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (i : Slot G H k) (x : Block k) :
    singleSlabs inc W amt D cap a μ (slabSlots G H k i) x=groupedSlabs inc W amt D cap a μ i x := by
  obtain ⟨⟨⟨g,v⟩,q⟩,rfl⟩ := (directory G H k).surjective i
  rw [slabSlots_at]
  simp only [singleSlabs,groupedSlabs,worldValue,Equiv.symm_apply_apply,filtered,member,
    Selected.winningRows,Selected.winningAmounts,Scan.leafDepth,split_at,weight_site]

/-- Every affine candidate has the same scalar score as on the physical
singleton directory indexed by `Fin (G*H)`. -/
theorem slab_score (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a : Bits k) (μ : Nonzero k) (j : Candidate k) :
    score (singleSlabs inc W amt D cap a μ) j = score (groupedSlabs inc W amt D cap a μ) j := by
  let diff (row : Block k→ℕ) := difference (side row j true) (side row j false)
  let term (i : Slot 1 (G*H) k) := diff (singleSlabs inc W amt D cap a μ i)
  change (∑ i, term i) = ∑ i, diff (groupedSlabs inc W amt D cap a μ i)
  calc
    _ = ∑ i, term (slabSlots G H k i) := ((slabSlots G H k).sum_comp term).symm
    _ = _ := Finset.sum_congr rfl fun i _=>congrArg diff (funext (slab_value inc W amt D cap a μ i))

end
end Hierarchy.DescentColonies.GroupedScan

end OAI
