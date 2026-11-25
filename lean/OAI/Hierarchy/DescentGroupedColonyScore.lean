import OAI.Hierarchy.DescentPaddedSites
import OAI.Hierarchy.DescentColonyScoreCore

namespace OAI
/-! # Splitting a product host into repeated scans over a single neighbor table -/

namespace Hierarchy.DescentColonies.GroupedScan
open DescentGL
open scoped Classical BigOperators
noncomputable section
variable {k G H : ℕ}

def product (G H : ℕ) : Fin G × Fin H ≃ Fin (G*H) := finProdFinEquiv

def site (g : Fin G) : Fin H ↪ Fin (G*H) where
  toFun v := product G H (g,v)
  inj' _ _ eqn := congrArg Prod.snd ((product G H).injective eqn)

def neighbors (G : ℕ) (inc : Fin H→List (Fin H)) (p : Fin (G*H)) :=
  let z := (product G H).symm p
  (inc z.2).map (site z.1)

def flat (rows : Fin G→Fin H→Block k→ℕ) (p : Fin (G*H)) : Block k→ℕ :=
  let z := (product G H).symm p
  rows z.1 z.2

@[simp] theorem neighbor_site (inc : Fin H→List (Fin H)) (g : Fin G) (v : Fin H) :
    neighbors G inc (site g v)=(inc v).map (site g) := by
  change (inc (((product G H).symm (product G H (g,v))).2)).map
    (site (((product G H).symm (product G H (g,v))).1))=_
  rw [Equiv.symm_apply_apply]

@[simp] theorem flat_site (rows : Fin G→Fin H→Block k→ℕ) (g : Fin G) (v : Fin H) :
    flat rows (site g v)=rows g v := by
  change rows (((product G H).symm (product G H (g,v))).1)
    (((product G H).symm (product G H (g,v))).2)=_
  rw [Equiv.symm_apply_apply]

theorem weight_site (rows : Fin G→Fin H→Block k→ℕ) (a μ : Bits k) (g : Fin G)
    (v : Fin H) (x : Block k) :
    multiplierLoad (flat rows) a μ (site g v) x=multiplierLoad (rows g) a μ v x := by
  unfold multiplierLoad
  split <;> simp only [flat_site]

/-- Every flag bit at every depth is unchanged by separating the groups. -/
theorem split_at (inc : Fin H→List (Fin H)) (rows : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a μ : Bits k) (g : Fin G) (s dep : ℕ) (v : Fin H) (x : Block k) :
    Scan.lookup (Scan.build (neighbors G inc) (multiplierLoad (flat rows) a μ) D cap s) dep (site g v) x=
      Scan.lookup (Scan.build inc (multiplierLoad (rows g) a μ) D cap s) dep v x :=
  Scan.padded_lookup (site g) inc (neighbors G inc) _ _ (neighbor_site inc g) (weight_site rows a μ g) D cap s dep v x

theorem uniform_score (inc : Fin H→List (Fin H)) (rows : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) :
    uniformColonyScore (neighbors G inc) (fun _ : Fin 1=>flat rows) D cap a μ=
      uniformColonyScore inc rows D cap a μ := by
  calc
    _ = ∑ s : Fin (G*H),(Scan.siteKeys (Scan.build (neighbors G inc) (multiplierLoad (flat rows) a μ.val) D cap k) s).card := by
      simp only [uniformColonyScore,Fin.sum_univ_one,Scan.leafScore_siteKeys]
    _ = ∑ g : Fin G,∑ v : Fin H,(Scan.siteKeys (Scan.build inc (multiplierLoad (rows g) a μ.val) D cap k) v).card := by
      rw [← (product G H).sum_comp,Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro v _
      exact congrArg Finset.card (Scan.sites_padded (site g) inc (neighbors G inc) _ _ (neighbor_site inc g)
        (weight_site rows a μ.val g) D cap v)
    _ = _ := by simp only [uniformColonyScore,Scan.leafScore_siteKeys]

end
end Hierarchy.DescentColonies.GroupedScan

end OAI
