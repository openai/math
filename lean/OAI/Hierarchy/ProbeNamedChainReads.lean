import OAI.Hierarchy.ProbeChainStrip
import OAI.Hierarchy.ProbeSiteOrder

namespace OAI
/-! # One activation cutoff for all actual global orders of named physical sites -/

namespace Hierarchy.AdaptiveProbe.ChainStrip
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped BigOperators Classical
noncomputable section

abbrev Site (depth k : ℕ) := ColumnSite (Columns depth) k
abbrev Naming (depth k : ℕ) := Site depth k ≃ Fin (Fintype.card (Site depth k))

def namedError (F : Type*) [Field F] (depth k : ℕ) (name : Naming depth k) (M : ℝ) (y : Axes depth k → ℝ) : ℝ :=
  letI : SiteNaming (Site depth k) := ⟨name⟩
  Probe.discrepancy F (wires depth k) (demands depth k) (prices depth k M y)

/-- These coordinates are common along a true H-strip. The inequalities hold for
every signed row, so a later activation can project onto its originally chosen sign. -/
def Reads (depth k : ℕ) (M η : ℝ) (y : Axes depth k → ℝ) : Prop :=
    ∃ zi zo : Fin (depth+1) → Coordinates k,
      (∀ j : ℕ, ∀ hj : j+1<depth+1, zo ⟨j,by omega⟩=zi ⟨j+1,hj⟩) ∧
      (∀ i : Axes depth k, |rise M (y i)-max (Source.sign i.2.2*(zo i.1 i.2.1-zi i.1 i.2.1)) 0|<η) ∧
      |0-max (dist (zi 0) (zo (Fin.last depth))-1) 0|<η

theorem sorted_reads {F : Type*} [Field F] (depth k : ℕ) (hk : 0<k) (no : ¬HasSpectralFlat F (k+1))
    {η : ℝ} (tol : 0<η) : ∃ M₀ : ℕ, ∀ M ≥ M₀, ∃ ε : ℝ, 0<ε ∧ ∀ name : Naming depth k,
    ∀ y ∈ Set.Icc (0:Axes depth k → ℝ) (fun _ => (M:ℝ)+1), namedError F depth k name M y ≤ ε → Reads depth k M η y := by
  let good (e : Naming depth k) (M : ℕ) (ε : ℝ) := ∀ y ∈ Set.Icc (0:Axes depth k → ℝ) (fun _ => (M:ℝ)+1),
    namedError F depth k e M y ≤ ε → Reads depth k M η y
  apply SiteOrder.common_tolerance good (fun e M _ _ ab h y box pass => h y box (pass.trans ab))
  intro name
  let : SiteNaming (Site depth k) := ⟨name⟩
  obtain ⟨N,each⟩ := frames (F:=F) depth k hk no tol
  refine ⟨N+1,?_⟩; intro M enough
  have pm : 0<M := by omega
  exact each M (by exact_mod_cast pm) (by exact_mod_cast (show N≤M by omega))
end
end Hierarchy.AdaptiveProbe.ChainStrip

end OAI
