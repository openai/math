import OAI.Hierarchy.DescentPackedMatchOrdinary
import OAI.Hierarchy.DescentPackedMatchChooserFrame

namespace OAI
/-! # The original signed and winner words retained by the chosen matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM
noncomputable section
variable {r D p d M H G w : ℕ}

/-- The original fields used in owner and donor addressing, with the same
sorted physical roster and the exact common lower-address bound. -/
structure Rails (P : Ports D) (wins : Fin r→Bank) (marked : Fin r→Fin p→Bank)
    (source : Fin H→Fin G→Panel r D p d) (next : Fin H→Fin D→Option (Fin H))
    (M limit : ℕ) (m : Memory w) : Prop where
  access : ∀x,Accessible P (wins x) H G M w limit
  chipFit : ∀x i,(marked x i).Fits w limit
  chipRows : ∀x i,H*chunks G M≤(marked x i).size
  winsRead : ∀x,Reads (wins x) (fun h g=>(source h g).winner x) M m
  chipRead : ∀x i,Reads (marked x i) (fun h g=>(source h g).neighbor x i) M m
  roster : Mounted P next m G M
  fieldsRead : ∀i,DescentPackedZip.Source (Gather.expr wins marked P H i)
    (fun h g=>Gather.terrain source h g i) M m

variable {P : Ports D} {wins : Fin r→Bank} {marked : Fin r→Fin p→Bank}
    {source : Fin H→Fin G→Panel r D p d} {next : Fin H→Fin D→Option (Fin H)} {limit : ℕ} {m o : Memory w}

theorem Rails.moved (prior : Rails P wins marked source next M limit m) (x₀ : Fin r)
    (keep : ∀a<limit,o a=m a) : Rails P wins marked source next M limit o := by
  refine ⟨prior.access,prior.chipFit,prior.chipRows,?_,?_,?_,?_⟩
  · intro x
    exact Chooser.reads_before _ _ m o (prior.winsRead x) keep (prior.access x).source (prior.access x).srcRoom
  · intro x j
    exact Chooser.reads_before _ _ m o (prior.chipRead x j) keep (prior.chipFit x j) (prior.chipRows x j)
  · exact Chooser.mounted_before P (wins x₀) next m o prior.roster keep (prior.access x₀)
  · intro i j
    exact (eval_below _ _ m o (early_expr wins marked P limit prior.access prior.chipFit i) keep).trans
      (prior.fieldsRead i j)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
