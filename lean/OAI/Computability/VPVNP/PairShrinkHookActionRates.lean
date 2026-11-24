import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader
import OAI.Computability.VPVNP.PairShrinkHookRates
import OAI.Computability.VPVNP.PairShrinkResidentBudget

/-!
# Ordinal cost of the canonical shrinking parser

The parent packet and the parsed child and hidden fields select the physical
resident jobs. Their actual gather and matrix actions determine the cost
bound on every successful tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression CompressorRecords CompressorRecords.ShrinkBlockInputs
open LocalHistory ShrinkNodeCost VertexImage
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} {B : S.Templates}
  {i : Fin S.steps} {g : ℕ} {X : State (a i) (packingLaneBits (a i) g)}
  {sel : X.ShrinkSelection B.shrink} {v : MapResidentRows.Site X}
  {w n t : ℕ} (site : CanonicalSite B i X sel v w n t) (ord : B.Entry → Fin t)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

variable (node : Word w)
  (order : (site.descriptor node).sites = List.ofFn fun j =>
    ((((shrinkPassReaders B f hf i rfl X).order sel).children v).entries j).val)
  (saved : Scratch w n) (bits tail : List Bool) (body : VisitPath w n)
  (room : RateRoom S (selectedHeaderLength B) (MapWitness.scanCoefficient B ord)
    (prologueCoefficient B) n)
  (level : site.levels - (site.passIndex + 1) ≤ (S.steps + 1) * (n.log2 + 1))
  (wire : X.maxWireWidth ≤ n)
  (hit : (canonicalParent site ord f hf).read node saved bits = some (body, tail))

include order room level wire hit in
/-- The selected parent parser leaves room for the dispatcher's probe and instructions. -/
theorem canonicalParent_rates :
    countProbes body.trace + 1 ≤
      probeRate S (MapWitness.scanCoefficient B ord) (prologueCoefficient B) * (n.log2 + 1) ∧
      body.trace.length + 9 ≤ n ^ 43 := by
  simp only [canonicalParent, parentParser] at hit
  obtain ⟨parent, _, read⟩ := Option.bind_eq_some_iff.mp hit
  let regions := TerminalLayout.privateRegions (slotDegree S) n site.rowEnd (Fintype.card B.Entry)
  refine selected_hook_rates B f hf i X sel v site.descriptor node order site.seed
    regions.arguments site.incidence site.mem site.older site.hiddenArgs
    (canonicalActions site ord f hf parent) site.publicData site.levels site.passIndex
    site.level ((MapResidentRows.siteIndex X v).val : Word w) saved bits tail body
    (MapWitness.scanCoefficient B ord) n room level wire ?_ read
  intro child _ hidden out es _ _ scan
  dsimp only [canonicalActions, typedActions, canonicalBank] at scan
  exact MapWitness.scan_bound B ord i X sel v _ _ site.mem site.level site.term site.source
    site.width _ _ node _ out es scan

include order room level wire hit in
/-- Every successful tape of the canonical parser gives an ordinal job with the
uniform scan coefficient of the installed resident maps. -/
theorem canonicalParent_ordinal_cost (offset : Word w) :
    ordinalJobCost n 1 (probeRate S (MapWitness.scanCoefficient B ord) (prologueCoefficient B))
      (dispatchJob site.mem offset node saved body) := by
  obtain ⟨probes, ticks⟩ :=
    canonicalParent_rates site ord f hf node order saved bits tail body room level wire hit
  exact dispatched_ordinal_cost site.mem offset node saved body probes ticks

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
