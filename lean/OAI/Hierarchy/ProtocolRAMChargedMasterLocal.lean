import OAI.Hierarchy.ProtocolRAMCorePointwise
import OAI.Hierarchy.ProtocolRAMEconomicPointwise
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMasterAll

namespace OAI
/-! # The complete charged input loader is pointwise in the incoming raw tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Calendar.CoreRoute Calendar.StripChart Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets
open BoughtSockets AdaptiveProbe CatalogueRows
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {z W k n edges R K H attempts phases X Y steps : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D

theorem chargedMasterWords_local (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) :
    AdviceLocal (chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj
      owners edges) := by
  have stat : AdviceLocal (staticWords (w:=Native.wordBits z D Native.copies) a id amt p o ci cj owners edges) := by
    intro m m' x same
    simp only [staticWords,mount,recipes,ownerAdvice,fillSegment,same]
  exact (JointHeader.words_local («N»:=scores) (k:=k) joint phase π (fun _=>0)).comp (E.ports.words_local.comp
    ((CoreRoute.low_local order M groups dir depth).comp
      (E.scalar.words_local.comp (E.vector_local.comp (P.words_local.comp ((AdviceLocal.fill _ _ _).comp stat))))))

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
