import OAI.Hierarchy.ProtocolRAMCatalystArchiveMasterAll
import OAI.Hierarchy.ProtocolRAMCoreCatalogueBoot

namespace OAI
/-! # All ten original catalogue columns after the charged CT boot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar Calendar.CoreRoute Calendar.StripChart Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets
open BoughtSockets AdaptiveProbe CatalogueRows
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {z W k w n edges : ℕ}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "r" => Fintype.card (Slots z D k)

variable {attempts R K H jobs phases X Y steps size : ℕ} {S : PurchaseSampler}


open CoreCatalogue
theorem charged_master_core_header (E : EconomicHeader phases X Y steps) (P : MenuROM.Charges) (empty : Bank)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D)
    (markets : Fin jobs→Market z D k) (size : ℕ)
    (coreEnd : CoreRoute.stop S z W k attempts depth K dir.groups H R≤joint.initial)
    (ports : joint.initial≤E.ports.base) (allocated : joint.initial≤ size)
    (marketsLow : ∀j,joint.initial≤Boot.low (markets j)) :
    let words:=chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges raw
    let mid:=Boot.booted markets size words
    Boot.Receipt markets π (Computability.VPVNP.RAMMemory.initialMemory size words) mid →
      Header order (headBase z W K dir.groups H) attempts (groupStart z W) M mid := by
  intro words mid boot
  let extra:=staticWords a id amt p o ci cj owners edges raw
  let econ:=E.scalar.words (E.vectorMemory (P.words (reserveWords empty extra)))
  let topAt:=top z W K dir.groups H R
  let endAt:=CoreRoute.directoryBase S z W k attempts depth K dir.groups H R
  let input:=Public.load S topAt z W k attempts depth (CoreLookup.mount endAt order econ)
  have stored : Header order (headBase z W K dir.groups H) attempts (groupStart z W) M
        (initial order M groups dir input) := by
    intro field row
    exact mountHeader_read order (headBase z W K dir.groups H) attempts (groupStart z W) M _ field row
  apply stored.frame
  intro x lo hi
  have lower : groupStart z W≤headBase z W K dir.groups H:=by
    unfold headBase SiteROM.endAddress superStart
    omega
  have head : headBase z W K dir.groups H+headerWords R≤topAt:=(le_max_left ..).trans (le_max_right ..)
  obtain ⟨keys,outer⟩:=Public.borders S topAt z W k attempts depth
  have topLow : topAt≤endAt:=(Nat.le_add_right ..).trans (keys.trans outer)
  have before : x<joint.initial := hi.trans_le (head.trans (topLow.trans ((Nat.le_add_right ..).trans coreEnd)))
  have address : groupStart z W≤x:=lower.trans lo
  have read:=boot.kept x ((le_max_left ..).trans address)
    (fun j hit=>Nat.not_lt_of_ge hit.1 (before.trans_le (marketsLow j)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (before.trans_le allocated)] at read
  exact read.trans (CoreCatalogue.master_retains order M groups dir joint E.ports scores phase π (fun _=>0)
    input x ((le_max_right ..).trans address) before (before.trans_le ports))

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
