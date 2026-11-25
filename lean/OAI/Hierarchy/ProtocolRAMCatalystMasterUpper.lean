import OAI.Hierarchy.ProtocolRAMCatalystArchiveMasterAll
import OAI.Hierarchy.ProtocolRAMBootHigh

namespace OAI
/-! # High private words survive the original charged boot and all six mounted ROMs -/
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

theorem booted_master_upper (E : EconomicHeader phases X Y steps) (ord : E.Ordered)
    (P : MenuROM.Charges) (empty : Bank) (firstCharge : P.payload.base=E.stop)
    (secondCharge : P.purchase.base=P.payload.stop) (reserveBase : empty.base=P.stop)
    (order : Fin R≃Edges S z D k) (M : ℕ) (groups : Fin K≃AllGroups z D)
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (scores depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (a : ReserveUse.Archive) (id amt : Fin n→ℕ)
    (p : Recipes) (o : Orders z D k) (ci : Commodity (Fin (2^z)) N k→ℕ) (cj : Columns z D×Fin k→ℕ)
    (owners : Bank) (edges : ℕ) (raw : Boot.Tape z D)
    (space : StaticSpace a p owners n r edges (Native.wordBits z D Native.copies))
    (tail : empty.base+empty.size≤a.kind.base) (first : 2^z≤joint.initial)
    (scoreEnd : JointHeader.stop joint z scores k phases≤E.ports.base)
    (board : CoreRoute.stop S z W k attempts depth K dir.groups H R≤joint.initial)
    (markets : Fin jobs→Market z D k) (oldSize x : ℕ) (layout : Boot.Layout markets oldSize)
    (inTape : x<size) (heap : oldSize≤x) (high : owners.base+owners.size≤x) :
    Boot.booted markets size (chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges raw) x=raw x := by
  let words:=chargedMasterWords E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges raw
  have authentic:=chargedMasterWords_authentic E P empty order M groups dir joint scores depth phase π a id amt p o ci cj owners edges raw first
  have receipt:=(Boot.start markets (layout.extend (heap.trans inTape.le)) (Nat.two_pow_pos W) π words authentic).2
  exact (receipt.high inTape (layout.subdivision.trans heap) (fun i=>(layout.extent i).trans heap)).trans
    (chargedMasterWords_above E ord P empty firstCharge secondCharge reserveBase order M groups dir joint scores depth phase π
      a id amt p o ci cj owners edges raw space tail first scoreEnd board x high)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
