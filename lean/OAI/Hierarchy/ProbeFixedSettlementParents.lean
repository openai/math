import OAI.Hierarchy.ProbeFixedActivationParent
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe

namespace OAI
/-! # The parent's real fetched row and purchase code at every settlement date -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart PurchaseFrozen
open StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "d" => 2^v.W
local notation "W" => wordBits z d copies
local notation "G" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "fmt" => v.nativeFormats P z width
local notation "keys" => stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase

abbrev SettlementParents (m : Memory W) (π : Equiv.Perm (Fin (2^z))) : Prop :=
    ∀(u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel),
      let a:=Attempt.outer u.val h.val
      let sh:=v.frozenMarket P z width u h
      let frozen:=v.frozenInput P z width r banks src tab dst owners m u h
      ∃fixture : Memory W,sh.shelf.Incoming (k:=k) sh.sampler π sh.depth sh.phase sh.temperature sh.kind frozen ∧
        (∀i : Key z d k,sh.shelf.Prepared sh.sampler sh.depth fixture i frozen) ∧
        sh.rows≤2^(fmt a).batch.decisionBits ∧ (fmt a).batch.purchaseLink.lengthCode=.lit 1

/-- Each dated parent uses the stock run and the same immutable table of public
stratum keys. The chronological guard prepares its own actual sampler shelf. -/
theorem settlement_parents (m : Memory W) (π : Equiv.Perm (Fin (2^z)))
    {jobs : ℕ} {controller : Fin jobs→Market z d k} {raw : Boot.Tape z d}
    (boot : Boot.Receipt controller π raw m)
    (stock : StockBound.Run C (v.stockBanks P z width) m z (Stages z d) k (v.keepLimit*width))
    (heap : heapEnd z d copies≤(G).first) (room : (keys).stop≤(G).first) («public» : (keys).Loaded m) :
    v.SettlementParents P z width r banks src tab dst owners m π := by
  intro u h a sh frozen
  obtain ⟨fixture,incoming,prepared,_⟩:=v.activation_parent P z width r banks src tab dst owners m π u h
    u.isLt h.isLt stock.mounted_all boot.geometry heap room «public»
  exact ⟨fixture,incoming,prepared,v.activation_padded P z width u h,rfl⟩

/-- On the common original tape both the inclusive CT range and the immutable
stratum table follow from the single core allocation used by the terminal catalogue. -/
theorem settlement_parents_original {K H R : ℕ} (b : JointHeader.Board) (cat : CatalogueRows.Board)
    (groups : Fin K≃AllGroups z d)
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W
      (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) H)
    (socket : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (order : Fin R≃Edges v.sampler z d k) (M : ℕ) (π : Equiv.Perm (Fin (2^z))) (m : Memory W)
    {jobs : ℕ} {controller : Fin jobs→Market z d k} {raw : Boot.Tape z d}
    (boot : Boot.Receipt controller π raw m) (seen : CoreRoute.Seen order M groups packed socket v.depth π m)
    (allocated : CoreRoute.stop v.sampler z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)
      v.depth K packed.groups H R≤b.initial) :
    let place:=v.catalystPlacement z K packed.groups H R b cat socket
    let chart:=v.nativeChart place z width r banks src tab dst owners
    StockBound.Run chart (v.stockBanks place z width) m z (Stages z d) k (v.keepLimit*width) →
    v.SettlementParents place z width r banks src tab dst owners m π := by
  intro place chart stock
  let n:=(v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
  let base:=CoreCatalogue.top z v.W K packed.groups H R
  have cover:=(CoreRoute.column_bounds v.sampler z v.W k n v.depth K packed.groups H R b.initial allocated).2
  have keysEnd := (BoughtSockets.Public.borders v.sampler base z v.W k n v.depth).2
  have header : (BoughtSockets.Public.keyHead v.sampler base z v.W k v.depth).stop≤b.initial :=
    keysEnd.trans ((Nat.le_add_right ..).trans allocated)
  have fixedFloor:=v.catalyst_initial_le_first place z width
  exact v.settlement_parents place z width r banks src tab dst owners m π boot stock
    (cover.ct.trans fixedFloor) (header.trans fixedFloor) seen.board.rom.keys

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
