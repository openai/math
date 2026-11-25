import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProbeFixedCatalystDateFrames
import OAI.Hierarchy.ProbeFixedCatalystMask
import OAI.Hierarchy.ProbeFixedStripCounts

namespace OAI
/-! # Every purchased local date on the native priced calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart CatalystArchive
open BoughtSockets PurchaseStage StockBound StockCommit
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) {K H R : ℕ} (z width : ℕ)
  (b : JointHeader.Board) (cat : CatalogueRows.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "N" => Stages z (2^v.W)
local notation "w" => wordBits z (2^v.W) copies
variable (groups : Fin K≃AllGroups z (2^v.W))
  (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) H)
  (socket : BoughtSockets.Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel)) (r : ℕ) (banks : RouteSettlement.Banks)
  (src tab dst : ℕ) (owners : Bank)
local notation "P" => v.catalystPlacement z K dir.groups H R b cat socket
local notation "s" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "forms" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "incoming" => resolvedStock v.mesh A b.initial (build F s)
local notation "core" => CoreRoute.stop v.sampler z v.W k n v.depth K dir.groups H R

set_option cleanup.letToHave false in
/-- The original master tape supplies the permutation and stratum header.
The finite indices select the actual outer birth and the later priced stage. -/
def purchasedLocal (initial : Memory w) (π : Equiv.Perm (Fin (2^z)))
    (p : Fin (v.mesh.inject+v.mesh.cool)) (a : Fin v.mesh.outerFuel)
    (j : Fin v.mesh.reserveSteps) (t : Fin v.mesh.innerFuel) :
    let e:=Attempt.inner p.val a.val j.val t.val
    let before:=entryMemory C initial e
    Calendar.mounted C (events v.mesh) initial → v.stripHeight≤z → width≤2^z →
    heapEnd z (2^v.W) copies≤b.initial → core≤b.initial →
    DatedBoard F s v.mesh cat (P).routes π groups dir (.outer p a) (entryMemory C initial (.outer p a)) →
    ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊≤z →
    TrialLayout C e (forms e).pricedArea (forms e).stockSource (g e) v.keepLimit width ((A).base v.mesh (.attempt e)) →
    PurchasedLocal F s v.mesh cat (P).routes p a j.val t.val (incoming e) C before (g e) π groups dir v.copyScale width := by
  intro e before whole late payload heap coreEnd board calibrated layout
  have slot:=(inner_slot C initial p.val a.val j.val t.val p.isLt a.isLt j.isLt t.isLt whole).choose_spec
  have entered : Event.attempt e∈events v.mesh := by
    change Event.attempt e∈events (C).mesh
    rw [slot.events]
    simp [e]
  have ready:=entryMemory_ready C initial e whole entered
  let base:=(A).base v.mesh (.attempt e)
  have dated : (A).first≤base := Nat.le_add_right ..
  have old:=v.catalyst_bought_archive_room P z width p.val a.val j.val t.val
  have beforeStop : base≤(C).stopAt e:= (v.catalyst_birth_room P z width e).1.trans (min_le_left _ _)
  have mask:=v.catalystMaskBounds_at_height P z width r banks src tab dst owners calibrated e
  have frame:=v.catalyst_purchased_frame P z width r banks src tab dst owners initial p a j.val t.val whole entered
    mask (old.1.trans beforeStop)
  have born:=v.catalyst_birth (K:=K) (G:=dir.groups) (H:=H) (R:=R) z width b cat socket r banks src tab dst owners
    initial π p.val a.val j.val t.val whole p.isLt a.isLt j.isLt t.isLt heap coreEnd board.columns.geometry board.strata
  have installed : (C).commit e=pricedSegment (forms e).pricedArea (forms e).stockSource (g e) w
      (enabledBatch (forms e).market.layout (forms e).board) := rfl
  let funded:=build F (withPorts s v.mesh cat (P).routes) e (incoming e)
  have physical : funded=forms e :=
    congrArg (fun B=>build F B e (incoming e)) (v.catalyst_boards P z width)
  have commit : (C).commit e=pricedSegment funded.pricedArea funded.stockSource (g e) w
      (enabledBatch funded.market.layout funded.board) := by
    rw [physical]; exact installed
  have output : EventBoard (fresh funded.pricedArea funded.stockSource) w := by
    rw [physical]
    exact v.catalyst_cash_board P z width r banks src tab dst owners e layout
  have tableRoom:=v.purchased_table_room z late
  have mass:=v.date_copies z P width p.val a.val j.val t.val
  let E:=v.publicHeader P z width
  have portEnd : (StripChart.header F (withPorts s v.mesh cat (P).routes) e).stop≤base := by
    have bound:=congrArg StockCommit.PortHeader.stop (v.catalyst_header P z width e).symm
    exact bound.le.trans ((E.ports.end_le 0).trans ((v.catalyst_ports_le_first P z width).trans dated))
  have keyCore : (Public.keyHead v.sampler (P).routes.column z v.W k v.depth).stop≤core :=
    (Public.borders v.sampler (P).routes.column z v.W k n v.depth).2.trans (Nat.le_add_right ..)
  refine {priceAtTime:=deadline v.mesh v.finish (v.basePhase width) e
          bounds:=v.purchased_size_room P z width C before (g e) (forms e).stockSource
            (enabledBatch (forms e).market.layout (forms e).board) p.val a.val j.val t.val (incoming e) late payload ready installed
          frame:=frame
          bins:=rfl
          keyHeader:=rfl
          receipt:=born
          rooms:=⟨tableRoom.1,tableRoom.2.1⟩
          whole:=tableRoom.2.2.1
          stock:=tableRoom.2.2.2
          low:=base
          protect:=fun y hy=>(v.event_prefix P z width r banks src tab dst owners (.attempt e) y hy).1
          below:=v.catalyst_base_label P z width e
          portEnd:=portEnd
          keysEnd:=keyCore.trans (coreEnd.trans ((v.catalyst_initial_le_first P z width).trans dated))
          tileEnd:=old.2
          commit:=commit
          output:=output
          alphabet:=((v.payloadPacketMenu N).index ⊕ v.purchasePacketMenu.index)
          finite:=inferInstance
          catalogue:=v.dateMenu N
          includeMenu:=Sum.inr
          widths:=fun _=>rfl
          mass:=mass.2.2
          scale:=mass.1
          idle:=pairKeys (CoreBoard.Columns z (2^v.W)) k (Sum.inl 0,⟨0,v.positive⟩)}

/-- The price, stock address, and frozen memory used to attribute an admitted
inner row are those of its originating outer market on this mounted run. -/
def purchasedLocalAtBirth (initial : Memory w) (π : Equiv.Perm (Fin (2^z)))
    (p : Fin (v.mesh.inject+v.mesh.cool)) (a : Fin v.mesh.outerFuel)
    (j : Fin v.mesh.reserveSteps) (t : Fin v.mesh.innerFuel) :
    let e := Attempt.inner p.val a.val j.val t.val
    let outer := Attempt.outer p.val a.val
    let market := (forms outer).atTime v.mesh v.finish (v.basePhase width) outer
    let frozen := market.failures.pass.apply ((guard C outer).apply (trialState C initial p.val a.val))
    let stock := resolvedStock v.mesh A b.initial (build F (withPorts s v.mesh cat (P).routes)) outer
    Calendar.mounted C (events v.mesh) initial → v.stripHeight ≤ z → width ≤ 2^z →
    heapEnd z (2^v.W) copies ≤ b.initial → core ≤ b.initial →
    DatedBoard F s v.mesh cat (P).routes π groups dir outer (entryMemory C initial outer) →
    ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊ ≤ z →
    TrialLayout C e (forms e).pricedArea (forms e).stockSource (g e) v.keepLimit width ((A).base v.mesh (.attempt e)) →
    {entry : PurchasedLocal F s v.mesh cat (P).routes p a j.val t.val (incoming e) C
        (entryMemory C initial e) (g e) π groups dir v.copyScale width //
      entry.receipt.stock = stock ∧ entry.receipt.phase = market.phase ∧
      entry.receipt.price = market.temperature ∧ entry.receipt.kind = market.kind ∧
      entry.receipt.frozen = frozen} := by
  intro e outer market frozen stock mounted late small heap coreFits born calibrated window
  let entry := v.purchasedLocal (R:=R) z width b cat groups dir socket r banks src tab dst owners
    initial π p a j t mounted late small heap coreFits born calibrated window
  exact ⟨entry,rfl,rfl,rfl,rfl,rfl⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
