import OAI.Hierarchy.ProbeFixedPostprocessing
import OAI.Hierarchy.ProbeFixedDatedGuard
import OAI.Hierarchy.ProbeFixedPriceLabelFits
import OAI.Hierarchy.ProbeFixedStockOriginal
import OAI.Hierarchy.ProtocolRAMCalendarPreDirectory

namespace OAI
/-! # Joining the frozen purchase, score checks and physical sparse settlement at one actual date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StockBound StockCommit
open StripChart StripDirectory CatalogueRows BoughtSockets PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (z width r K G H R idBase : ℕ) (joint : JointHeader.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
variable (origin : Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
local notation "s" => v.sampler
local notation "dir" => Public.join origin s z v.W k v.depth K G H R
local notation "cat" => liveBoard dir s z v.W k v.depth R K G H (CoreCatalogue.pointBits z v.W) idBase
local notation "P" => v.catalystPlacement z K G H R joint cat origin
local notation "A" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
local notation "W" => wordBits z (2^v.W) copies
local notation "coreEnd" => CoreRoute.stop s z v.W k n v.depth K G H R
variable (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "stamp" => v.stamp P z width r banks src tab dst owners

/-- All immutable headers, historical controls, sparse owner reads, counts, and signed
account operands of an actual trial are discharged here. The only computation-sensitive
inputs at the current date are the mounted frozen sampler and its three measured sums. -/
theorem trial_ready (a : Attempt) (scheduled : Event.attempt a∈events v.mesh)
    (allocated : coreEnd≤joint.initial) (room : (A).endAddress v.mesh<2^W)
    (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W) (widthWord : width<2^W)
    (alphabet : v.menu.alphabet≤2^W) (counters : v.menu.alphabet*width<2^W)
    (start fixture : Memory W)
    (original : Original (f a) (stamp a) (StripChart.start (v.nativeBoards P z width) a) (A).first start fixture)
    («prefix» : Calendar.mounted C ((events v.mesh).take (position v.mesh (.attempt a))) start) :
    let m:=state C start (position v.mesh (.attempt a))
    ((C).frozen a).ready ((guard C a).apply m) →
    TestsReady (repair C a) (prepared C a m) → ready C (.attempt a) m := by
  intro m fr tests
  let B:=repair C a
  let L:=(C).layout a
  let ff:=f a
  let g:=stamp a
  let h:=ff.occurrenceHeader (StripChart.start (v.nativeBoards P z width) a)
  let out:=postOutput L B (prepared C a m)
  have raw:=v.fixed_post z width r K G H R idBase joint origin banks src tab dst owners
    a scheduled allocated room threshold widthWord alphabet counters
  obtain ⟨board,mask,maskSpace,auditsOk,ordered,verdictFits,verdictSpace⟩:=raw
  have outsideFirst (e : Event) (x : ℕ) (hx : x<(A).first) : protected C x e ∧ outside C x e :=
    v.event_prefix P z width r banks src tab dst owners e x (hx.trans_le (Nat.le_add_right ..))
  have pub : h.Loaded out := by
    apply original.header.frame
    intro x _ low
    have initial := low.trans_le original.headLow
    have earlier:=StockBound.prefix_low C start (position v.mesh (.attempt a)) (A).first «prefix»
      (fun e _ j hj=>(outsideFirst e j hj).2)
    exact (before_commit_cell C a m x fr (auditsOk _) (outsideFirst _ x initial).1).trans (earlier x initial)
  obtain ⟨owner,parity,directory⟩:=ff.commit_ports h.start out original.sealed original.count pub
  have occ:=v.election_key_room z K G H R joint cat origin allocated
  have source:=v.stock_prefix_native P z width a occ
  have space:=((v.attempt_room P z width a).trans ((A).within v.mesh _ scheduled)).trans_lt room
  have gfit : g.out<2^W:=verdictSpace
  have label:=v.price_label_fits (K:=K) (G:=G) (H:=H) (R:=R) (idBase:=idBase) z width joint origin
    r banks src tab dst owners a allocated gfit
  have signed : ((C).commit a).ready out :=
    pricedSegment_ready ff.pricedArea ff.stockSource g (enabledBatch L B) out source
      (PrefixAgreement.inputEnd_of_fits _ label) le_rfl (owner.trans original.preLabels)
      (parity.trans original.preLabels) space directory
  have keeps:=v.dated_keeps P z width r banks src tab dst owners a board
  have pos : 0<W:=by
    unfold wordBits
    omega
  exact ⟨v.dated_guard P z width r banks src tab dst owners a scheduled room,fr,pos,tests,mask,
    maskSpace,auditsOk _,ordered,verdictFits,verdictSpace,signed,keeps⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
