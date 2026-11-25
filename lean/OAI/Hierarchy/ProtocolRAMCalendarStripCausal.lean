import OAI.Hierarchy.ProtocolRAMCalendarPostCausal
import OAI.Hierarchy.ProtocolRAMCalendarCommitCausal
import OAI.Hierarchy.ProtocolRAMCalendarMarketBelow
import OAI.Hierarchy.ProtocolRAMCalendarStripPrivate

namespace OAI
/-! # The executable priced chart is causal in its chronological private inputs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage
open StripDirectory
open scoped Classical Fin.CommRing
variable {z d k q depth r : ℕ}
local notation "stageCount" => List.length (Fabric.shapes (permutationFabric z d))
local notation "W" => wordBits z d copies
variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial width cap : ℕ) (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "A" => arena v s
local notation "B" => install v s c
local notation "S" => catalogue.sink r banks src tbl dst owners
local notation "C" => chart F c A initial width cap B finish prices catalogue r banks src tbl dst owners
local notation "p" => formats F c A initial B

theorem after_below (e : Event) (m m' : Memory W) (cut : ℕ) (h : Below cut m m')
    (high : (A).base c e+(A).stride≤cut) (rdy : ready C e m) (rdy' : ready C e m') :
    Below cut (after C e m) (after C e m') := by
  cases e with
  | feed b =>
    let L:=FeedLayout.atEvent (N:=stageCount) c A p initial width cap b
    apply h.passes
    intro t member
    have hi:= L.generated_extent C b rfl t member
    have reserve : goods z d k+goods z d k≤(A).stride := by
      change goods z d k+goods z d k≤ stride v s
      unfold stride
      omega
    change t.out+t.rows≤(A).base c (.feed b)+goods z d k+goods z d k at hi
    exact ⟨rdy t member,by omega⟩
  | attempt a =>
    obtain ⟨guardFit,frozenFit,wide,tests,mask,_,audit,_,receipt,_,stock,_,_⟩:=rdy
    let v' := (p a).atTime c finish prices a
    let L := (C).layout a
    let R := repair C a
    let pre := guard C a
    have limits := bounds (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners a cut high
    have lower := h.pass pre guardFit ((Nat.le_add_right ..).trans limits.guard)
    have packed : v'.flags≤cut := by
      have hi:=limits.frozen
      change max _ (v'.flags+v'.rows)≤cut at hi
      exact (Nat.le_add_right ..).trans ((Nat.le_max_right ..).trans hi)
    have frozen := v'.prefix_below (pre.apply m) (pre.apply m') frozenFit rdy'.2.1 packed lower
    have snap : Below cut (postSnapshot L R (prepared C a m)) (postSnapshot L R (prepared C a m')) :=
      frozen.snapshot L R tests ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans limits.excess))
        ((Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans limits.payload))
        ((Nat.le_add_right ..).trans limits.discrepancy) mask ((Nat.le_add_right ..).trans limits.mask)
    have post := snap.verdict L R audit ((Nat.le_add_right ..).trans limits.keys)
      (fun t ht=>(Nat.le_add_right ..).trans (limits.writes t ht))
      receipt ((Nat.le_add_right ..).trans limits.verdict)
    exact (p a).pricedCommit_agree S catalogue.idBase (header F B a).fieldTerm (id F B catalogue a) _
      _ _ ((fit v s F c initial a).trans high) stock post

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
end

end OAI
