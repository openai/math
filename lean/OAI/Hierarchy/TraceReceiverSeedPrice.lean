import OAI.Hierarchy.TraceReceiverSeedWords
import OAI.Hierarchy.TraceSeedCharge
import OAI.ThreeFlat.Diagonal.HistoryInitialCharge

namespace OAI
/-! # Physical gate and data-pointer charges for all native seed trees -/

noncomputable section
namespace Hierarchy.TraceReceiverSeedWords
open ThreeFlat Diagonal Diagonal.LaneCursor Diagonal.LaneCursor.RowLayout
open Diagonal.HistoryContraction Diagonal.TraceSourceOwner TraceDistribution
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical BigOperators

variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
    (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^W) (st : Word W) (B : PhysicalStage.Block F) (hk : 2≤k+1)
set_option quotPrecheck false

local notation "I" => bitIndex hF t.width t.labels base st t.header t.time regs words t.grid
local notation "depth" => (k+1)+low
local notation "off" => 1+(depth+depth)
local notation "G" => TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words depth
local notation "desc" => TraceSourceOwner.shape W pc regs words S fuel depth (G).internal
local notation "L" => wordsLayout M t hF st B hk
local notation "V" => PairedCursor.Site (k+1)

theorem billed_resources (v : V) :
    (forest M t hF st B hk v).resources ≤ 1+(L).ports.halfBits v+
      (if v.1=0 then TraceBitHeader.seedTraceWork low (desc).stride (G).cells B.cursorCopies depth else 0) := by
  by_cases first : v.1=0
  · let addr := bitAddress hF t.width t.labels base st t.header t.time regs words t.grid v.2 (I v.2)
    have cap := (I v.2).rectangular_charge (r:=B.cursorCopies) addr v.1 rfl rfl
    have tree : (forest M t hF st B hk v).resources ≤
        TraceBitHeader.seedTraceWork low (desc).stride (G).cells B.cursorCopies depth := by
      simpa only [forest,dite_eq_left first,Tree.resources_atom,BitNetwork.restrictPins,
        TraceBitHeader.seedTraceWork,addr] using cap
    refine tree.trans ?_
    rw [ite_eq_left first]
    exact Nat.le_add_left _ _
  · have cap := (I v.2).relay_resources_le (r:=B.cursorCopies) v.1
    have width := B.cursor_half_width hk low off (G).cells (width M t hF st)
      (fun z (x : Fin S → Bool) j => x (source M t hF st z j)) v
    change (B.cursorCopies+1)*2*(I v.2).t+(B.cursorCopies+1)*2*(I v.2).t=(L).ports.halfBits v at width
    have tree : (forest M t hF st B hk v).resources ≤ 1+2*((B.cursorCopies+1)*2*(I v.2).t) := by
      simpa only [forest,dite_eq_right first,Tree.resources_atom,BitNetwork.restrictPins,
        BucketIndex.initialNetwork] using cap
    have measured : 2*((B.cursorCopies+1)*2*(I v.2).t)=(L).ports.halfBits v :=
      (two_mul _).trans width
    exact (tree.trans_eq (congrArg (fun q : ℕ => 1+q) measured)).trans_eq
      (by rw [ite_eq_right first]; exact (Nat.add_zero _).symm)

theorem external_total : (∑ v : V, width M t hF st v)=S := by
  let e := Equiv.ofBijective _ (source_bijective M t hF st)
  simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr e


end Hierarchy.TraceReceiverSeedWords

end
end OAI
