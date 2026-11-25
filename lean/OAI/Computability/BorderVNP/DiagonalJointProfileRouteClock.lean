import OAI.Computability.BorderVNP.DiagonalNativeProfileDirectory
import OAI.Computability.BorderVNP.CubeRoutePinnedSchedule
import OAI.Computability.BorderVNP.RoutingISASignedPrepPublic

/-! # Joint profile publication and four-pass transmission on the same native execution -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Pins RoutingISA.Evaluator Transmission
open PackedHistoryCircuit Packing BorderVNP.Cube BorderVNP.Cube.Physical LocalRow
open private groups_deterministic from OAI.Computability.BorderVNP.RoutingISASignedPrepPublic

/-- The actual boot, substituted pin, reconstructed geometry, demand publication and
group schedule lead directly into the real send/receive passes. The startup and the
sparse-literal scan are charged once even though their code occurs in the profile
reader and the route estimate uses the same allowances. -/
theorem profile_route_visit_charge {w k : ℕ} (f : BroadcastFrame) {pub : Arg → Word w}
    {mac : TeamOpcode.Macros w 8} {bank : Bank w} {initial : Memory w} {es z saved}
    (boot : Runs pub mac JointHeader.bootHeader bank initial es z saved) (stable : f.Stable (readings z))
    (positive : (saved f.dst).val ≠ 0)
    (pins : (Fin k → Bool) ≃ Pins.Return pub mac (Function.update z 10 (saved f.dst)) saved)
    (streams : ∀ b, (pins b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (profile : (Fin k → Bool) ≃ Returns (withStartup pinGeometry) pub mac bank initial)
    (guesses : ∀ b, (profile b).val.1.flatMap TeamRAM.Event.choices = List.ofFn b)
    (b : Fin k → Bool) (geometry count teams sites : ℕ) (ar : CubeArena.Layout) (dir : Directory.Layout)
    {R : ℕ} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration ar.n ar.header.d}
    {group : Fin ar.header.d → Fin (R+1)} (layout : Pins.Layout) (scheduled : ℕ) {pass : Prop}
    (paid : traceCost (profile b).val.1 ≤ jointBudget count w+f.readTicks+2+
      (pinSetup.slots+17*(f.processors*f.literal)+1)+geometry)
    (directory : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac
      (profile b).val.2.1 (profile b).val.2.2)
    (scan : traceCost directory.val.1 ≤ deliveryScanTicks dir.entries teams sites)
    (clocked : PublicSchedule ar dir pp lp owner decl group layout pub mac directory.val.2.1 directory.val.2.2 scheduled pass)
    (before : Returns (beforeRoute epochPlacement (scheduleGroups ar.n (Tally.selectorWidth ar.n ar.K ar.h))) pub mac
      (pins b).val.2.1 (pins b).val.2.2)
    (routed : Returns route pub mac before.val.2.1 before.val.2.2)
    (l : TableLayout) (row : ℕ → TableRow) (al : l.Allocated w) (ordered : l.Ordered) (rows : l.RowsFit w row)
    (frame : (pub 0).val=l.frame) (loaded : l.frameFields (readings before.val.2.2))
    (original : l.recordsMatch row (readings before.val.2.2)) (atFrame : f.At (readings pub) (readings before.val.2.2))
    (fit : f.Fits w (pub 0).val) (size : f.teams=l.teams)
    (capacity : ∀ u v, f.header+Routing.legLoad al.teamCount (l.widthMatrix row) u v+
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (ranges : ∀ mt : Memory w, l.Image row (readings before.val.2.2) (readings mt) → RouteRanges l pub mt) :
    ∃ mt : Memory w, l.Image row (readings before.val.2.2) (readings mt) ∧
      traceCost es+2+traceCost (pins b).val.1+traceCost before.val.1+traceCost routed.val.1 ≤
        coreTicks count f l row (tableRange l mt) (directoryFrame pub mt 0) +
          (geometry+ScheduleClock.beforeDirectory teams sites dir.entries+scheduled) := by
  let upperFront := traceCost es+2+traceCost (pins b).val.1+traceCost before.val.1
  let groupTicks := geometry+ScheduleClock.beforeDirectory teams sites dir.entries+scheduled
  obtain ⟨actual,groupRun,_,cost⟩ := beforeRoute_after_profile f boot stable positive pins streams profile guesses b
    ar.n (Tally.selectorWidth ar.n ar.K ar.h) before
  obtain ⟨esame,bsame,msame⟩ := actual.property.unique_of_deterministic (by decide) directory.property
  have identical : actual = directory := Subtype.ext (Prod.ext esame (Prod.ext bsame msame))
  subst actual
  obtain ⟨_,_,_,actualSchedule,_,groupCost⟩ := clocked.1 (clocked.2 groupRun.property).1
  have groupBound : traceCost groupRun.val.1 ≤ scheduled := by
    rw [(groupRun.property.unique_of_deterministic (groups_deterministic ..) actualSchedule.runs).1]
    exact groupCost
  have scanBound : traceCost directory.val.1 ≤ ScheduleClock.beforeDirectory teams sites dir.entries := by
    simpa only [deliveryScanTicks,ScheduleClock.beforeDirectory,Nat.add_assoc] using scan
  change upperFront = _ at cost
  have prior : upperFront ≤ (jointBudget count w+f.readTicks+2)+(pinSetup.slots+17*(f.processors*f.literal)+1)+groupTicks := by
    dsimp only [groupTicks]
    omega
  obtain ⟨mt,image,physical⟩ := coreTicks_covers_profile_route l row pub mac before.val.2.1 before.val.2.2
    al ordered rows frame loaded original f atFrame fit size capacity ranges count upperFront groupTicks prior
  exact ⟨mt,image,physical routed⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
