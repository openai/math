import OAI.Computability.BorderVNP.DiagonalNativePreparedRoute
import OAI.Computability.BorderVNP.RoutingISAEvalCoreTicks
import OAI.Computability.BorderVNP.DiagonalNativeSignedTags

/-! # The measured cost of the four real routing passes at a prepared signed branch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP BurstRAM Transmission Finset TeamContraction.ProcessorSlots
open private route_iff from OAI.Computability.BorderVNP.DiagonalNativeRoute
open private prepare_iff from OAI.Computability.BorderVNP.DiagonalNativePreparedRoute
variable {w : ℕ}

/-- The native range scan pays the selected role's real per-bit rate, including the
smaller rate for outbound original data. This holds for every accepted word spelling. -/
theorem transmission_image_cost {l : TableLayout} {row : ℕ → TableRow} {before : ℕ → ℕ}
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : l.Image row before (readings m)) (al : l.Allocated w) (ordered : l.Ordered)
    (rowsFit : l.RowsFit w row) (initial : l.recordsMatch row before) (hf : (pub 0).val=l.frame)
    (loaded : l.frameFields before) (f : BroadcastFrame) (atFrame : f.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (teams : f.teams=l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (ranges : RouteRanges l pub m) (z : TableReturn pub mac s m) :
    let team := directoryFrame pub m 0
    traceCost z.val.1 ≤ setup.slots+(20+decision.depth)*l.count+
      (∑ i ∈ range l.count, (tableRange l m i).teamCost team)+1 := by
  intro team
  let a := Schedule.of_table image al pub hf loaded f atFrame fit teams capacity
  let rows := tableRange l m
  have count := image_count image al pub hf loaded
  have spans (i : ℕ) (hi : i < (directoryFrame pub m 13).val) : ScheduledRange f _ (rows i) :=
    ScheduledRange.of_table image al rowsFit initial f teams (count ▸ hi)
  have teamVal : team.val = f.team := by simpa [team,directoryFrame,frameField,readings] using a.frame.1
  have table := image_directory image al pub hf loaded
    (fun i hi => Range.directorySeparated_of_ordered ordered _ _ (ranges.destinations i hi))
  have safe := allTableArithmetic rows team a teamVal (directoryFrame pub m 13).val spans
    (fun i hi => teams.symm ▸ Range.scheduleSeparated_of_ordered image ordered pub hf loaded _ _ (ranges.destinations i (count ▸ hi)))
  obtain ⟨bits,permit,_,stream⟩ := table_sound rows pub mac m s table safe z.property
  have cost := (table_return_effects rows pub mac m s bits (table bits) permit z stream).2.1
  simpa only [count] using cost

/-- Charge the exact startup, pin and all four routing stages to the paper's physical core
budget. The post-schedule row fields are read from the actual returned scheduler memory. -/
theorem coreTicks_covers_route (l : TableLayout) (row : ℕ → TableRow) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (al : l.Allocated w) (ordered : l.Ordered) (rowsFit : l.RowsFit w row)
    (hf : (pub 0).val=l.frame) (loaded : l.frameFields (readings m)) (initial : l.recordsMatch row (readings m))
    (f : BroadcastFrame) (im : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (teams : f.teams=l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (ranges : ∀ mt : Memory w, l.Image row (readings m) (readings mt) → RouteRanges l pub mt)
    (used pinTicks count : ℕ) (startup : used ≤ jointBudget count w+f.readTicks+2)
    (pins : pinTicks ≤ pinSetup.slots+17*(f.processors*f.literal)+1) :
    ∃ mt : Memory w, l.Image row (readings m) (readings mt) ∧
      ∀ z : Returns route pub mac s m, used+pinTicks+traceCost z.val.1 ≤
        coreTicks count f l row (tableRange l mt) (directoryFrame pub mt 0) := by
  obtain ⟨es,t,mt,pre,ct,_,image⟩ := scheduleTable_image pub mac s m l row al rowsFit hf loaded initial
  change l.Image row (readings m) (readings mt) at image
  have test := route_checks pub mac t mt image al ordered rowsFit hf loaded f im fit teams capacity
  refine ⟨mt,image,?_⟩
  rintro ⟨⟨fs,q,mq⟩,go⟩
  obtain ⟨x,mx,as,bs,rfl,begin,transmit⟩ := Runs.seq_iff.mp (route_iff.mp go)
  obtain ⟨y,my,cs,ds,rfl,schedule,checks⟩ := Runs.seq_iff.mp begin
  obtain ⟨rfl,rfl,rfl⟩ := schedule.unique_of_deterministic (by decide) pre
  obtain ⟨rfl,passed⟩ := test.sound checks
  obtain ⟨hs,_,valid,cost⟩ := test.complete passed
  obtain ⟨rfl,_,_⟩ := checks.unique_of_deterministic (by decide) valid
  have scan := transmission_image_cost pub mac x _ image al ordered rowsFit initial hf loaded f
    (image.broadcast_of_ordered ordered hf im) fit teams capacity (ranges _ image) ⟨(bs,q,mq),transmit⟩
  change used+pinTicks+traceCost ((cs++ds)++bs) ≤ _
  simp only [traceCost,VPVNP.RAMBuckets.cost_append] at ct cost scan ⊢
  unfold coreTicks routingCheckTicks
  omega

/-- Charge the same routing kernel when the physical history interpreter already supplies
a combined startup, pin and pre-route charge. The arithmetic cancels both fixed prefix
allowances, which prevents charging the literal input scan twice. -/
theorem coreTicks_covers_profile_route (l : TableLayout) (row : ℕ → TableRow) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (al : l.Allocated w) (ordered : l.Ordered) (rowsFit : l.RowsFit w row)
    (hf : (pub 0).val=l.frame) (loaded : l.frameFields (readings m)) (initial : l.recordsMatch row (readings m))
    (f : BroadcastFrame) (im : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (teams : f.teams=l.teams)
    (capacity : ∀ u v, f.header + Routing.legLoad al.teamCount (l.widthMatrix row) u v +
      Routing.legLoad al.teamCount (l.widthMatrix row) v u ≤ f.capacity)
    (ranges : ∀ mt : Memory w, l.Image row (readings m) (readings mt) → RouteRanges l pub mt)
    (count prefixCost beforeTicks : ℕ)
    (paid : prefixCost ≤ (jointBudget count w+f.readTicks+2)+(pinSetup.slots+17*(f.processors*f.literal)+1)+beforeTicks) :
    ∃ mt : Memory w, l.Image row (readings m) (readings mt) ∧
      ∀ z : Returns route pub mac s m, prefixCost+traceCost z.val.1 ≤
        coreTicks count f l row (tableRange l mt) (directoryFrame pub mt 0)+beforeTicks := by
  obtain ⟨mt,image,cost⟩ := coreTicks_covers_route l row pub mac s m al ordered rowsFit hf loaded initial
    f im fit teams capacity ranges (jointBudget count w+f.readTicks+2) (pinSetup.slots+17*(f.processors*f.literal)+1)
    count le_rfl le_rfl
  exact ⟨mt,image,fun z => by have hz := cost z; omega⟩

/-- Decompose the true public preparation trace into the deterministic public table work,
the four charged routing passes, and the true local input construction. -/
theorem preparation_charges {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m}
    (epochs groups args : Code) (z : Returns (prepareExpansion epochs groups args) pub mac s m) :
    ∃ p : Returns (beforeRoute epochs groups) pub mac s m,
      ∃ r : Returns route pub mac p.val.2.1 p.val.2.2,
        ∃ a : Returns args pub mac r.val.2.1 r.val.2.2,
          z.val.2 = a.val.2 ∧ traceCost z.val.1 = traceCost p.val.1+traceCost r.val.1+traceCost a.val.1 := by
  obtain ⟨u,mu,bs,other,ev,pre,tail⟩ := Runs.seq_iff.mp ((prepare_iff epochs groups args).mp z.property)
  obtain ⟨v,mv,rs,gs,rfl,route,input⟩ := Runs.seq_iff.mp tail
  refine ⟨⟨(bs,u,mu),pre⟩,⟨(rs,v,mv),route⟩,⟨(gs,z.val.2),input⟩,rfl,?_⟩
  rw [ev]
  simp only [traceCost,VPVNP.RAMBuckets.cost_append,Nat.add_assoc]

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
