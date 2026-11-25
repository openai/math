import OAI.Computability.BorderVNP.DiagonalNativeRouteWindow
import OAI.Computability.BorderVNP.PackedRoutingPublishedRun
import OAI.Computability.BorderVNP.RoutingISAScheduleClockPhases
import OAI.Computability.BorderVNP.RoutingISAScheduleClockRuns
import OAI.Computability.BorderVNP.GeometryAdviceFrame

/-! # The real geometric profile and demand-directory clock before routing -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP VPVNP.BurstRAM Crossing GeometryFrameEncoding GeometryAdvice Packing
open BorderVNP.Cube CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs
open private seq_assoc from OAI.Computability.BorderVNP.RoutingISABlockAppend

variable {w u o b : ℕ}

set_option maxRecDepth 4000 in
/-- A returning reconstruction has the charged true geometry result, including the
memory frame, even when its interpreter contains dormant free-input instructions. -/
theorem geometry_return_cost (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : BroadcastFrame) (a : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool) (fit : f.Fits w (pub 0).val)
    (space : a.Fits f w (pub 0).val) (layout : GeometryOutput.Placement pub l base start a.dense src t)
    (input : PhysicalInput pub m f a L P l base start src t x)
    (r : Returns reconstruct pub mac s m) :
    GeometryOutput.validBit t (Sum.elim x Fin.elim0)=true ∧
      traceCost r.val.1 ≤ GeometryAdviceRate.ticks t.size u o b w ∧
      GeometryOutput.Result (a.image f.stride m (a.words*w)) r.val.2.2 l base start t x := by
  have ok : GeometryOutput.validBit t (Sum.elim x Fin.elim0)=true := by
    by_contra failed
    exact reconstruct_invalid pub mac s m f a L P l base start src t x fit space layout input
      (Bool.eq_false_iff.mpr failed) r.property
  obtain ⟨es,z,mz,run,charge,empty,result⟩ := reconstruct_runs pub mac s m f a L P l base start src t x
    fit space layout input ok
  obtain ⟨events,_,memory⟩ := DiagonalResidueRAM.unique_returns (c := reconstruct) (by decide)
    run r.property (tail := r.val.1.flatMap TeamRAM.Event.choices) (tail' := []) (by simp [empty])
  rw [←events,←memory]
  refine ⟨ok,?_,result⟩
  simpa only [GeometryAdvice.cost,GeometryOutput.stagedTicks,GeometryOutput.packetCount,
    GeometryAdviceRate.ticks,GeometryAdviceRate.packetWords,Nat.add_assoc] using charge

private theorem before_iff (dim bits : ℕ) {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m es z mz} :
    Runs pub mac (beforeRoute epochPlacement (scheduleGroups dim bits)) s m es z mz ↔
      Runs pub mac (.seq reconstruct (.seq (.seq PrivatePlacement.program Directory.ISA.program)
        (scheduleGroups dim bits))) s m es z mz := by
  change Runs pub mac (.seq (.seq reconstruct PrivatePlacement.program) (.seq _ _)) s m es z mz ↔ _
  rw [←seq_assoc]
  simp only [Runs.seq_iff (a := reconstruct),seq_assoc]
  rfl

variable {D sites wires ports cells axes k digit : ℕ} {Port : Type*} [Fintype Port] {width : Port → ℕ}
variable {σ : Type*} [Fintype σ]

/-- Starting from the true profile circuit and the real network placements, every completed
before-route pass has the charged public clock. The third stage reads the directory produced
by the first two in the same memory, with the actual published seven-word rows. -/
theorem published_before_cost (dir : Directory.Layout) (N : Network D Port width) (cell : N.Site → Fin cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin wires)
    (portID : Port ↪ Fin ports) (F : Fields sites wires ports cells axes k digit σ) {bits : σ → Bool}
    (net : Represents N cell aux siteID edgeID portID F bits) (code : ∀ c, (F.cells c).val = c.val)
    (wordFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^digit)
    (original : Fin dir.entries → N.Site) (live : Fin (dir.teams*dir.sites) → Port)
    (origin base gap extent : ℕ) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (f : BroadcastFrame) (a : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (g : GeometryOutput.Layout) (work start : ℕ) (src : Fin u → ℕ)
    (t : Table (Fin u ⊕ Fin 0) o b) (x : Fin u → Bool)
    (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val)
    (placed : GeometryOutput.Placement pub g work start a.dense src t)
    (input : PhysicalInput pub m f a L P g work start src t x)
    (bounds : dir.DestinationBounds) (teams : 0 < dir.teams) (fields : 0 < dir.fields)
    (siteCount : dir.processors ≤ dir.sites) (originals : dir.entries ≤ dir.teams*dir.sites)
    (capacity : ∀ c, suppliedSize N cell c+gap+dir.entries*dir.description ≤ extent)
    (before : (pub 0).val+92 < base) (reserve : base+7*dir.candidates ≤ origin)
    (room : let v := bases origin wires cells dir.entries
      Directory.ISA.wordBound (Directory.ISA.placementBound dir v.privatePairs v.livePairs extent) < 2^w)
    (emission : ∀ gm, GeometryOutput.Result (a.image f.stride m (a.words*w)) gm g work start t x →
      Image F (siteID ∘ original) (portID ∘ live) bits origin (readings gm) ∧
      Header (pub 0).val origin wires cells dir.entries (readings gm) ∧
      Directory.ISA.frameLayout (readings pub) (readings gm) = dir ∧
      frameField (readings pub) (readings gm) 8 = base ∧
      readings gm (readings gm ((pub 0).val+92)+8) = gap ∧ readings gm ((pub 0).val+92)+8 < 2^w)
    (z dim selectorBits : ℕ) (p : ScheduleClock.Placements)
    (group : ∀ gm mid v,
      GeometryOutput.Result (a.image f.stride m (a.words*w)) gm g work start t x →
      (privateLayout (pub 0).val origin wires cells dir.entries dir.description gap).Image
        (readings gm) dir.entries (readings mid) →
      let d := bases origin wires cells dir.entries
      let result := Directory.ISA.publish mid (pub 0).val base
        (dir.directory (Directory.ISA.placement (readings mid) d.privatePairs) (Directory.ISA.placement (readings mid) d.livePairs))
      ScheduleClock.AtEntries pub mac (ScheduleClock.passes pub mac z dim selectorBits result p) v result)
    (r : Returns (beforeRoute epochPlacement (scheduleGroups dim selectorBits)) pub mac s m) :
    ∃ gm mid : Memory w, GeometryOutput.Result (a.image f.stride m (a.words*w)) gm g work start t x ∧
      (privateLayout (pub 0).val origin wires cells dir.entries dir.description gap).Image
        (readings gm) dir.entries (readings mid) ∧
      let d := bases origin wires cells dir.entries
      let result := Directory.ISA.publish mid (pub 0).val base
        (dir.directory (Directory.ISA.placement (readings mid) d.privatePairs) (Directory.ISA.placement (readings mid) d.livePairs))
      let labels := LabelIndex.layout (pub 0).val (readings result)
      traceCost r.val.1 ≤ GeometryAdviceRate.ticks t.size u o b w +
        ScheduleClock.beforeDirectory dir.teams dir.sites dir.entries +
        ScheduleClock.descriptorTicks labels (readings result) z p.header.a p.groups p.teams +
        ScheduleClock.declarationTicks (p.header.decoder p.broadcast) dim selectorBits := by
  obtain ⟨v,gm,gs,rest,events,geometry,tail⟩ := Runs.seq_iff.mp ((before_iff dim selectorBits).mp r.property)
  obtain ⟨t₀,dm,ds,ss,rfl,directory,schedule⟩ := Runs.seq_iff.mp tail
  obtain ⟨_,cg,result⟩ := geometry_return_cost pub mac s m f a L P g work start src t x fit space placed input ⟨(gs,v,gm),geometry⟩
  obtain ⟨img,hdr,shape,dest,readGap,controlRoom⟩ := emission gm result
  obtain ⟨es,fs,z₀,t₁,mid,_,pref,_,run,ct,_⟩ := img.publish_directory dir N cell aux siteID edgeID portID F
    net code wordFit original live origin base gap extent pub mac v gm hdr shape dest readGap controlRoom
    before reserve bounds teams fields siteCount originals capacity room
  obtain ⟨events',bank',mem'⟩ := directory.unique_of_deterministic (by decide) run
  subst dm
  have sched := ScheduleClock.scheduleGroups_traceCost pub mac z dim selectorBits p (group gm mid t₀ result pref) schedule
  refine ⟨gm,mid,result,pref,?_⟩
  rw [events,events']
  change traceCost gs ≤ _ at cg
  have scan : traceCost (es++fs) ≤ ScheduleClock.beforeDirectory dir.teams dir.sites dir.entries := by
    simpa only [PackedHistoryCircuit.deliveryScanTicks,ScheduleClock.beforeDirectory,Nat.add_assoc] using ct
  simp only [traceCost,VPVNP.RAMBuckets.cost_append] at cg scan sched ⊢
  omega

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
