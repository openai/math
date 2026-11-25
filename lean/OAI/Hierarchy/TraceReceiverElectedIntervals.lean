import OAI.Hierarchy.GridReceiverIntervalInputs
import OAI.Hierarchy.TraceReceiverEntryTables
import OAI.Hierarchy.TraceReceiverDescendantExecution
import OAI.Hierarchy.TraceReceiverSeedOffset

namespace OAI
/-! # The selected receiver's genuine S5 source offsets -/

namespace Hierarchy.TraceReceiverElectedIntervals
open ThreeFlat RAM Diagonal PhysicalStage TickWorkspace
open Computability.VPVNP.BurstRAM GridRegisteredSetting GridReceiverDirectory GridPinArena GridThrough FactorPinIntervals
open TraceReceiverSeedWords TraceReceiverLeafSetup RAM.HistoryStageBody.Physical
open scoped Fin.CommRing Classical
noncomputable section

variable {F : Type} [Field F] [Fintype F] {w pc rr pp S addr fuel axes : ℕ}
variable (D : RunData F (64*w) pc rr pp S addr fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => (64*w)
local notation "u" => TraceAdmission.receiverAge w
local notation "m" => l.dimension
local notation "n" => l.sideMinusOne
local notation "q" => l.copies
local notation "k" => m+1
local notation "T" => (n+1)^k*q
local notation "A" => GridReceiverTickDirectory.banks w u
local notation "P" => GridReceiverBanks.pinPlan D l
local notation "N" => (GridReceiverDirectory.parameters D l).roots
local notation "stages" => (GridReceiverDirectory.native D l).stages.length
local notation "full" => (2^(axes+1) : ℕ)
local notation "K" => (20*(w+1)+2)^(k+2)
local notation "J" => GridDescription.sector w
local notation "g" => GridPinArena.slab w
local notation "unit" => D.issuedUnit w l.degree l.stageRate l.rootRate
local notation "amount" => D.costs (GridNativeImage.resources D l)
local notation "countIn" => GridPinPublisher.CountInputs
local notation "tables" => TraceReceiverTablesMount.output D

variable (geom : ElectionRoom D l) (safe : GridNativeDispatch.WordRoom D) (z : D.trace)
    (sel : Fin (l.selectorCap+1)→Bool) (t : Fin ((l.sideMinusOne+1)^(l.dimension+1)*l.copies))
    (input origin elected : Memory (64*w))
    (got : Elected D l geom safe z sel t input origin elected)
    (Q : Layout (Cell (l.dimension+1) l.sideMinusOne × Fin l.copies) S (D.roots z.1) l.pinWidth)
local notation "costRows" => amount z.1 m n l.bank D.issuedCharges unit

include got in
/-- Recover the true word tables from the same run, and pass them unchanged
through the receiver's template and codebook writes before scanning them. -/
theorem offsets (large : 64^10≤w) (source : ∀ i,Q.origin i=D.origin z.1 i)
    (dispatch : ∀ f,GridTicks.index (Q.owner f)=FactorAllocation.owner geom.teams_pos w costRows f)
    (order : ∀ s,Q.rows s=FactorAllocation.factors w costRows (List.finRange _) (GridTicks.index s))
    (lens : ∀ s,(Q.header s).length=(P).headerSize)
    (R : GridPinArena.Scalars W P S full K g) (small : GridPinArena.Small w P S full (stages*full) K)
    (lib : libraryWords D.block W≤ stride u)
    (keep : TraceReceiverEntryTables.TableFrame w u (libraryWords D.block W) elected (tables elected)) :
    ∀ j : Fin S, (P).bucketed (tables elected) ((P).source.blocks+j.val/(P).source.span)+
      ((j.val%(P).source.span:ℕ):Word W)=((GridPinAddressImage.code (Q.address j)).val:Word W) := by
  rcases got with ⟨reg,hist,assigned,cl,el⟩
  have raw:=GridReceiverIntervalInputs.from_prefix D l geom large z sel safe hist t cl el Q source
  have times:=TraceAdmission.receiverAge_chart w large
  have sector:=TraceReceiverOwnerMount.sector geom.pos times.2
  have wide:=(GridPinArena.scales w geom.pos).1
  have old:stages*full≤g:=small.staged
  have Fbound:full≤g:=small.full
  have current:=GridReceiverIntervalInputs.keep_window D l geom z Q raw (fun i lo hi=>by
    apply keep i (by omega)
    right
    change 39*stride u+libraryWords D.block W ≤ i
    omega)
  have actual : P=GridPinPublisher.canonical w k n q l.pinWidth (GridNativeImage.parameterCount D l)
      (l.selectorCap+1) l.receiverText l.bank (GridControllerSimGeometry.railCount m n l.bank)
      S (D.roots z.1) stages full (2*2^(w/2)) := by rw [GridReceiverDirectory.roots D l z.1];rfl
  exact GridPinPublisher.receiver_offsets Q geom.teams_pos costRows (D.dest z.1) dispatch order
    D.bucket (TraceDistribution.native_interval_index D.machine D.fit D.field D.state)
    (fun j=>(D.owns z.1 j).trans (source j).symm) P actual lens R small (tables elected) current

/-- The S5 row the leaf interpreter actually reads after its owner pass. -/
theorem first {first roots : ℕ} (large : 64^10≤w) (room : TraceReceiverOwnerMount.Room W u first roots (A).owners ((A).scratch+1))
    (R : GridPinArena.Scalars W P S full K g) (small : GridPinArena.Small w P S full (stages*full) K)
    (offset : ∀ j : Fin S, (P).bucketed (tables elected) ((P).source.blocks+j.val/(P).source.span)+
      ((j.val%(P).source.span:ℕ):Word W)=((GridPinAddressImage.code (Q.address j)).val:Word W))
    (v : PairedCursor.Site (axes+1)) (nonempty : 0<width D.machine D.fit D.field D.state v) :
    TraceReceiverDescendantExecution.entry D first roots P elected
      (base u 5+4*(finFunctionFinEquiv v.2).val+3)=
      ((Q.slot (TraceReceiverSeedWords.source D.machine D.fit D.field D.state v ⟨0,nonempty⟩)).val:Word W) := by
  have big : 2≤w := (by decide : 2≤64^10).trans large
  have times:=TraceAdmission.receiverAge_chart w large
  have sector:=TraceReceiverOwnerMount.sector (by omega : 0<w) times.2
  have slabs:=GridPinArena.scales w (by omega : 0<w)
  have slots : 4*(P).lanes≤ stride u := TraceReceiverEntryFrame.lane_span big small.bits times.1
  have cells : (P).source.blocks+(P).lanes≤2^W :=
    (Nat.add_le_add_left (R.within.trans small.full) _).trans (R.window.fit .blocks).le
  have power : base u 5+4*(P).lanes≤2^W := by change 6*stride u+4*(P).lanes≤_;omega
  have grid : (n+1)^k*(q*l.pinWidth)≤2^W := by
    have h:=small.pinStorage
    change ((n+1)^k*q)*l.pinWidth≤g at h
    rw [←Nat.mul_assoc]
    omega
  have disjoint (b : ℕ) (hb:b<(P).lanes) (i : ℕ) (hi:i<(P).lanes) : (P).source.blocks+b≠base u 5+4*i+3 := by
    change 15*J+10*g+b≠6*stride u+4*i+3
    omega
  have slot:=TraceReceiverOriginal.interval_original D.machine D.fit D.field D.state P Q (base u 5) (tables elected)
    rfl rfl R.lanesFit cells power rfl R.pinsFit grid disjoint offset v nonempty
  let j:=TraceReceiverSeedWords.source D.machine D.fit D.field D.state v ⟨0,nonempty⟩
  have fact : j.val=(finFunctionFinEquiv v.2).val*(2*2^(w/2)) := by
    rw [show j.val=_ from source_val D.machine D.fit D.field D.state v ⟨0,nonempty⟩]
    change (finFunctionFinEquiv v.2).val*((1*2)*2^(w/2))+0=_
    simp
  have rel : j.val/(2*2^(w/2))=(finFunctionFinEquiv v.2).val := by
    rw [fact,Nat.mul_div_cancel _ (by positivity)]
  have reaches:(finFunctionFinEquiv v.2).val<(P).lanes := by
    rw [←rel]; exact GridPinPublisher.bucket_visited (by positivity) j
  exact (TraceReceiverEntryFrame.owner_slot room big times.1 small.bits
    (TraceReceiverDescendantExecution.sliced D P elected) (⟨_,reaches⟩:Fin (P).lanes)).trans slot

end
end Hierarchy.TraceReceiverElectedIntervals

end OAI
