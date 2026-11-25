import OAI.Hierarchy.DescentPackedCanvasAny
import OAI.Hierarchy.DescentPackedCanvasHardware
import OAI.Hierarchy.DescentEstimatorAny
import OAI.Hierarchy.DescentEstimatorProgramBill
import OAI.Hierarchy.DescentDatedPhysicalReset

namespace OAI
/-! # The fixed-date reset prefix through the published measured GL basis -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSIMDLookup DescentPackedWalsh DescentSixParty.PackedFlow.Canvas
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (a : PhysicalReset) (floor : ℕ)

def estimator := (a.chart floor).estimator a.payload a.gain a.positive
def flow := Setup.core a.previousToken a.previousRoster a.hosts a.ports a.high a.low a.bits a.short a.lanes
  floor a.depthCut a.fullBudget a.classBound a.grain
local notation "P" => a.chart floor
local notation "C" => flow a floor
local notation "E" => estimator a floor
local notation "N" => a.hosts*(a.high+a.low+1)+a.hosts*a.ports

def prime (src count : Bank) (R δ w : ℕ) : Procedure w :=
  let setup:=Setup.prep a.previousToken a.previousRoster a.hosts a.ports a.high a.low a.bits a.short a.lanes
    floor a.depthCut a.fullBudget a.classBound a.grain src R w
  (setup.seq ((P).prepare C count a.k δ R a.lanes w (E).start)).seq (((E).header (w:=w)).program.seq ((E).cpu w))

def primeTicks (R δ w : ℕ) :=
  Setup.ticks a.hosts a.ports a.high a.low a.bits a.short a.lanes floor a.depthCut a.fullBudget a.classBound a.k R+
    (P).prepareTicks C a.k δ R a.lanes w+(4+10*((E).staticEnd-(E).origin)+(E).clock)

structure PrimeRoom (src count : Bank) (R δ w : ℕ) : Prop where
  batch : chunks R a.lanes=2^a.high
  source : src.base+src.size≤floor
  oldTokens : ∀t,(a.previousToken t).base+(a.previousToken t).size≤floor ∧ a.hosts*chunks R a.lanes≤(a.previousToken t).size
  oldRoster : a.previousRoster.base+a.previousRoster.size≤floor
  slots : a.hosts*a.ports≤a.previousRoster.size
  countLow : count.base+count.size≤floor
  smooth : DescentBaseProfile.decayExponent δ<2^w
  dimensions : a.high+a.low<2^w
  fit : (E).Fits w
  bounded : (E).endAddress<2^w
  payload : a.payload≤w

theorem prime_any (src count : Bank) (R δ w : ℕ) (mem : Memory w) (ok : PrimeRoom a floor src count R δ w) :
    ∃prior,(prime a floor src count R δ w).Exec mem ((E).image ((E).literal prior)) (primeTicks a floor R δ w) := by
  have header:(P).endAddress≤(E).start:=((P).estimator_prefix a.payload a.gain a.positive).trans (Nat.le_add_right ..)
  have rows : N=(E).hosts:=by change _=a.hosts*((a.high+a.low)+1+a.ports);ring
  have span:(E).start+(E).hosts*2^(E).high≤(E).inputEnd:=Nat.add_le_add (E).areas.2.2.2.2.2.1 (rows_le (E).hosts (E).high)
  have limit:(E).start+N*2^a.high<2^w:=by
    rw [rows];exact (span.trans ((E).calendar.pre ((E).dim+1))).trans_lt ok.fit.bounded
  have prefixRoom:(P).endAddress<2^w:=header.trans_lt ((Nat.le_add_right ..).trans_lt limit)
  obtain ⟨mid,one⟩:=Setup.setup_any a.previousToken a.previousRoster src a.hosts a.ports R a.high a.low a.bits a.short
    a.lanes floor a.depthCut a.fullBudget a.classBound a.grain w mem ok.batch ok.source prefixRoom
  obtain ⟨prior,two⟩:=Setup.prepare_any a.previousToken a.previousRoster count a.hosts a.ports R a.high a.low a.bits a.short
    a.lanes floor a.depthCut a.fullBudget a.classBound a.grain δ w (E).start mid ok.batch ok.oldTokens ok.oldRoster
    ok.slots ok.countLow ok.smooth ok.dimensions header limit
  have headerRoom:(E).staticEnd<2^w:=(Nat.le_add_right (E).staticEnd (E).dataGap).trans_lt ((Nat.le_add_right ..).trans_lt limit)
  refine ⟨prior, Procedure.Exec.then (Procedure.Exec.then one two) ?_⟩
  exact (E).any prior ok.fit headerRoom ((E).room_of_end ok.bounded) ok.payload (Nat.succ_le_of_lt ok.dimensions)

private theorem hardware_seq {w : ℕ} (first header tail : Procedure w) (x y z : ℕ)
    (h₁ : CheapCode first ∧ names first ≤ x) (h₂ : CheapCode header ∧ names header = y)
    (h₃ : CheapCode tail ∧ names tail ≤ z) :
    CheapCode (first.seq (header.seq tail)) ∧ names (first.seq (header.seq tail)) ≤ x+(y+z) := by
  constructor
  · exact cheap_seq (A:=first) (B:=header.seq tail) h₁.1 (cheap_seq (A:=header) (B:=tail) h₂.1 h₃.1)
  · rw [names_seq first _, names_seq header tail, h₂.2]
    exact Nat.add_le_add h₁.2 (Nat.add_le_add_left h₃.2 _)

theorem prime_hardware (src count : Bank) (R δ w : ℕ) :
    CheapCode (prime a floor src count R δ w) ∧
      names (prime a floor src count R δ w)≤Setup.allText a.hosts a.ports a.high a.low a.bits a.short a.lanes a.k a.c+
        (15*((E).staticEnd-(E).origin+1)+(E).controlNames) := by
  have front:=Setup.full_hardware a.previousToken a.previousRoster src count a.hosts a.ports R a.high a.low a.bits a.short
    a.lanes floor a.depthCut a.fullBudget a.classBound a.grain δ w (E).start
  have hdr:=((E).header (w:=w)).hardware
  have cpu:=(E).cpu_names w
  let setup := Setup.prep a.previousToken a.previousRoster a.hosts a.ports a.high a.low a.bits a.short a.lanes
    floor a.depthCut a.fullBudget a.classBound a.grain src R w
  let first := setup.seq ((P).prepare C count a.k δ R a.lanes w (E).start)
  let header := ((E).header (w:=w)).program
  let program := (E).cpu w
  exact hardware_seq first header program _ _ _ front hdr cpu

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
