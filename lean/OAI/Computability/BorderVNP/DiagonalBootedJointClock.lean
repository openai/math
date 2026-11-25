import OAI.Computability.BorderVNP.DiagonalJointRouteCore
import OAI.Computability.BorderVNP.DiagonalJointSparseWindow
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart

/-! # Measuring the profile and route of one actual supported signed prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM TeamScales Transmission TeamContraction ProcessorSlots Filter Finset

/-- The route estimate at one length, uniform over all choices of the actual
row range, width, packet, mutable memory and team at that length. -/
def CoreAt (α ξ : ℝ) (n : ℕ) : Prop :=
  ∀ {w : ℕ} (base count : ℕ) (f : BroadcastFrame) (l : TableLayout) (row : ℕ → TableRow)
      (orig : ℕ → ℕ) (m : Memory w) (self : Word w) (u : Fin l.teams),
      l.Image row orig (readings m) → l.Allocated w → l.recordsMatch row orig →
      (∀ i < l.count, (row i).first<l.teams ∧ (row i).second<l.teams) →
      self.val=u.val → f.Fits w base → (f).teams=l.teams → f.link=TeamScales.link ξ (f).teams n →
      (f).literal ≤ literal α n → w≤count → count≤(f).processors →
      (∀ v : Fin l.teams, (∑ i ∈ range l.count, endpointWidth (row i) v.val) ≤
        3*(f).processors*literal α n+exterior ξ (f).processors n/256) →
      coreTicks count f l row (tableRange l m) self ≤ 2048*(exterior ξ (f).processors n+(l.teams+1)^3+l.count+(f).processors+1)

/-- The cutoff for the route estimate is chosen before all physical inputs. -/
theorem eventually_core_at {α ξ : ℝ} (gap : ξ < α/3) : ∀ᶠ n in atTop, CoreAt α ξ n :=
  eventually_core_of_scheduled_endpoints gap

end RoutingISA.Evaluator.ScheduleClock

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube Cube.Physical
open private groups_deterministic from OAI.Computability.BorderVNP.RoutingISASignedPrepPublic

/-- The actual eleven-stage writer and its measured charge pay for every group
schedule from these same published words. -/
theorem ReturnedWriters.publicSchedule {n R w : ℕ} {ar : CubeArena.Layout} {dir : Packing.Directory.Layout}
    {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration ar.n ar.header.d}
    {group : Fin ar.header.d → Fin (R+1)} {pins : Pins.Layout}
    {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s t : Bank w} {m mt : Memory w}
    {es : List (TeamRAM.Event w)}
    {W : WriterHistory ar.n (Tally.selectorWidth ar.n ar.K ar.h) pub mac s m es t mt}
    (returned : ReturnedWriters ar dir pp lp owner decl group pins W) (cost : traceCost es≤n) :
    PublicSchedule ar dir pp lp owner decl group pins pub mac s m n True := by
  refine ⟨fun _ => ⟨es,t,mt,W,returned,cost⟩,?_⟩
  intro tr z memory run
  obtain ⟨rfl,rfl,rfl⟩ := run.unique_of_deterministic (groups_deterministic ..) W.runs
  exact ⟨True.intro,W,returned⟩

end RoutingISA.Evaluator

namespace TeamContraction

open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock RoutingISA.Transmission
open Routing TeamScales Finset ProcessorSlots

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {tab : TableLayout} {row : ℕ → TableRow} {pub : Fin (R+1) → Arg → Word w} {before : Fin (R+1) → Memory w}
    {dst ib hb sb : Fin (R+1) → ℕ} {guess : Fin (R+1) → ℕ → Bool}

/-- Apply the uniform length estimate to the very team, row memory and physical
wire layout that actually returned on this instance. -/
theorem SharedRoutePrepared.core_at {α ξ : ℝ} {length : ℕ} (bound : CoreAt α ξ length)
    (ready : SharedRoutePrepared G pin ext L D pp lp owner origin stride tab row pub before dst ib hb sb guess)
    (u : Fin (R+1)) (count : ℕ) (mt : Memory w) (image : tab.Image row (readings (before u)) (readings mt))
    (linkEq : link=TeamScales.link ξ (R+1) length) (lit : G.program.length+t ≤ literal α length)
    (wc : w≤count) (cr : count≤r) (load : ∀ v : Fin (R+1), (∑ i ∈ range tab.count, endpointWidth (row i) v.val) ≤
      3*r*literal α length+exterior ξ r length/256) :
    coreTicks count (G.transferFrame u L.header (dst u)) tab row (tableRange tab mt) (directoryFrame (pub u) mt 0) ≤
      2048*(exterior ξ r length+(R+1+1)^3+tab.count+r+1) := by
  let frame := G.transferFrame u L.header (dst u)
  let team : Fin tab.teams := Fin.cast ready.teams u
  have state := image.broadcast_of_ordered ready.ordered (ready.base u) (ready.frame u)
  have teamNum : (directoryFrame (pub u) mt 0).val=team.val := by
    simpa [directoryFrame,frameField,team,readings,Wiring.transferFrame] using state.1
  have bounds := bound (pub u 0).val count frame tab row (readings (before u)) mt (directoryFrame (pub u) mt 0) team
    image ready.allocated (ready.records u) (fun i hi => (ready.rowFit.labels i hi).2) teamNum
    (ready.fit u) ready.teams linkEq lit wc cr (fun v => load (Fin.cast ready.teams.symm v))
  simpa only [frame,Wiring.transferFrame,←ready.teams] using bounds


end TeamContraction

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock RoutingISA.Transmission
open Routing PackedHistoryCircuit TeamScales Packing _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical Finset
open RoutingISA.CompactMachine CellMacro.Generator
open scoped BigOperators Classical
set_option maxRecDepth 5500
set_option maxHeartbeats 1100000

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {args : Fin (R+1) → UnitAddresses} {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w}
    {ar : CubeArena.Layout} (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (B : ∀ u, BootedPinStart SparseExterior.driver G pub reg args pin ext u)
    (a : PinStart.JointPrefix id (fun u => (B u).start))
    (u : Fin (R+1))
local notation3 (prettyPrint := false) "vst(" i ")" => PinStart.visits id (fun k => (B k).start) (a i)
local notation3 (prettyPrint := false) "pins" => (B u).pins
local notation3 (prettyPrint := false) "mac" => install SparseExterior.driver n (B u).start.routines
local notation3 (prettyPrint := false) "f" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "F" => G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase

/-- Charge the actual chosen prefix, including its original pin substitution,
published demand array and group schedule, and the working route table produced
on this very exterior. Every private report later rejected by a tally check is
still covered by the same two length-only windows. -/
theorem early_on_joint_prefix {α ξ : ℝ} (bound : CoreAt α ξ n)
    {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {tab : TableLayout} {row : ℕ → TableRow} {guess : Fin (R+1) → ℕ → Bool}
    (ready : SharedRoutePrepared G pin ext wire dir pp lp owner origin stride tab row pub
      (fun v => (vst(v)).profile.val.2.2) (fun v => (args v).dst) (fun v => (args v).ibase)
      (fun v => (args v).hbase) (fun v => (args v).starbase) guess)
    (profile : (Fin (B u).start.guessWidth → Bool) ≃ Returns (withStartup pinGeometry)
      (pub u) mac (reg u) (processorMemory F w))
    (spelling : ∀ b, (profile b).val.1.flatMap TeamRAM.Event.choices=List.ofFn b)
    (geometry count sites : ℕ)
    (paid : traceCost (profile (a u).1).val.1 ≤ jointBudget count w+(f).readTicks+2+
      (pinSetup.slots+17*((f).processors*(f).literal)+1)+geometry)
    (directory : Returns (.seq PrivatePlacement.program Directory.ISA.program) (pub u) mac
      (profile (a u).1).val.2.1 (profile (a u).1).val.2.2)
    (scan : traceCost directory.val.1 ≤ deliveryScanTicks dir.entries (R+1) sites)
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)} {pass : Prop}
    (scheduled : ℕ) (layout : Pins.Layout)
    (clocked : PublicSchedule ar dir pp lp owner decl group layout (pub u) mac directory.val.2.1 directory.val.2.2
      scheduled pass)
    (header : (args u).header=wire.header) (teamNum : (f).teams=tab.teams)
    (linkEq : link=TeamScales.link ξ (R+1) n) (lit : G.program.length+t ≤ literal α n)
    (wc : w≤count) (countFit : count≤r)
    (load : ∀ v : Fin (R+1), (∑ i ∈ range tab.count, endpointWidth (row i) v.val) ≤
      3*r*literal α n+exterior ξ r n/256)
    (budget : PhaseCharges)
    (coreRoom : 2048*(exterior ξ r n+(R+1+1)^3+tab.count+r+1) ≤ budget.core)
    (beforeRoom : geometry+beforeDirectory (R+1) sites dir.entries+
      scheduled ≤ budget.before) :
    (B u).used+traceCost (pins (a u).1).val.1+traceCost (vst(u)).profile.val.1+traceCost (vst(u)).routing.val.1 ≤
      budget.core+budget.before := by
  have boot := (B u).boot
  rw [siteLibrary_installed SparseExterior.driver n] at boot
  have front := profile_route_visit_charge f boot (B u).stable (B u).positive pins (fun b => ((B u).outputs b).1)
    profile spelling (a u).1 geometry count (R+1) sites ar dir layout _ paid directory scan clocked
    (vst(u)).profile (vst(u)).routing tab row ready.allocated ready.ordered ready.rowFit (ready.base u) (ready.fields u)
    (ready.records u) (header ▸ ready.frame u) (header ▸ ready.fit u) teamNum
    (fun i j => header ▸ ready.capacity u i j) (ready.written u).route
  obtain ⟨mt,image,time⟩ := front
  have core := ready.core_at bound u count mt image linkEq lit wc countFit load
  rw [header] at time
  exact time.trans (Nat.add_le_add (core.trans coreRoom) beforeRoom)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
