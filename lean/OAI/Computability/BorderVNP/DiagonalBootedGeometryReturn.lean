import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.DiagonalNativeProfilePrefix

/-! # Readback on each returning geometry prefix of the physical pin start -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Pins
open RoutingISA.CompactMachine PackedHistoryCircuit DiagonalResidueRAM CellMacro.Generator BorderVNP.Cube.Tally

variable {R r t d link inner n w : ℕ} {Edge : Type} {gen : Fragment IO}
    {G : Wiring R r t d link inner n Edge} {pub : Fin (R+1) → Arg → Word w}
    {regs : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {live : Fin d → Bool} {wire : Exterior R r link → Bool} {u : Fin (R+1)}
    (B : BootedPinStart gen G pub regs args live wire u)
local notation3 (prettyPrint := false) "mac" => TeamSiteEvents.macros (w := w) (siteLibrary gen) (nativeClock n)
local notation3 (prettyPrint := false) "installed" => install gen n mac
local notation3 (prettyPrint := false) "L" => G.pinLayout u (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "f" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "F" => G.processorFields u live wire (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "initial" => processorMemory F w

/-- The true full returning startup obtained from this specific reconstructed
geometry. Every fact about the memory of all complete profile returns can be
used at this local prefix, including publication of a typed frozen packet. -/
theorem BootedPinStart.fullGeometryReturn (g : Fin (L).guessWidth → Bool)
    (geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2) :
    ∃ run : Returns (withStartup pinGeometry) (pub u) installed (regs u) initial, run.val.2 = geo.val.2 := by
  have boot : Runs (pub u) installed JointHeader.bootHeader (regs u) initial B.trace B.out B.memory := by
    rw [←siteLibrary_installed gen n]
    exact B.boot
  obtain ⟨_,_,pre,head,_,start,copy⟩ := Runs.seq_iff.mp boot
  let es := dispatchPrefix f B.memory pre head ++ ((B.pins g).val.1 ++ geo.val.1)
  exact ⟨⟨(es,geo.val.2),(evaluation_startup_iff f pinGeometry start copy B.stable B.positive).mpr
    ⟨_,rfl,(B.pins g).property.seq geo.property⟩⟩,rfl⟩

open private before_iff from OAI.Computability.BorderVNP.DiagonalNativePublishedWindow

/-- Every successful pre-call visit contains this local reconstruction, the
following publisher, and the ensuing group scheduler on its actual memory.
The corresponding full booted return has precisely the reconstruction result. -/
theorem BootedPinStart.preparedGeometryReturn {dim box lanes selectors symbols : ℕ}
    (id : BorderVNP.Cube.TableEntry dim box lanes selectors symbols → ℕ) (prep : B.start.Prefix id) :
    let g := prep.1
    let visit := (SignedPrep.visitsEquiv id (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2).symm prep.2
    ∃ geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2,
    ∃ run : Returns (withStartup pinGeometry) (pub u) installed (regs u) initial,
    ∃ write : Returns (.seq PrivatePlacement.program Packing.Directory.ISA.program) (pub u) installed geo.val.2.1 geo.val.2.2,
    ∃ groups : Returns (scheduleGroups dim (selectorWidth dim selectors lanes)) (pub u) installed write.val.2.1 write.val.2.2,
      run.val.2=geo.val.2 ∧ visit.profile.val.2=groups.val.2 ∧
      visit.profile.val.1=geo.val.1++(write.val.1++groups.val.1) := by
  intro g visit
  obtain ⟨bank,mem,trace,tail,events,reconstruct,rest⟩ :=
    Runs.seq_iff.mp ((before_iff dim (selectorWidth dim selectors lanes)).mp visit.profile.property)
  obtain ⟨next,published,descs,sched,rfl,write,groups⟩ := Runs.seq_iff.mp rest
  let geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2 :=
    ⟨(trace,bank,mem),reconstruct⟩
  obtain ⟨run,state⟩ := B.fullGeometryReturn g geo
  exact ⟨geo,run,⟨(descs,next,published),write⟩,⟨(sched,visit.profile.val.2),groups⟩,state,rfl,events⟩

/-- Read the actual reconstruct result using the profile run for the same pin digits.
The clock includes the selected pin prefix and the real boot, and the returned memory
is compared to the pin start's own snapshot even if the profile enumerator obtained
its boot trace independently. -/
theorem BootedPinStart.geometryReadback
    (profile : (Fin (L).guessWidth → Bool) ≃ Returns (withStartup pinGeometry) (pub u) installed (regs u) initial)
    (stream : ∀ g, (profile g).val.1.flatMap TeamRAM.Event.choices = List.ofFn g)
    {header : List Bool} {packet : ReferencePacket w d} {next : ℕ}
    (memory : ∀ g, ∃ trace z saved, Runs (pub u) installed JointHeader.bootHeader (regs u) initial trace z saved ∧
      JointHeader.BootHeaderState F f (args u).advice packet (pub u) header z saved ∧
      ∀ i < next, (profile g).val.2.2 i = Pins.preparedMemory L (extendGuess g) saved (L).count i)
    (g : Fin (L).guessWidth → Bool)
    (geo : Returns GeometryAdvice.reconstruct (pub u) installed (B.pins g).val.2.1 (B.pins g).val.2.2) :
    (profile g).val.2 = geo.val.2 ∧
    B.used + traceCost (B.pins g).val.1 + traceCost geo.val.1 = traceCost (profile g).val.1 ∧
    JointHeader.BootHeaderState F f (args u).advice packet (pub u) header B.out B.memory ∧
    ∀ i < next, geo.val.2.2 i = Pins.preparedMemory L (extendGuess g) B.memory (L).count i := by
  have boot : Runs (pub u) installed JointHeader.bootHeader (regs u) initial B.trace B.out B.memory := by
    rw [←siteLibrary_installed gen n]
    exact B.boot
  obtain ⟨eqn,_,cost⟩ := profile_at_pin_return f boot B.stable B.positive B.pins
    (fun a => (B.outputs a).1) profile stream g geo
  obtain ⟨tr,z,saved,runs,headerState,keep⟩ := memory g
  obtain ⟨_,registers,mem⟩ := boot.unique_of_deterministic (by decide) runs
  exact ⟨eqn,cost.symm,registers ▸ mem ▸ headerState,fun i hi => eqn ▸ mem ▸ keep i hi⟩

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
