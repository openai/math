import OAI.Computability.BorderVNP.DiagonalBootedOriginalOwnedBanks
import OAI.Computability.BorderVNP.DiagonalBootedGeometryProfile

/-! # The original readback on the frozen publication's actual boot residence -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows
open Scatter.Assignment DiagonalTallyPacketEmit FiniteEvaluator ProcessorSlots

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
    {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
    {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)} (sa : SignedTaskArena.Layout)
    {decl : LengthDeclaration sa.cube.n sa.cube.header.d} {group : Fin sa.cube.header.d → Fin (R+1)}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) →
      Fin sa.cube.header.d → Fin (R+1)} {template : Frame} {rows : ℕ}

open CellMacro.Generator RoutingISA.CompactMachine RoutingISA.Evaluator RoutingISA.Pins JointHeader SignedTaskArena
open PackedHistoryCircuit

variable {pub : Fin (R+1) → Arg → Word w}
  {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
  (B : (u : Fin (R+1)) → BootedPinStart SparseExterior.driver G pub reg args pin ext u)
  (active : (u : Fin (R+1)) → (B u).start.Prefix sa.id) (u : Fin (R+1))
local notation3 (prettyPrint := false) "history" => PinStart.ownedVisits (ar:=sa.cube) (fun t => (B t).start) active
local notation3 (prettyPrint := false) "V" => PinStart.visits sa.id (fun t => (B t).start) (active u)
local notation3 (prettyPrint := false) "afterPin" => ((B u).pins (active u).1).val.2
set_option maxRecDepth 7500
set_option maxHeartbeats 2200000

/-- The residence of the public profile already fixes every previous low word.
This permits the genuine geometry publisher's output to feed the owned
readback directly, without constructing its gate trace a second time. -/
theorem SharedWriters.banks_on_original_low
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) sa.cube.header.blocks sa.cube.K sa.cube.h decl group)
    (handoff : OwnedHandoff f g src sa.cube decl group template sa.id rows history)
    {q : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners}
    (observed : ObservedOwned sa.cube decl group history owners (f.receivedRows g group) q)
    (A : StartupArena) {entries indices res side blocks hdrCap digits : ℕ}
    (p : PositiveFields res side blocks hdrCap sa.cube.teams sa.dim digits)
    (copies : entries*w≤A.copied) (index : indices≤A.count)
    (posI : (args u).ibase=A.ibase) (posH : (args u).hbase=A.hbase) (frame : (pub u 0).val=A.frame)
    (size : A.header=PositiveFields.width res side blocks hdrCap sa.cube.teams sa.dim digits)
    (seed : HeaderSeed sa p (pub u) (rawAddress A res side blocks hdrCap) u.val (B u).memory)
    {dest : ℕ} {geo : Memory w} (low : ∀ j<A.next, geo j=afterPin.2 j) (outputAbove : A.next ≤ dest)
    {edges cells desc gap : ℕ} (directory : List Packing.Directory.Row) (placed : Memory w)
    (placement : (Packing.RoutingOutputs.privateLayout A.frame dest edges cells D.entries desc gap).Image
      (readings geo) D.entries (readings placed))
    {s z : Bank w} {after : Memory w} {es}
    (W : WriterHistory sa.cube.n (Tally.selectorWidth sa.cube.n sa.cube.K sa.cube.h) (pub u)
      (install SparseExterior.driver n (B u).start.routines) s (Packing.Directory.ISA.publish placed A.frame A.next directory) es z after)
    (accepted : ReturnedWriters sa.cube D pp lp owner decl group (pins u) W)
    (atSource : src u=readings W.sharedInput) (secondary : A.next≤ sa.cube.header.header) :
    ReaderKept A entries indices (B u).memory afterPin.2 (V).owned.val.2.2 ∧
      HeaderSeed sa p (pub u) (rawAddress A res side blocks hdrCap) u.val (V).owned.val.2.2 := by
  have unchanged (j : ℕ) (early : j<A.next) : geo j=preparedMemory
      (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase) (extendGuess (active u).1) (B u).memory
      (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).count j := by
    rw [low j early,((B u).outputs (active u).1).2.2.2.2]
    rfl
  exact writer.boot_to_owned sa args reg u (B u) A p (active u).1 copies index posI posH frame size seed
    geo (B u).memory (B u).out (B u).trace (B u).boot unchanged directory placed placement outputAbove
    W accepted secondary atSource symbols handoff observed

/-- Align an independently obtained boot residence with the actual chosen
pin's installed memory. Both boots run deterministically from the same
original processor input; the two layouts name the same prepared arrays. -/
theorem BootedPinStart.protected_low_after_residence
    (A : StartupArena) (index : Fin A.teams) (slot : ℕ) (reference : ReferencePacket w d)
    (copy : BroadcastFrame) (advice : AdviceLayout)
    (fields : Pins.ProcessorFields (A.operands index slot reference).layout) (header : List Bool)
    (sameLayout : (A.operands index slot reference).layout=
      G.pinLayout u (args u).ibase (args u).hbase (args u).starbase)
    {geo : Memory w} (p : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
    (resident : BootResidence (F:=fields) A index slot reference copy advice (pub u)
      (install SparseExterior.driver n (B u).start.routines)
      header (processorMemory (G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase) w)
      (reg u) p geo) :
    ∀ j<A.next, geo j=((B u).pins p).val.2.2 j := by
  obtain ⟨es,z,saved,run,_,words⟩ := resident
  have actual := (B u).boot
  rw [siteLibrary_installed SparseExterior.driver n] at actual
  have same := (run.unique_of_deterministic (by decide) actual).2.2
  intro j early
  rw [words j early,same,sameLayout,((B u).outputs p).2.2.2.2]

end TeamContraction

end BorderVNP
end Computability
end OAI
