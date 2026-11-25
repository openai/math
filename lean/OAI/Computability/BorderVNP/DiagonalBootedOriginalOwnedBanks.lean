import OAI.Computability.BorderVNP.DiagonalNativeReaderOwned
import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved
import OAI.Computability.BorderVNP.DiagonalJointSparseWindow

/-! # Depositing the deployed boot fields on a joint prefix's actual owned banks -/

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

/-- The complete boot, arbitrary local pin, public geometry and absolute
seven-word directory describe this very team's reached owned stage.
The two conclusions use the identical joint prefix consumed by the
physical post-call certificate, before any private report is checked. -/
theorem SharedWriters.banks_on_original_owned
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
    {o fresh dest clock : ℕ} {out : Fin o → ℕ} {trace : List (TeamRAM.Event w)} {endReg : Bank w} {geo : Memory w}
    (geometry : GeometryReturn (pub u) (install SparseExterior.driver n (B u).start.routines) afterPin.1 afterPin.2
      fresh dest clock out trace endReg geo)
    (geometryAbove : A.next ≤ fresh) (outputAbove : A.next ≤ dest)
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
    rw [geometry.preserved j (early.trans_le geometryAbove),((B u).outputs (active u).1).2.2.2.2]
    rfl
  exact writer.boot_to_owned sa args reg u (B u) A p (active u).1 copies index posI posH frame size seed
    geo (B u).memory (B u).out (B u).trace (B u).boot unchanged directory placed placement outputAbove
    W accepted secondary atSource symbols handoff observed

/-- Source and output of the original returning writer at a chosen team's
local prefix. The names of the physical directory and all addressed private
and public writes stay visible when this proposition is specialized to a
deployed tape. -/
abbrev BootedPinStart.ReturnedWriterReadback (A : StartupArena)
    {res side blocks hdrCap digits : ℕ} (fields : PositiveFields res side blocks hdrCap sa.cube.teams sa.dim digits)
    (D₀ : Packing.Directory.Layout) (fresh dest edges cells outputs entryWords indices : ℕ) : Prop :=
  ∀ {wire : WireLayout (R+1) r link} {pp₀ lp₀ : ℕ → ℕ × ℕ} {holder : ℕ → Fin (R+1)}
    {callBase spacing : ℕ} {hist : Fin (R+1) → TeamHistory w} {locations : Fin (R+1) → Pins.Layout}
    {del : ReturnedDelivery G pin ext wire D₀ pp₀ lp₀ holder callBase spacing hist locations}
    {shared : SharedRows.Layout} {prior : Fin (R+1) → ℕ → ℕ} {lead : Fin (R+1)}
    {lengths : LengthDeclaration sa.cube.n sa.cube.header.d} {groups : Fin sa.cube.header.d → Fin (R+1)}
    {who : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) →
      Fin sa.cube.header.d → Fin (R+1)}
    {proto : Frame} {nRows : ℕ} {original : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) who},
    SharedWriters del shared prior →
    SymbolFrame shared (prior lead) sa.cube.header.blocks sa.cube.K sa.cube.h lengths groups →
    OwnedHandoff del shared prior sa.cube lengths groups proto sa.id nRows history →
    ObservedOwned sa.cube lengths groups history who (del.receivedRows shared groups) original →
    ∀ {clock : ℕ} {values : Fin outputs → ℕ} {trace : List (TeamRAM.Event w)} {endReg : Bank w} {geo : Memory w},
    GeometryReturn (pub u) (install SparseExterior.driver n (B u).start.routines) afterPin.1 afterPin.2
      fresh dest clock values trace endReg geo →
    ∀ {gap : ℕ} {placed : Memory w},
    (Packing.RoutingOutputs.privateLayout A.frame dest edges cells D₀.entries D₀.description gap).Image
      (readings geo) D₀.entries (readings placed) →
    ∀ {s z : Bank w} {after : Memory w} {es : List (TeamRAM.Event w)}
      (W₁ : WriterHistory sa.cube.n (Tally.selectorWidth sa.cube.n sa.cube.K sa.cube.h) (pub u)
        (install SparseExterior.driver n (B u).start.routines) s
        (Packing.Directory.ISA.publish placed A.frame A.next (D₀.directory pp₀ lp₀)) es z after),
    ReturnedWriters sa.cube D₀ pp₀ lp₀ holder lengths groups (locations u) W₁ →
    prior u=readings W₁.sharedInput →
    ReaderKept A entryWords indices (B u).memory afterPin.2 (V).owned.val.2.2 ∧
      HeaderSeed sa fields (pub u) (rawAddress A res side blocks hdrCap) u.val (V).owned.val.2.2

end TeamContraction

end BorderVNP
end Computability
end OAI
