import OAI.Computability.BorderVNP.DiagonalNativePublishedBroadcastChecks
import OAI.Computability.BorderVNP.DiagonalReturnedWriterScan

/-! # Range and capacity checks on the signed directory scan of a returning pin -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP BurstRAM RoutingISA RoutingISA.CompactMachine RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open RoutingISA.LocalRow PackedHistoryCircuit Packing Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.LabelIndex

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {pub : Fin (R+1) → Arg → Word w}
    {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses} {ar : CubeArena.Layout}
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    {u : Fin (R+1)} (B : BootedPinStart SparseExterior.driver G pub reg args pin ext u)
local notation3 (prettyPrint := false) "lib" => install SparseExterior.driver n
  (TeamSiteEvents.macros (w:=w) (siteLibrary SparseExterior.driver) (nativeClock n))
local notation3 (prettyPrint := false) "entry" => G.transferFrame u (args u).header (args u).dst
local notation3 (prettyPrint := false) "fields₀" => G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "Full" => Returns (withStartup pinGeometry) (pub u) lib (reg u)
  (processorMemory fields₀ w)

variable {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins}
    {guess : ℕ → Bool} {pinRegs : Bank w} {pinMem : Memory w} {used frame base : ℕ}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {key : I ↪ ℕ} {widths : I → ℕ}
    {old : Fin 81 → Word w} {fresh gates outputs bitWidth off ell controls : ℕ}
    {word : List Bool} {claims : List (List Bool)} {pad : ℕ} {raw : Broadcast ar.n ar.header.d ar.header.cap} {X : ℕ}
    {dim : ℕ} {Names : Type*} {bits : Names → ℕ} {N : Network dim Names bits} {tile : N.Site → Fin ar.cells}
    {recv : Fin (dir.directory pp lp).length → Fin ar.cells} {label : Fin ar.cells → Label (ar.n+1) ar.header.d}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)} {owner : ℕ → Fin (R+1)}

local notation3 (prettyPrint := false) "rows" => dir.directory pp lp
local notation3 (prettyPrint := false) "sizes" => fun i : Fin (dir.directory pp lp).length => (dir.directory pp lp)[i.val].width

/-- The two native checks on the same scan that published the route rows and selected the writer. -/
theorem published_returned_scan_checks (g : Fin B.start.guessWidth → Bool)
    (profile : (Fin B.start.guessWidth → Bool) ≃ Full)
    (spelling : ∀ v, (profile v).val.1.flatMap TeamRAM.Event.choices=List.ofFn v) {ret : Full}
    (source : Diagonal.ReturnedWriterScan ar dir rows pp lp fields entry guess (pub u) lib (profile g) ret
      pinRegs pinMem used frame base host key widths old fresh gates outputs bitWidth off ell controls word claims pad raw
      X N tile recv sizes label decl group owner) (hd : 0<ar.header.d)
    (code : B.start.Prefix id) (chosen : code.1=g) :
    declarationInRange raw ∧ broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h
      (meanPackedLabel N tile recv sizes (List.finRange ar.cells) ar.n ar.header.d hd) recv sizes raw := by
  obtain ⟨_,epoch,published,mid,scan,_,stored,_,_,same,_,_,_,_,writer,pinned,placed,_⟩ := source
  exact published_native_broadcast_checks id B writer.some old fresh gates outputs bitWidth off ell controls word claims pad
    raw X pinned g profile spelling scan ((congrArg Prod.snd same).trans stored) N tile recv placed hd code chosen

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
