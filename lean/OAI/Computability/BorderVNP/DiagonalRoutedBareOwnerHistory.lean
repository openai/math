import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership
import OAI.Computability.BorderVNP.DiagonalRoutedIssuedInputs
import OAI.Computability.BorderVNP.DiagonalPinnedOwnerReceipt

/-! # The reconstructed exterior and owner scan on the literal issued native prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open Cube.Physical RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine Routing JointHeader
open CellMacro.Generator BorderVNP.Cube

variable {R r t d link inner n w reserve dim tally : ℕ} {ar : CubeArena.Layout}
    {Edge Hist : Type} (gen : Fragment IO) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link)
    (headerWidth : L.header=PositiveFields.width reserve ar.n ar.header.d (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally)
    (code : Hist ↪ (Fin reserve → Bool))
    (args : Fin (R+1) → UnitAddresses) (fixed : Block (R+1)) (hw : 0<w)
    (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)

local notation "Fields" => PositiveFields reserve ar.n ar.header.d (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation "mac" => TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n)
local notation "active" => PinStart.preCallSupport U id
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation "guess" => (fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl)

local notation "headers" => positiveExteriorFieldsEquiv G args pin L fixed hw size base fit headerWidth
variable {Route : Hist → Type} {Report : (Fin d → Bool) → (q : Hist) → Route q → Type}
  (routed : ∀ (i : Fin d → Bool) (q : Hist) (claim : Fin ((R+1)*dim*tally) → Bool),
    (Σ c : RawBroadcast ar,
      ParsedPreCall G args pin L fixed hw size base fit headerWidth (fun x u => (B x u).start)
        (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i ⟨code q,c,claim⟩) ≃
        Σ v : Route q,Report i q v)
variable {gen id G pub reg pin L headerWidth code args fixed hw size base fit B}
local notation3 (prettyPrint := false) "FieldsAt" => PreparedFields (Fin d → Bool) Hist
  (Fin ((R+1)*dim*tally) → Bool) Route Report

/-- The pinned preparation and issued bare tuple carry the identical exterior and full
joint native owner history. This also applies to empty teams. -/
theorem routedBareTuple_owner_observation (f : FieldsAt) :
    let z := routedBareTuple routed f
    let source := (routed f.1 f.2.1 f.2.2.2.1).symm ⟨f.2.2.1,f.2.2.2.2⟩
    z.1.val=source.2.1.val ∧
      PinStart.ownedVisits (ar:=ar) (fun u => (B z.1 u).start) z.2 =
        pinnedOwnedHistory G args pin L fixed hw size base fit ar headerWidth U ib hb sb guess id f.1
          (code f.2.1) f.2.2.2.1 source := by
  constructor <;> rfl

end TeamContraction.ProcessorSlots.BootedPinStart

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena FiniteEvaluator

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} (sa : SignedTaskArena.Layout) {decl : LengthDeclaration sa.cube.n sa.cube.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w}
    {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks →
      Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1)}
    (F : PreparationFrame G L sa.cube decl header pin pub mac reg mem)

variable {sa F}
theorem PreparationFrame.ReturnedOwnershipAt.onOriginal {origin : HeaderExterior L header}
    {x y : Exterior R r link → Bool} {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners}
    {before after : TeamRows.Returns (Fin (R+1)) sa.cube w}
    (real : F.ReturnedOwnershipAt sa origin x template count v before) (same : y=x ∧ after=before) :
    F.ReturnedOwnershipAt sa origin y template count v after := by
  obtain ⟨rfl,rfl⟩ := same
  exact real

end TeamContraction

end BorderVNP
end Computability
end OAI
