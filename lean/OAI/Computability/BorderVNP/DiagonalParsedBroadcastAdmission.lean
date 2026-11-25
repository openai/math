import OAI.Computability.BorderVNP.DiagonalJointPrefixAdmission
import OAI.Computability.BorderVNP.DiagonalSupportedParsedFields

/-! # The checked broadcast recovered from a parsed physical preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine SignedPrep Routing
open RoutingISA.LocalRow Transmission ProcessorSlots JointHeader PackedHistoryCircuit Packing Crossing
open BorderVNP.Cube Physical MeanChoice LabelIndex CellMacro.Generator

variable {R r t d link inner n w reserve dim tally : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (ar : CubeArena.Layout) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (args : Fin (R+1) → UnitAddresses) (live : Fin d → Bool) (L : WireLayout (R+1) r link)
    (fixed : Block (R+1)) (hw : 0<w) (size : ∀ j, (args j).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ j, (G.transferFrame j (args j).header (args j).dst).Fits w (base j))
    (width : L.header=PositiveFields.width reserve ar.n ar.header.d ar.header.cap (R+1) dim tally)
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w}
    (B : (z : {ext // PositiveExterior G args live w ext}) → (u : Fin (R+1)) →
      BootedPinStart SparseExterior.driver G pub reg args live z.val u)
    (i : Fin d → Bool) (p : PositiveFields reserve ar.n ar.header.d ar.header.cap (R+1) dim tally)

set_option quotPrecheck false
local notation3 (prettyPrint := false) "starts" => fun z u => (B z u).start
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation3 (prettyPrint := false) "parsed" => ParsedPreCall G args live L fixed hw size base fit width starts ib hb sb
  (fun _ _ => rfl) id i p
local notation3 (prettyPrint := false) "sub(" u ")" => ((G.jointGuess ib hb sb).symm i u)
local notation3 (prettyPrint := false) "key(" witness ")" =>
  (positiveExteriorFieldsEquiv G args live L fixed hw size base fit width).symm ⟨p,(witness).1⟩

/-- Recover the original joint tuple and its exact substituted raw pin before
using the directory row image to read the gates of the broadcast validator. -/
noncomputable def restoredParsedBootPrefix (z : parsed) :
    PinStart.JointPrefix id (fun u => (B (key(z)) u).start) :=
  fun u => ⟨sub(u),z.2 u⟩

/-- Apply the deployed frozen tuple checker at precisely the exterior of the
parsed input. The retained public bits and the original private pins select
the same physical tuple on every processor. -/
theorem checkedParsedBootPrefix (allowed : Broadcast ar.n ar.header.d ar.header.cap → Prop)
    (deployed : ∀ ex : {ext // PositiveExterior G args live w ext},
      (∀ b, JointHeader.observed L ex.val b=p.bits) → PinStart.JointPrefix id (fun u => (B ex u).start) →
        declarationInRange p.cube ∧ allowed p.cube) (z : parsed) :
    declarationInRange p.cube ∧ allowed p.cube :=
  deployed (key(z)) z.1.property (restoredParsedBootPrefix G ar id args live L fixed hw size base fit width B i p z)

/-- A checked prefix reaches the lead processor's actual publication on the
same exterior and precisely the lead component of its substituted pin. -/
theorem checkedParsedLead (allowed : Broadcast ar.n ar.header.d ar.header.cap → Prop)
    (scanned : ∀ e : HeaderExterior L p.bits,
      let ex := (positiveExteriorFieldsEquiv G args live L fixed hw size base fit width).symm ⟨p,e⟩
      ∀ code : (B ex 0).start.Prefix id, code.1=sub(0) →
        declarationInRange p.cube ∧ allowed p.cube) (z : parsed) :
    declarationInRange p.cube ∧ allowed p.cube :=
  scanned z.1 ⟨sub(0),z.2 0⟩ rfl

variable {dir : Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pins : Pins.Layout} {middle : Memory w} {rawBase : ℕ}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {number : I ↪ ℕ} {sizes : I → ℕ}
local notation "rr" => dir.directory pp lp
local notation3 (prettyPrint := false) "mac(" z "," u ")" => install SparseExterior.driver n (B (key(z)) u).start.routines
local notation3 (prettyPrint := false) "fields(" z "," u ")" =>
  G.processorFields u live (key(z)).val (args u).ibase (args u).hbase (args u).starbase
local notation3 (prettyPrint := false) "Full(" z "," u ")" => Returns (withStartup pinGeometry) (pub u)
  (mac(z,u)) (reg u) (processorMemory (fields(z,u)) w)

set_option maxHeartbeats 1500000 in
/-- The actual parsed preparation supplies the scan other than the public
geometry and the emitted demand-row directory. The latter are available
before any range or capacity comparison, even on malformed broadcasts. -/
theorem parsedBroadcast_admission (z : parsed) (u : Fin (R+1))
    (writer : SlottedWriter ar dir pp lp pins (pub u) middle rawBase host number sizes)
    (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ)
    (profile : List Bool) (claims : List (List Bool)) (pad X : ℕ)
    (room : PinnedRawInput (ar:=ar) (D:=dir) (pp:=pp) (lp:=lp) (pub:=pub u) (slotted:=middle) (base:=rawBase)
      (G.transferFrame u (args u).header (args u).dst) old fresh gates outputs bitWidth off ell controls profile claims pad p.cube R X)
    (paths : (Fin (B (key(z)) u).start.guessWidth → Bool) ≃ Full(z,u))
    (spelling : ∀ rawPin, (paths rawPin).val.1.flatMap TeamRAM.Event.choices=List.ofFn rawPin)
    (ret : Full(z,u)) (digits : ret.val.1.flatMap TeamRAM.Event.choices=List.ofFn (sub(u)))
    (scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) (pub u) (mac(z,u)) ret.val.2.1 ret.val.2.2)
    (stored : scan.val.2.2=Directory.ISA.publish middle (pub u 0).val rawBase rr)
    {axes : ℕ} {Port : Type*} {bits : Port → ℕ} (N : Network axes Port bits) (cell : N.Site → Fin ar.cells)
    (recv : Fin (rr).length → Fin ar.cells)
    (placed : PublishedRowPlacement N cell recv (fun j : Fin (rr).length => rr[j.val].width) (pub u 0).val scan.val.2.2)
    (hd : 0<ar.header.d) :
    declarationInRange p.cube ∧ broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h
      (meanPackedLabel N cell recv (fun j : Fin (rr).length => rr[j.val].width) (List.finRange ar.cells) ar.n ar.header.d hd)
      recv (fun j : Fin (rr).length => rr[j.val].width) p.cube := by
  let tuple := restoredParsedBootPrefix G ar id args live L fixed hw size base fit width B i p z
  have tested := BootedPinStart.joint_published_admission id (B (key(z))) tuple u writer old fresh gates outputs
    bitWidth off ell controls profile claims pad p.cube X room paths spelling ret digits scan stored N cell recv placed hd
  exact ⟨tested.2.1,tested.2.2.1⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
