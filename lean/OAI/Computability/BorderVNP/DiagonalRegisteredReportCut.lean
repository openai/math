import OAI.Computability.BorderVNP.DiagonalAdmittedReportCut
import OAI.Computability.BorderVNP.DiagonalRoutedReportCutDecoder

/-! # Report inputs on the registered family of physical decoder routes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine SignedPrep Routing JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter DiagonalTallyCellReports

set_option autoImplicit false
set_option maxRecDepth 8500


/-- The fitted report scanner and sparse argument program belonging to one
team of a jointly supported physical prefix. -/
def jointReportCutAt {R n w axes boxes lanes copies symbols : ℕ} {X : Type} {gen : Fragment IO}
    {id : TableEntry axes boxes lanes copies symbols → ℕ}
    (T : X → Fin (R+1) → PositiveTeam id gen n w) (z : JointBeforeCells T) (u : Fin (R+1))
    {l : ReportLayout} {cs : List (ReportCell l)} (rows : ReportAssignments cs) : Prop :=
  ∃ cur desc, Nonempty (ReportArgumentCut ((T z.1 u).start.visited (z.2 u)).reports rows cur desc)

variable {R r t d link inner n w reserve dim width : ℕ} {Edge Hist : Type} (gen : Fragment IO)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link) (args : Fin (R+1) → UnitAddresses)
    (fixed : Block (R+1)) (positive : 0<w) (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (ar : CubeArena.Layout) (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (hdr : L.header=PositiveFields.width reserve ar.n ar.header.d
      (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim width)
    (code : Hist ↪ (Fin reserve → Bool))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)
    (owners : Hist → (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (source : (h : Hist) → SourceReports ar (owners h))

local notation "I" => Fin d → Bool
local notation "Claim" => Fin ((R+1)*dim*width) → Bool
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation3 (prettyPrint := false) "digits" => fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl
local notation3 (prettyPrint := false) "routes" => fun h : Hist =>
  {v : Routed (b:=ar.b) (s:=ar.s) (owners h) // (source h).pins v}
local notation3 (prettyPrint := false) "proposals" => fun (_ : I) (h : Hist) (v : routes h) =>
  (source h).actual v.val

variable (allowed : (Fin d → Bool) → Hist → (Fin ((R+1)*dim*width) → Bool) → RawBroadcast ar → Prop)
    (template : (Fin d → Bool) → Hist → (Fin ((R+1)*dim*width) → Bool) → DiagonalTallyPacketEmit.Frame)
    (entries : (Fin d → Bool) → Hist → (Fin ((R+1)*dim*width) → Bool) → ℕ)
    (frames : ∀ i h c, AdmittedPinnedFrames G args pin L fixed positive size base fit ar hdr (fun x u => (B x u).start) (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id
      (owners h) (source h) i (code h) c (allowed i h c) (template i h c) (entries i h c))
    (checked : ∀ i h c v, ParsedPreCall G args pin L fixed positive size base fit hdr (fun x u => (B x u).start) (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) id i
      ⟨code h,v,c⟩ → LocalRow.declarationInRange v ∧ allowed i h c v)
    (honest : ∀ i h c (v : Routed (b:=ar.b) (s:=ar.s) (owners h)), allowed i h c (routeBroadcast ar (owners h) v).val)

set_option maxHeartbeats 300000 in
/-- The route supplied to the decoder at each pin, history and subtotal is
the joint preparation equivalence of the admitted physical frame. -/
noncomputable def admittedReportRoutes (i : I) (h : Hist) (c : Claim) :
    (Σ v : RawBroadcast ar, ParsedPreCall G args pin L fixed positive size base fit hdr U ib hb sb digits id i
      ⟨code h,v,c⟩) ≃ Σ v : routes h, proposals i h v :=
  (frames i h c).preparations G args pin L fixed positive size base fit ar hdr U ib hb sb digits id
    (owners h) (source h) i (code h) c (allowed i h c) (template i h c) (entries i h c) (checked i h c) (honest i h c)

local notation3 (prettyPrint := false) "registered" => admittedReportRoutes gen G pub reg pin L args fixed positive
  size base fit ar id hdr code B owners source allowed template entries frames checked honest

variable (decoder : PreparedHistoryDecoder gen id G pub reg pin L hdr code args fixed positive size base fit B)
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (x : {ext // PositiveExterior G args pin w ext ∧ PinStart.preCallSupport (fun y v => (B y v).start) id ext}) (u : Fin (R+1)),
      let node := B ⟨x.val,x.property.1⟩ u
      PositiveContinuation id gen n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n))
        node.start.bank node.memory node.pins node.used limit)

set_option maxHeartbeats 400000 in
private theorem supportedOnRoute
    (routed : ∀ i h c, (Σ v : RawBroadcast ar,
      ParsedPreCall G args pin L fixed positive size base fit hdr U ib hb sb digits id i ⟨code h,v,c⟩) ≃
      Σ v : routes h, proposals i h v)
    (i : I) (h : Hist) (v : routes h) (c : Claim) (reports : proposals i h v) (u : Fin (R+1)) :
    pinnedReportCutAt G args pin L fixed positive size base fit ar hdr U ib hb sb digits id i (code h) c
        ((routed i h c).symm ⟨v,reports⟩) u (reports u) →
      jointReportCutAt (supportedTeam id B limit burst room next)
        ((decoder.supported limit burst room next routes proposals routed).val.symm ⟨i,h,v,c,reports⟩) u (reports u) := by
  rintro ⟨cur,desc,cut⟩
  exact ⟨cur,desc,PreparedHistoryDecoder.supported_reportCut gen id G pub reg pin L hdr code args fixed positive size base fit B
    decoder limit burst room next routes proposals routed i h v c reports u (reports u) cur desc cut⟩

set_option maxHeartbeats 700000 in
/-- Every unscreened report and subtotal on the registered decoder reaches
the genuine scanner and argument launcher on its supported positive team. -/
theorem PreparedHistoryDecoder.admitted_reportCut (i : I) (h : Hist) (v : routes h) (c : Claim)
    (reports : proposals i h v) (u : Fin (R+1)) :
    jointReportCutAt (supportedTeam id B limit burst room next)
      ((decoder.supported limit burst room next routes proposals registered).val.symm ⟨i,h,v,c,reports⟩) u (reports u) := by
  apply supportedOnRoute gen G pub reg pin L args fixed positive size base fit ar id hdr code B owners source
    decoder limit burst room next registered i h v c reports u
  dsimp only [admittedReportRoutes]
  have cut := (frames i h c).reportCut G args pin L fixed positive size base fit ar hdr U ib hb sb digits id
    (owners h) (source h) i (code h) c (allowed i h c) (template i h c) (entries i h c)
    (checked i h c) (honest i h c) v reports u
  with_reducible exact cut

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
