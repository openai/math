import OAI.Computability.BorderVNP.DiagonalRegisteredReportCut
import OAI.Computability.BorderVNP.DiagonalAdmittedFrameOwnedState
import OAI.Computability.BorderVNP.DiagonalPrefixFinishRun

/-! # Original ownership states in the admitted supported route decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.BootedPinStart

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine SignedPrep Routing JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter DiagonalTallyCellReports

set_option autoImplicit false
set_option maxRecDepth 8500


variable {R r t d link inner n w reserve dim width : ℕ} {Edge Hist : Type} (gen : Fragment IO)
    (G : Wiring R r t d link inner n Edge) (pub : Fin (R+1) → Arg → Word w) (reg : Fin (R+1) → Bank w)
    (pin : Fin d → Bool) (L : WireLayout (R+1) r link) (args : Fin (R+1) → UnitAddresses)
    (fixed : Block (R+1)) (positive : 0<w) (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (sa : SignedTaskArena.Layout)
variable
    (hdr : L.header=PositiveFields.width reserve sa.cube.n sa.cube.header.d
      (declarationCap sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.s) (R+1) dim width)
    (code : Hist ↪ (Fin reserve → Bool))
    (B : (x : {ext // PositiveExterior G args pin w ext}) → (u : Fin (R+1)) →
      BootedPinStart gen G pub reg args pin x.val u)
    (owners : Hist → (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1))
    (source : (h : Hist) → SourceReports sa.cube (owners h))

local notation "I" => Fin d → Bool
local notation "Claim" => Fin ((R+1)*dim*width) → Bool
local notation3 (prettyPrint := false) "U" => fun x u => (B x u).start
local notation3 (prettyPrint := false) "ib" => fun u => (args u).ibase
local notation3 (prettyPrint := false) "hb" => fun u => (args u).hbase
local notation3 (prettyPrint := false) "sb" => fun u => (args u).starbase
local notation3 (prettyPrint := false) "digits" => fun (_ : {ext // PositiveExterior G args pin w ext}) (_ : Fin (R+1)) => rfl
local notation3 (prettyPrint := false) "routes" => fun h : Hist =>
  {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) (owners h) // (source h).pins v}
local notation3 (prettyPrint := false) "proposals" => fun (_ : I) (h : Hist) (v : routes h) =>
  (source h).actual v.val

variable (allowed : (Fin d → Bool) → Hist → (Fin ((R+1)*dim*width) → Bool) → RawBroadcast sa.cube → Prop)
    (template : (Fin d → Bool) → Hist → (Fin ((R+1)*dim*width) → Bool) → DiagonalTallyPacketEmit.Frame)
    (entries : (Fin d → Bool) → Hist → (Fin ((R+1)*dim*width) → Bool) → ℕ)
    (frames : ∀ i h c, AdmittedPinnedFrames G args pin L fixed positive size base fit sa.cube hdr (fun x u => (B x u).start) (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) sa.id
      (owners h) (source h) i (code h) c (allowed i h c) (template i h c) (entries i h c))
    (checked : ∀ i h c v, ParsedPreCall G args pin L fixed positive size base fit hdr (fun x u => (B x u).start) (fun u => (args u).ibase) (fun u => (args u).hbase) (fun u => (args u).starbase) (fun _ _ => rfl) sa.id i
      ⟨code h,v,c⟩ → LocalRow.declarationInRange v ∧ allowed i h c v)
    (honest : ∀ i h c (v : Routed (b:=sa.cube.b) (s:=sa.cube.s) (owners h)), allowed i h c (routeBroadcast sa.cube (owners h) v).val)

local notation3 (prettyPrint := false) "registered" => admittedReportRoutes gen G pub reg pin L args fixed positive
  size base fit sa.cube sa.id hdr code B owners source allowed template entries frames checked honest

variable (decoder : PreparedHistoryDecoder gen sa.id G pub reg pin L hdr code args fixed positive size base fit B)
    (limit burst : ℕ) (room : TeamScales.width n (1/2) ≤ burst)
    (next : ∀ (x : {ext // PositiveExterior G args pin w ext ∧ PinStart.preCallSupport (fun y v => (B y v).start) sa.id ext}) (u : Fin (R+1)),
      let node := B ⟨x.val,x.property.1⟩ u
      PositiveContinuation sa.id gen n (pub u) (TeamSiteEvents.macros (w:=w) (siteLibrary gen) (nativeClock n))
        node.start.bank node.memory node.pins node.used limit)

open _root_.OAI.Computability.BorderVNP.Cube.Physical.NativeLedger

/-- Read the entire ownership stage of an already fixed supported prefix. -/
noncomputable def jointOwnedStateAt {R n w axes boxes lanes copies symbols : ℕ} {X : Type} {gen : Fragment IO}
    {id : TableEntry axes boxes lanes copies symbols → ℕ}
    (T : X → Fin (R+1) → PositiveTeam id gen n w) (z : JointBeforeCells T) (u : Fin (R+1)) :
    (Arg → Word w) × List (TeamRAM.Event w) × Bank w × Memory w :=
  ((T z.1 u).pub,(prefixVisits (T z.1 u) (z.2 u)).owned.val)

local notation3 (prettyPrint := false) "T" => supportedTeam sa.id B limit burst room next

set_option maxHeartbeats 450000 in
private theorem ownedOnRoute
    (routed : ∀ i h c, (Σ v : RawBroadcast sa.cube,
      ParsedPreCall G args pin L fixed positive size base fit hdr U ib hb sb digits sa.id i ⟨code h,v,c⟩) ≃
      Σ v : routes h, proposals i h v)
    (i : I) (h : Hist) (v : routes h) (c : Claim) (reports : proposals i h v) (u : Fin (R+1)) :
    jointOwnedStateAt T ((decoder.supported limit burst room next routes proposals routed).val.symm ⟨i,h,v,c,reports⟩) u =
      pinnedOwnedStateAt G args pin L fixed positive size base fit sa hdr U ib hb sb digits i (code h) c
        ((routed i h c).symm ⟨v,reports⟩) u := by
  let observe (p : Σ M : PinStart gen n w, M.Prefix sa.id) := (p.1.pub,(p.1.visited p.2).owned.val)
  exact congrArg observe (PreparedHistoryDecoder.supported_restored_pair gen sa.id G pub reg pin L hdr code args fixed
    positive size base fit B decoder limit burst room next routes proposals routed i h v c reports u)

set_option maxHeartbeats 850000 in
/-- Each registered decoder tuple runs on the supported team's own public
words. Its complete ownership return is precisely the one reconstructed by
the admitted frame from that same tuple's routed report. -/
theorem PreparedHistoryDecoder.admitted_ownedSourceState (i : I) (h : Hist) (v : routes h) (c : Claim)
    (reports : proposals i h v) (u : Fin (R+1)) :
    jointOwnedStateAt T ((decoder.supported limit burst room next routes proposals registered).val.symm ⟨i,h,v,c,reports⟩) u =
      (frames i h c).sourceOwnedState G args pin L fixed positive size base fit sa hdr U ib hb sb digits
        (owners h) (source h) i (code h) c (allowed i h c) (template i h c) (entries i h c) (honest i h c) v reports u := by
  have restore := ownedOnRoute gen G pub reg pin L args fixed positive size base fit sa hdr code B owners source decoder
    limit burst room next registered i h v c reports u
  have native := (frames i h c).pinned_ownedSourceState G args pin L fixed positive size base fit sa hdr U ib hb sb digits
    (owners h) (source h) i (code h) c (allowed i h c) (template i h c) (entries i h c)
    (checked i h c) (honest i h c) v reports u
  let routed := (frames i h c).preparations G args pin L fixed positive size base fit sa.cube hdr U ib hb sb digits
    sa.id (owners h) (source h) i (code h) c (allowed i h c) (template i h c) (entries i h c) (checked i h c) (honest i h c)
  have equal : registered i h c = routed := rfl
  let observe (E : (Σ v : RawBroadcast sa.cube,
      ParsedPreCall G args pin L fixed positive size base fit hdr U ib hb sb digits sa.id i
        ⟨code h,v,c⟩) ≃ Σ v : routes h, proposals i h v) :=
    pinnedOwnedStateAt G args pin L fixed positive size base fit sa hdr U ib hb sb digits i (code h) c (E.symm ⟨v,reports⟩) u
  with_reducible exact restore.trans ((congrArg observe equal).trans native)

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
