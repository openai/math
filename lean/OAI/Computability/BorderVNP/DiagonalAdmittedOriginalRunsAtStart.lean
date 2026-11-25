import OAI.Computability.BorderVNP.DiagonalAdmittedOriginalRegistrations

/-! # Original report registrations at the actual restored start -/

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

local notation3 (prettyPrint := false) "T" => supportedTeam sa.id B limit burst room next


local notation3 (prettyPrint := false) "restore" => (decoder.supported limit burst room next routes proposals registered).val

local notation3 (prettyPrint := false) "atReturn(" i "," h "," v "," cc "," src "," u ")" =>
  (frames i h cc).sourceOwnedState G args pin L fixed positive size base fit sa hdr U ib hb sb digits
    (owners h) (source h) i (code h) cc (allowed i h cc) (template i h cc) (entries i h cc)
    (honest i h cc) v src u

set_option maxHeartbeats 800000 in
/-- The remaining report and roster checks run on exactly the start restored
by the decoder. Supplying this start to the local finish also retains its
complete positive continuation when the report layout is reindexed. -/
theorem PreparedHistoryDecoder.admittedRunsOnStart (i : I) (h : Hist) (v : routes h)
    (result : proposals i h v → Claim → JointBeforeCells T → Fin (R+1) → Prop)
    (issued : ∀ (src : proposals i h v) (cc : Claim) (u : Fin (R+1)),
      let start := (restore).symm ⟨i,h,v,cc,src⟩
      let team := T start.1 u
      RegisteredOriginalPrefix (team.pub,(prefixVisits team (start.2 u)).owned.val)
        atReturn(i,h,v,cc,src,u) (result src cc start u)) :
    ∀ (src : proposals i h v) (cc : Claim) (u : Fin (R+1)),
      result src cc ((restore).symm ⟨i,h,v,cc,src⟩) u := by
  intro src cc u
  exact (issued src cc u).atSource (decoder.admitted_ownedSourceState gen G pub reg pin L args fixed positive
    size base fit sa hdr code B owners source allowed template entries frames checked honest limit burst room
    next i h v cc src u)

/-- The original owned run yields the true continuation on every selected
report word and subtotal once its local registrations are supplied. -/
structure OriginalReportRule where
  /-- All physical reports and their issued continuations on this source. -/
  registrations : Prop
  /-- The native positive-prefix runs on the restored source tuples. -/
  runs : Prop
  /-- Decode each registration at its actual positive start. -/
  apply : registrations → runs

/-- Recover the original run for each report family, subtotal and team at its own prepared source. -/
noncomputable def PreparedHistoryDecoder.originalReportRule (i : I) (h : Hist) (v : routes h)
    (result : proposals i h v → Claim → JointBeforeCells T → Fin (R+1) → Prop) : OriginalReportRule where
  registrations := ∀ (src : proposals i h v) (cc : Claim) (u : Fin (R+1)),
    let start := (restore).symm ⟨i,h,v,cc,src⟩
    let team := T start.1 u
    RegisteredOriginalPrefix (team.pub,(prefixVisits team (start.2 u)).owned.val)
      atReturn(i,h,v,cc,src,u) (result src cc start u)
  runs := ∀ (src : proposals i h v) (cc : Claim) (u : Fin (R+1)),
    result src cc ((restore).symm ⟨i,h,v,cc,src⟩) u
  apply := decoder.admittedRunsOnStart gen G pub reg pin L args fixed positive size base fit sa hdr code B owners
    source allowed template entries frames checked honest limit burst room next i h v result

end TeamContraction.ProcessorSlots.BootedPinStart

end BorderVNP
end Computability
end OAI
