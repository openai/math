import OAI.Computability.BorderVNP.PackedTerminalSignedGridSourceCost
import OAI.Computability.BorderVNP.PackedTerminalSignedEmitterCost

/-! # The complete widened signed packet emitter on its actual frozen grid -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Cover Cover.AddressCircuit Crossing Packing Packing.Inherited Packing.SewnField
open Packing.CellAddressCircuit Packing.Inherited.FrozenTape TeamContraction Diagonal.ExternalSew Diagonal.ExternalSew.GridHosts
open Shortening.PublicCapacity VPVNP.VerifierNetwork PackedHistoryCircuit.Normalized.SelectedSchedule
open GeometryFrameEncoding CellPacketGeometry CellPacketGeometry.LiveWords CellPacketGeometry.History
open CellPacketGeometry.History.Native CellSparse.Packet Packing.RoutingOutputs
open scoped Classical
set_option quotPrecheck false
set_option maxHeartbeats 1300000
set_option maxRecDepth 5200

variable {I X Geo Move : Type} [Fintype I] [Fintype X] [Fintype Geo] [Fintype Move]
    {R r t pins link inner n tiles groups copies : ℕ} {Edge : Type}
    (G : Wiring R r t pins link inner n Edge) (htiles : 0 < tiles) (mult : groups*copies=R+1)
    (hg : 0<blockWidth (r*n) tiles) (small : blockWidth (r*n) tiles ≤ link)
    (shape : Shape) {q d C b w J reserve : ℕ} (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C)
    (cf : C ≤ 2^b) (fmt : Format) (read : RouteRows.Pins Move q (d+1) shape.sites shape.edges w → Geo)
    (vf : shape.sites ≤ 2^w) (host width : Fin (groups*tiles) → ℕ) (mark : ℕ → ℕ → ℕ)

local notation "live" => (R+1)*tiles
local notation "p" => (⟨R,r,G.program.length+t,link,blockWidth (r*n) tiles,tiles⟩ : FieldExport.Params)
local notation3 (prettyPrint := false) "F" => TerminalCells.fields (Move:=Move) (q:=q) (d:=d) (E:=shape.edges)
  vf cf host width
local notation3 (prettyPrint := false) "B" => FieldExport.fields F p mark
local notation3 (prettyPrint := false) "primary" => frozenPrimary (X:=X) (reserve:=reserve) enum number cf fmt read
local notation3 (prettyPrint := false) "source" => stagedSource B (FieldExport.withSewnFields primary)
local notation3 (prettyPrint := false) "saved" => Retained.Terminal.saved (X:=X) (reserve:=reserve) (Geo:=Geo)
  (a:=shape.sites) (w:=w) (d:=w) fmt

variable (present : Fin shape.edges → Wires Move q d shape.sites shape.edges w b)
local notation3 (prettyPrint := false) "raw" => Grid.physicalOperands G htiles mult hg small F mark present
local notation3 (prettyPrint := false) "past" => stagedHistory (s:=shape.sites) (w:=w)
  (Sewn.terminalHistory (Geo:=Geo) fmt (F).sites raw)

variable {L native v cap qa : ℕ} (extend : w ≤ native) (owner : b ≤ native)
    (old : Fin J → Fin shape.sites) (controls : Fin v → Fin (2^native))
    (boxes : Fin shape.sites → List (Source.Box (Fin J))) (arena stride gap desc g digits : ℕ)
    (occupied : Fin (shape.edges+4*(R+1)*tiles) → StagedWires (Wires Move q d shape.sites shape.edges w b) shape.sites w)
    (portUsed : Fin ((R+1)*tiles) → Bool) (valid : StagedWires (Wires Move q d shape.sites shape.edges w b) shape.sites w)

local notation3 (prettyPrint := false) "schema₀" => fmt.schema.append (Sewn.schema (2*shape.edges+6*(R+1)*tiles) w)
local notation3 (prettyPrint := false) "final₀" => FinalTies.tieSchema (shape.edges+(p).slots) live native
local notation3 (prettyPrint := false) "priv₀" => FinalReports.Spare.priv (C:=C) (g:=g) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "report₀" => FinalReports.Spare.reports (C:=C) (g:=g) (digits:=digits) (E:=Fin J)
local notation3 (prettyPrint := false) "fields₀" => Fields.widenWidths (stagedFields B) extend (Sum.inr false)
local notation3 (prettyPrint := false) "feed₀" => Terminal.feeds (s:=⟨shape.sites,shape.edges+(p).slots⟩)
  fields₀ occupied portUsed boxes past (SignedFields.liveFrame fields₀ boxes old arena stride gap desc g digits) valid
variable (hs : ∀ j, ((fmt.schema.append (Sewn.schema (2*shape.edges+6*(R+1)*tiles) w)).tags j).length≤cap)
  (hf : ∀ j, ((FinalTies.tieSchema (shape.edges+4*(R+1)*tiles) ((R+1)*tiles) native).tags j).length≤cap)
  (depth : w≤qa) (sites : shape.sites<2^qa) (cells : C<2^b)
  (sw : ∀ j, (fmt.schema.append (Sewn.schema (2*shape.edges+6*(R+1)*tiles) w)).width j≤native)
  (fw : ∀ j, (FinalTies.tieSchema (shape.edges+4*(R+1)*tiles) ((R+1)*tiles) native).width j≤native)
local notation3 (prettyPrint := false) "tpl₀" => template schema₀ final₀ boxes hs hf priv₀ report₀
local notation3 (prettyPrint := false) "items₀" => roster shape.sites schema₀ final₀
variable (base : Fin (roster shape.sites (fmt.schema.append (Sewn.schema (2*shape.edges+6*(R+1)*tiles) w))
    (FinalTies.tieSchema (shape.edges+4*(R+1)*tiles) ((R+1)*tiles) native)).length → Fin (C+1))
  (pointer : Fin J → (template (fmt.schema.append (Sewn.schema (2*shape.edges+6*(R+1)*tiles) w))
    (FinalTies.tieSchema (shape.edges+4*(R+1)*tiles) ((R+1)*tiles) native) boxes hs hf
    (FinalReports.Spare.priv (C:=C) (g:=g) (digits:=digits) (E:=Fin J)) FinalReports.Spare.reports).Fields)
  (pad : (roster shape.sites (fmt.schema.append (Sewn.schema (2*shape.edges+6*(R+1)*tiles) w))
    (FinalTies.tieSchema (shape.edges+4*(R+1)*tiles) ((R+1)*tiles) native)).length < 2^qa) (dest header : ℕ)
local notation3 (prettyPrint := false) "packet₀" => (feed₀).ordered schema₀ final₀ boxes hs hf priv₀ report₀ depth depth
  sites cells sw fw base pointer pad dest header

/-- Cable triples, routing outputs, private site controls and the signed
packet are consecutive blocks of the returned public word array. -/
def signedGridOutputCount (cables cells original liveCount controls packetWords : ℕ) : ℕ :=
  cables*3 + (RoutingOutputs.count cables cells original liveCount +
    ((cells+(original+cells))+(controls+packetWords)))

/-- The single native terminal emission frame. Its routing inputs and saved
initial verifier were fixed before the public histogram word is supplied. -/
noncomputable abbrev signedGridEmitter :
    Frame ((X ⊕ Fin reserve) ⊕ fmt.Output Geo shape.sites w w)
      (Fin (signedGridOutputCount (shape.edges+(p).slots) C J live v (Total (tpl₀).publicDepth (tpl₀).chunkDepth)) × Fin native) :=
  Retained.emitter fields₀ owner old id (Retained.privateControls fields₀ old controls packet₀) source saved

variable (fieldSource : Frame
  (StagedWires (Wires Move q d shape.sites shape.edges w b) shape.sites w ⊕ fmt.Output Geo shape.sites w w)
  (FinalReports.Spare.Field C g digits (Fin J) × Fin native))
local notation3 (prettyPrint := false) "feedAny" => Terminal.feeds (s:=⟨shape.sites,shape.edges+(p).slots⟩)
  fields₀ occupied portUsed boxes past fieldSource valid
local notation3 (prettyPrint := false) "packetAny" => (feedAny).ordered schema₀ final₀ boxes hs hf priv₀ report₀ depth depth
  sites cells sw fw base pointer pad dest header
local notation3 (prettyPrint := false) "reportBudget" => Terminal.ReportFieldBound ⟨shape.sites,shape.edges+(p).slots⟩
  live C J w b native g digits fieldSource.size

/-- Frozen geometry, retained history, and an installed terminal field frame
as one physical array of packet words. -/
noncomputable abbrev reportGridEmitter :
    Frame ((X ⊕ Fin reserve) ⊕ fmt.Output Geo shape.sites w w)
      (Fin (signedGridOutputCount (shape.edges+(p).slots) C J live v (Total (tpl₀).publicDepth (tpl₀).chunkDepth)) × Fin native) :=
  Retained.emitter fields₀ owner old id (Retained.privateControls fields₀ old controls packetAny) source saved

omit [Fintype I] in
/-- All returned gates and bits of a widened frozen grid using a measured
scalar field frame on the selected staged wires. -/
theorem reportGridEmitter_bits (fieldBound : reportBudget) (key : keyWidth q (d+1) ≤ L) (short : w≤L) (bits : native≤L)
    (logs : Nat.clog 2 (routingRows shape C J live) ≤ L)
    (wa : qa≤L) (wp : (tpl₀).publicDepth≤L) (wd : (tpl₀).chunkDepth≤L) (wb : (tpl₀).recordDepth≤L)
    (wh : Nat.clog 2 ((items₀).length+(C+1))≤L) (wl : Nat.clog 2 ((shape.sites+1)+(items₀).length)≤L) :
    let o := Total (tpl₀).publicDepth (tpl₀).chunkDepth
    let output := signedGridOutputCount (shape.edges+(p).slots) C J live v o
    let emit := Retained.emitter fields₀ owner old id (Retained.privateControls fields₀ old controls packetAny) source saved
    emit.size+output*native ≤
      (11920000*routingRows shape C J live+16008100*sourceVolume schema₀ final₀ boxes report₀+v)*(L+1)^3 := by
  intro o output emit
  let rows := routingRows shape C J live
  have same : 1+CellAddressCircuit.count shape.sites (shape.edges+(p).slots) live C+J+live=rows := by
    dsimp only [rows,routingRows,FieldExport.Params.slots]; rw [Nat.mul_assoc 4]
  have cost := retainedReport_bits fields₀ owner old source saved controls schema₀ boxes g digits
    occupied portUsed past valid hs hf depth depth sites cells sw fw base pointer pad dest header fieldSource fieldBound
    ⟨short,owner.trans bits,bits,same ▸ logs⟩ wa wp wd wb wh wl
  have sourceCost := signedGridSource_size (X:=X) (reserve:=reserve) G htiles mult hg small shape enum number cf fmt read
    vf host width mark present key (owner.trans bits) short logs
  change emit.size+output*native ≤ (source).size+(saved).size+(past).size+
    (10020000*(1+CellAddressCircuit.count shape.sites (shape.edges+(p).slots) live C+J+live)+16008100*sourceVolume schema₀ final₀ boxes report₀+v)*(L+1)^3 at cost
  rw [same] at cost
  exact cost.trans ((Nat.add_le_add_right sourceCost _).trans_eq (by dsimp only [rows]; ring))

omit [Fintype I] in
/-- A measured report frame, the retained frozen source and all output words
fit a single fixed multiple of the actual routing row count. -/
theorem reportGridEmitter_charge (fieldBound : reportBudget) (H E A controlsCap : ℕ) (hpos : 1 ≤ H) (nv : native = H^(E+2))
    (key : keyWidth q (d+1) ≤ native) (logs : Nat.clog 2 (routingRows shape C J live) ≤ native)
    (wa : qa ≤ native) (wp : (tpl₀).publicDepth ≤ native) (wd : (tpl₀).chunkDepth ≤ native)
    (wb : (tpl₀).recordDepth ≤ native) (wh : Nat.clog 2 ((items₀).length+(C+1)) ≤ native)
    (wl : Nat.clog 2 ((shape.sites+1)+(items₀).length) ≤ native)
    (volume : sourceVolume schema₀ final₀ boxes report₀ ≤ A*routingRows shape C J live*H^(max 2 (E+2)))
    (controlsFit : v ≤ controlsCap) :
    let output := signedGridOutputCount (shape.edges+(p).slots) C J live v (Total (tpl₀).publicDepth (tpl₀).chunkDepth)
    let emit := Retained.emitter fields₀ owner old id (Retained.privateControls fields₀ old controls packetAny) source saved
    emit.size+output*native ≤ (8*(11920000+16008100*A+controlsCap))*routingRows shape C J live*H^(4*(E+2)) := by
  intro output emit
  have built := reportGridEmitter_bits (X:=X) (reserve:=reserve) G htiles mult hg small shape enum number cf fmt read
    vf host width mark present extend owner old controls boxes g digits occupied portUsed valid
    hs hf depth sites cells sw fw base pointer pad dest header fieldSource fieldBound key extend le_rfl logs wa wp wd wb wh wl
  let rows := routingRows shape C J live
  let vol := sourceVolume schema₀ final₀ boxes report₀
  let u := E+2
  change emit.size+output*native ≤ (11920000*rows+16008100*vol+v)*(native+1)^3 at built
  have xp : max 2 (E+2) = u := max_eq_right (by omega)
  rw [xp] at volume
  have nonzero : 1 ≤ rows := by dsimp only [rows,routingRows]; omega
  have huge : rows ≤ rows*H^u := Nat.le_mul_of_pos_right _ (Nat.pow_pos hpos)
  have ctrl : v ≤ controlsCap*(rows*H^u) := controlsFit.trans (Nat.le_mul_of_pos_right _ (nonzero.trans huge))
  have mass : 11920000*rows+16008100*vol+v ≤ (11920000+16008100*A+controlsCap)*rows*H^u := by
    calc
      _ ≤ 11920000*(rows*H^u)+16008100*(A*rows*H^u)+controlsCap*(rows*H^u) :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ huge) (Nat.mul_le_mul_left _ volume)) ctrl
      _ = _ := by ring
  have room : native+1 ≤ 2*H^u := by
    change native+1 ≤ 2*H^(E+2)
    rw [nv]
    have hpow : 0 < H^(E+2) := Nat.pow_pos hpos
    omega
  refine built.trans ((Nat.mul_le_mul mass (Nat.pow_le_pow_left room 3)).trans_eq ?_)
  change (11920000+16008100*A+controlsCap)*rows*H^u*(2*H^u)^3 =
    (8*(11920000+16008100*A+controlsCap))*rows*H^(4*u)
  rw [mul_pow,←pow_mul,show 4*u=u+u*3 by omega,pow_add]
  ring

omit [Fintype I] in
/-- All gates and output bits of the physically staged signed terminal. The
short tape words, new extents and original pointers share the same emitter
with the stable four-slot routing rows and the full native-width packet. -/
theorem signedGridEmitter_bits (key : keyWidth q (d+1) ≤ L) (short : w≤L) (bits : native≤L)
    (logs : Nat.clog 2 (routingRows shape C J live) ≤ L)
    (wa : qa≤L) (wp : (tpl₀).publicDepth≤L) (wd : (tpl₀).chunkDepth≤L) (wb : (tpl₀).recordDepth≤L)
    (wh : Nat.clog 2 ((items₀).length+(C+1))≤L) (wl : Nat.clog 2 ((shape.sites+1)+(items₀).length)≤L) :
    let o := Total (tpl₀).publicDepth (tpl₀).chunkDepth
    let output := signedGridOutputCount (shape.edges+(p).slots) C J live v o
    let emit := Retained.emitter fields₀ owner old id (Retained.privateControls fields₀ old controls packet₀) source saved
    emit.size+output*native ≤
      (11920000*routingRows shape C J live+16008100*sourceVolume schema₀ final₀ boxes report₀+v)*(L+1)^3 := by
  exact reportGridEmitter_bits (X:=X) (reserve:=reserve) G htiles mult hg small shape enum number cf fmt read
    vf host width mark present extend owner old controls boxes g digits occupied portUsed valid
    hs hf depth sites cells sw fw base pointer pad dest header
    (SignedFields.liveFrame fields₀ boxes old arena stride gap desc g digits)
    (Terminal.signedReportFieldBound (s:=⟨shape.sites,shape.edges+(p).slots⟩) fields₀ boxes old arena stride gap desc g digits)
    key short bits logs wa wp wd wb wh wl

omit [Fintype I] in
/-- The actual emitter and its written bits satisfy the charge used to
reserve the geometry table. The exponent pays for the full native report words
and all three powers of the real gate word width, uniformly in its values. -/
theorem signedGridEmitter_charge (H E A controlsCap : ℕ) (hpos : 1 ≤ H) (nv : native = H^(E+2))
    (key : keyWidth q (d+1) ≤ native) (logs : Nat.clog 2 (routingRows shape C J live) ≤ native)
    (wa : qa ≤ native) (wp : (tpl₀).publicDepth ≤ native) (wd : (tpl₀).chunkDepth ≤ native)
    (wb : (tpl₀).recordDepth ≤ native) (wh : Nat.clog 2 ((items₀).length+(C+1)) ≤ native)
    (wl : Nat.clog 2 ((shape.sites+1)+(items₀).length) ≤ native)
    (volume : sourceVolume schema₀ final₀ boxes report₀ ≤ A*routingRows shape C J live*H^(max 2 (E+2)))
    (controlsFit : v ≤ controlsCap) :
    let output := signedGridOutputCount (shape.edges+(p).slots) C J live v (Total (tpl₀).publicDepth (tpl₀).chunkDepth)
    let emit := Retained.emitter fields₀ owner old id (Retained.privateControls fields₀ old controls packet₀) source saved
    emit.size+output*native ≤ (8*(11920000+16008100*A+controlsCap))*routingRows shape C J live*H^(4*(E+2)) := by
  exact reportGridEmitter_charge (X:=X) (reserve:=reserve) G htiles mult hg small shape enum number cf fmt read
    vf host width mark present extend owner old controls boxes g digits occupied portUsed valid
    hs hf depth sites cells sw fw base pointer pad dest header
    (SignedFields.liveFrame fields₀ boxes old arena stride gap desc g digits)
    (Terminal.signedReportFieldBound (s:=⟨shape.sites,shape.edges+(p).slots⟩) fields₀ boxes old arena stride gap desc g digits)
    H E A controlsCap hpos nv key logs wa wp wd wb wh wl volume controlsFit

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI
