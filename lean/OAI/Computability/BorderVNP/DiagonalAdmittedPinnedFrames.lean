import OAI.Computability.BorderVNP.DiagonalPinnedBroadcastRouting
import OAI.Computability.BorderVNP.DiagonalObservedFrameBuilders

/-! # Selecting one physical signed implementation for each admitted cube broadcast -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w reserve dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (ar : CubeArena.Layout)
local notation "cap" => declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s
variable (width : L.header=PositiveFields.width reserve ar.n ar.header.d
      (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally)
    {gen : Fragment IO}
    (U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (S : SourceReports ar owners) (rawPin : Fin d → Bool)
    (profile : Fin reserve → Bool) (claim : Fin ((R+1)*dim*tally) → Bool)

local notation "Fields" => PositiveFields reserve ar.n ar.header.d cap (R+1) dim tally
local notation3 (prettyPrint := false) "p(" c ")" => (⟨profile,c,claim⟩ : Fields)
local notation3 (prettyPrint := false) "head" => fun c : RawBroadcast ar => (p(c)).bits
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
/-- The native pin return and its public/macro inputs on a variable wire
allocation. The admitted wire reads the same public header as the decoder. -/
noncomputable abbrev pinnedBroadcastFrame (c : RawBroadcast ar) (wire : WireLayout (R+1) r link)
    (same : wire.header=L.header) :=
  let back := (HeaderExterior.changeLayout L wire same (p(c)).bits).symm
  let key := fun x : HeaderExterior wire (p(c)).bits => (headers).symm ⟨p(c),back x⟩
  let pins := fun x u => (U (key x) u).pins
    ((Equiv.arrowCongr (finCongr (pinWidth (key x) u).symm) (Equiv.refl Bool)) ((G.jointGuess ib hb sb).symm rawPin u))
  PreparationFrame G wire ar (decodedBroadcast ar c) (p(c)).bits live (fun x u => (U (key x) u).pub)
    (fun x u => CompactMachine.install gen n (U (key x) u).routines) (fun x u => (pins x u).val.2.1)
    (fun x u => (pins x u).val.2.2)

local notation3 (prettyPrint := false) "PF(" c "," wire "," same ")" =>
  pinnedBroadcastFrame G args live L fixed hw size base fit ar width U ib hb sb pinWidth rawPin profile claim c wire same
variable (allowed : RawBroadcast ar → Prop) (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ)

/-- The wires, complete writer frames and observed builders of the very same
physical implementation, indexed by the parsed cube bits. -/
structure AdmittedPinnedFrames where
  /-- Header and relay lengths for this physical broadcast. -/
  wire : RawBroadcast ar → WireLayout (R+1) r link
  /-- All relay layouts use the original header length. -/
  extent : ∀ c, (wire c).header=L.header
  /-- The actual native preparation on each admitted declaration. -/
  frame : ∀ (c : CheckedBroadcast ar), allowed c.val → PF(c.val,wire c.val,extent c.val)
  /-- The installed per-exterior owner and report programs of that preparation. -/
  builder : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frame c a).Builders fixed id owners
  /-- Source rows and endpoint tests of the selected builder. -/
  source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frame c a).SourceAgreement fixed S (builder c a)
  /-- The selected inverse retains its actual routing and ownership scans. -/
  observed : ∀ (c : CheckedBroadcast ar) (a : allowed c.val),
    (frame c a).ObservedBuilders fixed id owners template entries (builder c a)

set_option maxHeartbeats 900000 in
/-- Choose each admitted frame together with its observed scanner inverse.
A malformed or over-capacity declaration only needs a wire with the parser's
header extent, since a prepared execution at those bits is impossible. -/
theorem admittedPinnedFrames_nonempty
    (real : ∀ c : CheckedBroadcast ar, allowed c.val →
      ∃ (wire : WireLayout (R+1) r link) (same : wire.header=L.header) (F : PF(c.val,wire,same))
        (B : F.Builders fixed id owners), F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed id owners template entries B) :
    Nonempty (AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners S
      rawPin profile claim allowed template entries) := by
  classical
  have selectWire (c : RawBroadcast ar) : ∃ (wire : WireLayout (R+1) r link) (same : wire.header=L.header),
      LocalRow.declarationInRange c → allowed c →
      ∃ (F : PF(c,wire,same)) (B : F.Builders fixed id owners),
        F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed id owners template entries B := by
    by_cases h : LocalRow.declarationInRange c ∧ allowed c
    · obtain ⟨wire,same,F,B,agree,seen⟩ := real ⟨c,h.1⟩ h.2
      exact ⟨wire,same,fun _ _ => ⟨F,B,agree,seen⟩⟩
    · exact ⟨L,rfl,fun range admitted => (h ⟨range,admitted⟩).elim⟩
  choose wire same build using selectWire
  choose F B agree seen using fun (c : CheckedBroadcast ar) (a : allowed c.val) => build c.val c.property a
  exact ⟨⟨wire,same,F,B,agree,seen⟩⟩

set_option maxHeartbeats 1200000 in
/-- Select all eligible broadcasts together with any additional physical
readback of their actual frame and builder. The frame used by the weighted
inverse remains the one used for the native return and its terminating
clock at every raw word. -/
theorem admittedPinnedFrames_with
    (Q : ∀ (c : CheckedBroadcast ar) (_ : allowed c.val) (wire : WireLayout (R+1) r link)
      (same : wire.header=L.header) (F : PF(c.val,wire,same)), F.Builders fixed id owners → Prop)
    (real : ∀ (c : CheckedBroadcast ar) (a : allowed c.val),
      ∃ (wire : WireLayout (R+1) r link) (same : wire.header=L.header) (F : PF(c.val,wire,same))
        (B : F.Builders fixed id owners), F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed id owners template entries B ∧
        Q c a wire same F B) :
    ∃ chosen : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners S
      rawPin profile claim allowed template entries,
      ∀ (c : CheckedBroadcast ar) (a : allowed c.val),
        Q c a (chosen.wire c.val) (chosen.extent c.val) (chosen.frame c a) (chosen.builder c a) := by
  classical
  have selectWire (c : RawBroadcast ar) : ∃ (wire : WireLayout (R+1) r link) (same : wire.header=L.header),
      ∀ (ok : LocalRow.declarationInRange c) (a : allowed c), ∃ (F : PF(c,wire,same)) (B : F.Builders fixed id owners),
        F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed id owners template entries B ∧ Q ⟨c,ok⟩ a wire same F B := by
    by_cases e : LocalRow.declarationInRange c ∧ allowed c
    · obtain ⟨wire,same,F,B,agree,seen,held⟩ := real ⟨c,e.1⟩ e.2
      exact ⟨wire,same,fun _ _ => ⟨F,B,agree,seen,held⟩⟩
    · exact ⟨L,rfl,fun ok a => (e ⟨ok,a⟩).elim⟩
  choose wire same build using selectWire
  choose F B agree seen held using fun (c : CheckedBroadcast ar) (a : allowed c.val) => build c.val c.property a
  exact ⟨⟨wire,same,F,B,agree,seen⟩,held⟩

local notation3 (prettyPrint := false) "runs(" c ")" => ((ext : HeaderExterior L (p(c)).bits) ×
  pinnedPreps G args live U ib hb sb pinWidth id ((headers).symm ⟨p(c),ext⟩) rawPin)

variable (candidates : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth
    id owners S rawPin profile claim allowed template entries)

set_option maxHeartbeats 750000 in
/-- The actual joint prepared inputs at the fixed raw pin, profile and claim
are in bijection with the padded routed assignments and their private reports.
The scanner receipts of this very equivalence are retained by the candidate. -/
noncomputable def AdmittedPinnedFrames.preparations
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners, allowed (routeBroadcast ar owners q).val) :
    (Σ c : RawBroadcast ar, runs(c)) ≃ Σ q : {v : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners // S.pins v},
      S.actual q.val :=
  routedPinnedPreparations G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners S rawPin
    profile claim candidates.wire candidates.extent allowed checked honest candidates.frame candidates.builder candidates.source

end TeamContraction

end BorderVNP
end Computability
end OAI
