import OAI.Computability.BorderVNP.DiagonalSignedCandidateSite
import OAI.Computability.BorderVNP.DiagonalPublishedControlReadback

/-! # Choosing a real signed candidate site while retaining the deployed words and geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM TeamContraction JointHeader Packing BorderVNP.Cube Physical LocalRow
open PackedHistoryCircuit Crossing

variable {w R X : ℕ} {ar : CubeArena.Layout} {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {word : Broadcast ar.n ar.header.d ar.header.cap} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
    {frame base : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {d : ℕ} {P A : Type*} {bits : P → ℕ} {N : Network d P bits} {cell : N.Site → Fin ar.cells}
    {recv : A → Fin ar.cells} {amount : A → ℕ}

local notation3 (prettyPrint := false) "Site₀" => CandidateSite (X:=X) ar D pp lp word owner decl group
  frame base pins fields f guess pub mac reg mem host key sizes N cell recv amount

/-- The selected site's public operands are the ones of the deployed machine.
The pre-epoch state and charged cost are those of the named frozen geometry
return; its complete packet data can be used on exactly these registers and RAM. -/
structure CandidateSite.OnReturn (chosen : CandidateSite (X:=X) ar D pp lp word owner decl group
    frame base pins fields f guess pub mac reg mem host key sizes N cell recv amount)
    (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ) (profile : List Bool)
    (claims : List (List Bool)) (pad : ℕ) (preRegs : Bank w) (preMem : Memory w) (used charged : ℕ) : Prop where
  oldWords : chosen.old=old
  first : chosen.fresh=fresh
  gateCount : chosen.gates=gates
  outputCount : chosen.outputs=outputs
  fieldWidth : chosen.width=width
  stripeOffset : chosen.off=off
  stripeLength : chosen.ell=ell
  controlBase : chosen.control=controls
  copiedProfile : chosen.profile=profile
  copiedClaims : chosen.claims=claims
  padding : chosen.pad=pad
  geometryRegs : chosen.geometryRegs=preRegs
  geometryMemory : chosen.geometry=preMem
  pinCost : chosen.used=used
  geometryCost : chosen.profileCost=charged

/-- Recover the signed raw guard on the original placement arrays read from
the middle RAM. Only occupied original and live keys enter the decoded table. -/
theorem CandidateSite.original_input (chosen : Site₀) {privatePairs livePairs : ℕ → ℕ × ℕ}
    (physical : SlottedWriter ar D privatePairs livePairs pins pub chosen.middle base host key sizes)
    (reference : Directory.BankPlacement D pp lp I host key sizes)
    (keys : ∀ k, physical.placement.key k=reference.key k) :
    PinnedRawInput (ar:=ar) (D:=D) (pp:=privatePairs) (lp:=livePairs) (pub:=pub) (slotted:=chosen.middle) (base:=base)
      f chosen.old chosen.fresh chosen.gates chosen.outputs chosen.width chosen.off chosen.ell chosen.control
      chosen.profile chosen.claims chosen.pad word R X :=
  chosen.input.commonPlacement (physical.placement.directory_eq reference keys physical.destinations).symm

set_option maxHeartbeats 1500000
set_option maxRecDepth 6000

/-- Retain one specific bare pin and its originating frozen profile, selecting
the directory/epoch returns from the real standalone scan. The input is the
public return of the deployed raw writer before it tests the stated eligibility. -/
theorem CandidateSite.of_checked_scan (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (profile : List Bool) (claims : List (List Bool)) (pad : ℕ)
    (preRegs : Bank w) (preMem : Memory w) (used charged : ℕ)
    (origin : (pub 0).val=frame) (space : f.Fits w (pub 0).val) {allowed : Prop}
    (valid : declarationInRange word) (eligible : allowed)
    (returned : ∃ (epoch : Returns epochPlacement pub mac reg mem)
      (published : Returns Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2) (mid : Memory w)
      (scan : Returns (.seq PrivatePlacement.program Directory.ISA.program) pub mac preRegs preMem),
      let l := LabelIndex.layout frame (readings scan.val.2.2)
      epoch.val.2.2=mid ∧ published.val.2.2=Directory.ISA.publish mid (pub 0).val base (D.directory pp lp) ∧
      epoch.val.1.flatMap TeamRAM.Event.choices=[] ∧
      used+traceCost epoch.val.1+traceCost published.val.1≤charged+deliveryScanTicks D.entries D.teams D.sites ∧
      scan.val.2=published.val.2 ∧ traceCost scan.val.1≤deliveryScanTicks D.entries D.teams D.sites ∧
      ProfileRouteInputs fields f pub guess published.val.2.2 ∧ fields.header.length=(pub 0).val ∧
      (∀ count,TablePointers (ar.table frame count) (readings published.val.2.2)) ∧
      Nonempty (SlottedWriter ar D pp lp pins pub mid base host key sizes) ∧
      PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=mid) (base:=base)
        f old fresh gates outputs width off ell controls profile claims pad word R X ∧
      PublishedRowPlacement N cell recv amount (pub 0).val scan.val.2.2 ∧
      (declarationInRange word → allowed → Nonempty (HeaderWriterReceipt ar D pp lp owner decl group pins f pub mac
        scan.val.2.1 scan.val.2.2)) ∧
      l.cells=ar.cells ∧ l.cableCount=ar.cables ∧ l.deliveryCount=(D.directory pp lp).length ∧ l.labels=ar.alphabet) :
    ∃ site : Site₀, site.OnReturn old fresh gates outputs width off ell controls profile claims pad preRegs preMem used charged := by
  obtain ⟨e,p,mid,scan,first,last,empty,paid,same,scanCost,source,len,points,⟨placement⟩,raw,rows,make,dims⟩ := returned
  obtain ⟨W⟩ := make valid eligible
  have image := congrArg Prod.snd same
  rw [image] at rows dims
  rw [same] at W
  exact ⟨{ epoch := e
           published := p
           middle := mid
           epochMemory := first
           actual := last
           empty := empty
           used := used
           profileCost := charged
           cost := paid
           origin := origin
           sources := source
           fieldLength := len
           pointers := points
           space := space
           placement := placement
           old := old
           fresh := fresh
           gates := gates
           outputs := outputs
           width := width
           off := off
           ell := ell
           control := controls
           profile := profile
           claims := claims
           pad := pad
           input := raw
           rows := rows
           geometryRegs := preRegs
           geometry := preMem
           scan := scan
           scanState := same
           scanCost := scanCost
           dimensions := dims
           receipt := W }, ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
