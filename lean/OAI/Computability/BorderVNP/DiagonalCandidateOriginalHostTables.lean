import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection

/-! # Host-source arguments on a returned processor's own published directory -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

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

private theorem receipt_at_published {m m' : Memory w} {s : Bank w}
    (receipt : HeaderWriterReceipt ar D pp lp owner decl group pins f pub mac s m)
    (same : m=m') :
    ∃ issued : HeaderWriterReceipt ar D pp lp owner decl group pins f pub mac s m',
      issued.history.sharedInput=receipt.history.sharedInput := by
  subst m'
  exact ⟨receipt,rfl⟩

/-- On an attained site, the processor's source, slotted writer, raw header
input and issued writer all use its own native publication. The receipt at
that memory retains the complete shared input of the original writer. -/
theorem CandidateSite.onReturnHostInputs
    (site : CandidateSite (X:=X) ar D pp lp word owner decl group frame base pins fields f guess
      pub mac reg mem host key sizes N cell recv amount)
    {old : Fin 81 → Word w} {fresh gates outputs width off ell controls : ℕ}
    {profile : List Bool} {claims : List (List Bool)} {padding : ℕ}
    {preRegs : Bank w} {preMem : Memory w} {used charged : ℕ}
    (attained : site.OnReturn old fresh gates outputs width off ell controls profile claims padding
      preRegs preMem used charged) :
    let published := Directory.ISA.publish site.middle (pub 0).val base (D.directory pp lp)
    ProfileRouteInputs fields f pub guess published ∧
      Nonempty (SlottedWriter ar D pp lp pins pub site.middle base host key sizes) ∧
      PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=site.middle) (base:=base)
        f old fresh gates outputs width off ell controls profile claims padding word R X ∧
      site.published.val.2.2=published ∧
      ∃ issued : HeaderWriterReceipt ar D pp lp owner decl group pins f pub mac site.published.val.2.1 published,
        issued.history.sharedInput=site.receipt.history.sharedInput := by
  intro published
  have raw := site.input
  rw [attained.oldWords,attained.first,attained.gateCount,attained.outputCount,attained.fieldWidth,attained.stripeOffset,
    attained.stripeLength,attained.controlBase,attained.copiedProfile,attained.copiedClaims,attained.padding] at raw
  have source := site.sources
  rw [site.actual] at source
  exact ⟨source,⟨site.placement⟩,raw,site.actual,receipt_at_published site.receipt site.actual⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
