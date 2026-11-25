import OAI.Computability.BorderVNP.DiagonalSourceLookupWords
import OAI.Computability.BorderVNP.DiagonalSignedCandidateSiteSelection
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderWriters
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderRoom

/-! # The signed lookup and actual copied subtotal at the declared candidate writer -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace RoutingISA.SignedTaskArena
open VPVNP.BurstRAM TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader Packing
open PackedHistoryCircuit RoutingISA.LocalRow

/-- The published boot fields and copied header suffice for the subtotal reader at
this memory. They need no copy of unrelated bootstrap registers. -/
theorem headerSeed_ofPublishedPins {w reserve axes groups cap width : ℕ} (l : Layout)
    (p : PositiveFields reserve axes groups cap l.cube.teams l.dim width) (pub : Arg → Word w)
    (raw team : ℕ) (old : Fin 81 → Word w) (D : Directory.Layout)
    (origin edges cells fresh profile gates outputs geomWidth off ell : ℕ) {f : BroadcastFrame} {mem : Memory w}
    (rawAt : raw=f.dst+1+reserve+Cube.DeclarationBits.length axes groups cap)
    (boot : BootPins pub f (signedProfileExtension l old D origin edges cells raw team width fresh profile gates
      outputs geomWidth off ell) p.bits mem)
    (dimFit : l.dim<2^w) (localFit : l.after.localBase<2^w) (rawFit : raw<2^w)
    (teamsFit : l.cube.teams<2^w) (member : team<l.cube.teams) (widthFit : width ≤ w) (wpos : 0<w) :
    HeaderSeed l p pub raw team mem := by
  let previous := fun k => (l.cube.extension old ⟨min (k-31) 80,by omega⟩).val
  have atField (i : Fin 81) (h : i.val+31 ∈ [33,34,35,36,38,39,40,44,45,46,71,80,89,90,95])
      (fit : l.reportFields raw team width previous (31+i.val)<2^w) :
      (mem ((pub 0).val+(31+i.val))).val=l.reportFields raw team width previous (31+i.val) := by
    rw [←Nat.add_assoc,boot.extension]
    exact signedProfileExtension_report l old D origin edges cells raw team width fresh profile gates outputs geomWidth off ell i h fit
  have machine : (mem ((pub 0).val+101)).val=w := by
    change (mem ((pub 0).val+31+(70 : Fin 81).val)).val=w
    rw [boot.extension,signedProfileExtension_geometry]
    exact Nat.mod_eq_of_lt Nat.lt_two_pow_self
  have addr : l.after.descriptors < 2^w := by
    apply lt_of_le_of_lt _ localFit
    unfold DiagonalTallyAllocation.AfterTasks.localBase DiagonalTallyAllocation.AfterTasks.fresh
    omega
  refine ⟨⟨⟨atField 2 (by decide) dimFit,atField 3 (by decide) localFit⟩,
    ⟨atField 5 (by decide) rawFit,atField 7 (by decide) teamsFit,atField 8 (by decide) (member.trans teamsFit),
      atField 9 (by decide) (widthFit.trans_lt Nat.lt_two_pow_self)⟩,⟨atField 13 (by decide) addr,machine⟩⟩,?_,?_⟩
  · exact atField 64 (by decide) ((Nat.le_add_right l.p.parameters l.p.report.gadgets).trans_lt dimFit)
  · exact rawAt ▸ (p.copied wpos boot.copy).2.2

end RoutingISA.SignedTaskArena

namespace RoutingISA.Evaluator.SignedPrep
open VPVNP.BurstRAM TeamContraction JointHeader ProcessorSlots Packing BorderVNP.Cube Physical LocalRow
open PackedHistoryCircuit Crossing SignedTaskArena DiagonalTallyPacketEmit Transmission

variable {w R X : ℕ} (sa : SignedTaskArena.Layout) {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {word : Broadcast sa.cube.n sa.cube.header.d sa.cube.header.cap} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration sa.cube.n sa.cube.header.d} {group : Fin sa.cube.header.d → Fin (R+1)}
    {frame base : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin sa.cube.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {d : ℕ} {P A : Type*} {bits : P → ℕ} {N : Network d P bits} {cell : N.Site → Fin sa.cube.cells}
    {recv : A → Fin sa.cube.cells} {amount : A → ℕ}


local notation3 (prettyPrint := false) "Site₀" => CandidateSite (X:=X) sa.cube D pp lp word owner decl group
  frame base pins fields f guess pub mac reg mem host key sizes N cell recv amount

set_option maxHeartbeats 900000
set_option maxRecDepth 6500

/-- Every count uses the descriptor, ID destination and fixed lookup dimensions
of this candidate site's own signed packet and returned writer. -/
theorem CandidateSite.sharedLookup (site : Site₀) (previous : Fin 81 → Word w)
    (origin raw team subtotal visits : ℕ)
    (installed : site.old=routingExtension (sa.extension raw team subtotal previous) D origin sa.cube.cables sa.cube.cells)
    (room : sa.after.packed ≤ 2^w) :
    LookupPointers (sa.lookupFrame visits) sa.after.ids (pub 0).val (readings site.receipt.history.sharedInput) := by
  have loaded := site.input.boot
  rw [←site.actual,installed] at loaded
  exact site.receipt.done.signed_lookup sa site.receipt.history previous origin sa.cube.cables sa.cube.cells
    raw team subtotal site.fresh site.profile.length site.gates site.outputs site.width site.off site.ell visits
    loaded room site.input.frameSpace

/-- The selected candidate's real published claims survive the signed scheduler
and its data writer, on the same shared RAM used by the native lookup. -/
theorem CandidateSite.sharedHeaderSeed (site : Site₀) (A₀ : StartupArena)
    {res side blocks cap width : ℕ} (p : PositiveFields res side blocks cap sa.cube.teams sa.dim width)
    (previous : Fin 81 → Word w) (origin team : ℕ)
    (installed : site.old=routingExtension (sa.extension (rawAddress A₀ res side blocks cap) team width previous)
      D origin sa.cube.cables sa.cube.cells)
    (header : padded (spelling (site.profile++DeclarationBits.spelling word) site.claims) site.pad=p.bits)
    (head : (pub 0).val=A₀.frame) (dest : f.dst=A₀.broadcastBase)
    (size : A₀.header=PositiveFields.width res side blocks cap sa.cube.teams sa.dim width)
    (secondary : A₀.next ≤ sa.cube.header.header) {query guesses gates : ℕ}
    (endFit : sa.endAddress w query guesses gates<2^w)
    (teamsFit : sa.cube.teams<2^w) (member : team<sa.cube.teams) (widthFit : width≤w) (wordPos : 0<w) :
    HeaderSeed sa p pub (rawAddress A₀ res side blocks cap) team site.receipt.history.sharedInput := by
  have loaded := site.input.boot
  rw [←site.actual,installed,header] at loaded
  obtain ⟨_,_,_,_,dimFit,localFit,rawFit⟩ := finishSeedRoom sa A₀ size secondary endFit
  have seed := headerSeed_ofPublishedPins sa p pub (rawAddress A₀ res side blocks cap) team previous D
    origin sa.cube.cables sa.cube.cells site.fresh site.profile.length site.gates site.outputs site.width
    site.off site.ell (by rw [dest]; rfl) loaded dimFit localFit rawFit teamsFit member widthFit wordPos
  exact HeaderSeed.sharedInput sa A₀ p team head size site.receipt.history site.receipt.done seed secondary

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
