import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedSources

/-! # The actual field value returned by one owned public assignment

On a passing endpoint pin check, each returned physical report history
recovers its preceding typed RAM. Its logical packet data determine the
corresponding field summand. Summing over all matrices gives the checked
public team value, including reports and cube entries with value zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OwnedContinuation

open Crossing Packing Packing.Inherited FiniteDiagonal BorderVNP.Cube Cube.Physical
open VPVNP.BurstRAM RoutingISA CellPacket.Supplement
open scoped BigOperators Classical

set_option synthInstance.maxSize 4096
set_option maxRecDepth 6000
set_option maxHeartbeats 1800000

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (routed : V.Raw R) (bank : Ports bits) (z : V.Public R) (u : Fin (R+1))
  (header profile cells cables maxRows stride : ℕ)
  (entry : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F) (params : SignedTaskArena.Parameters)
  (codec : Cells.Codec) (pub : Arg → Word w) (regs : Bank w) (mem : Memory w)
  (length ticks burst clock : ℕ)

local notation "Y" => V.signedInputs R routed u header profile cells cables maxRows stride entry params
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock length
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel

/-- Actual source rows, native readback and measured private and team clocks
at the returned signed allocator. The packet hypotheses are on the concrete
middle memory and the physical report tape consumed at this endpoint. -/
structure Physical where
  /-- The authenticated opening and task tables before the report choices. -/
  opening : Opening pub mem Y
  /-- Physical ordinal of each host cell assigned to this team. -/
  order : Fin opening.rows.length ≃ {c : L.Cell // V.cellOwner R z c=u}
  /-- Type of the source site identifiers in the placed packets. -/
  Orig : Type
  localSites : ∀ v, (S.site v).Local
  schemas : ∀ v, (S.site v).Schema
  relative : ∀ v, (S.site v).RelativeBoxes
  fieldCodes : S.values=FieldPowers.entry (Fintype.equivFin F).symm
  locality : ∀ i, (Merged.rowSite V R z u opening.rows order i).Local
  range : ∀ i, let site := Merged.rowSite V R z u opening.rows order i
    ∀ (g : Fin site.work → Bool) obs, site.observe (Inherited.bits g (Merged.rowInput V R bank z u opening.rows order i))=some obs →
      ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F
  fit : ∀ i, let site := Merged.rowSite V R z u opening.rows order i
    ∀ (g : Fin site.work → Bool) obs, site.observe (Inherited.bits g (Merged.rowInput V R bank z u opening.rows order i))=some obs →
      (obs.filterMap Prod.snd).length < 2^opening.report.digits
  openingTime : opening.stage.cost (pub 0).val (readings mem) ≤ ticks
  wide : 2*Fintype.card F<w
  privateRoom : 2*Fintype.card F<fuel
  oneWord : 1 ≤ TeamScales.width length (1/2)
  wordCap : TeamScales.width length (1/2) ≤ burst
  choiceCap : length^25 ≤ clock
  sources : ∀ opened : Evaluator.Returns OpenSuffix.code pub mac regs mem,
    readings opened.val.2.2=opening.stage.image (pub 0).val (readings mem) →
    ∀ (c : TaskReadback.Matrices F opening.report.digits opening.rows)
      (out : Evaluator.Returns prepareTasks pub mac opened.val.2.1 opened.val.2.2),
    let observed := Reports.rebit opening.rows (out.val.1.flatMap TeamRAM.Event.choices)
    let raw := Reports.image opening.report observed (readings opened.val.2.2)
    (∀ i : Fin opening.rows.length, (observed[i.val]'(by simp [observed])).bits=FiniteScalarRounds.stream F (c i)) →
    ∀ middle : Memory w, readings middle=opening.tasks.published raw → out.val.2.2=Batch.written middle opening.supp opening.count →
    ∃ (X : Cells.Inputs F) (owned : ℕ → Batch.Owned Orig),
      PacketSources V R bank z u opening order codec raw c X owned out.val.2.2 length ∧
      traceCost opened.val.1+traceCost out.val.1+X.validatorCost pub out.val.2.2+X.scalarCost+(Y).cost ≤ ticks

variable {V R routed bank z u header profile cells cables maxRows stride entry params codec pub regs mem length ticks burst clock}

/-- Exact bounded field contribution of this passing team. The proof uses
only the native return history, the actual report sources and measured clocks. -/
theorem Physical.passing_public
    (H : Physical V R routed bank z u header profile cells cables maxRows stride entry params codec pub regs mem length ticks burst clock)
    (fixed : ∀ p, L.table p=entry) (decoded : V.readPublic R z=routed.1) (original : CubePacket.Prepared Y pub mem)
    (pad : (Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem)) :
    boundedWeight pub lib ret fuel code regs mem ticks burst clock=V.ownedPublicValue R entry bank z u := by
  let A := H.opening
  obtain ⟨opened,E,image,bits,calcValue⟩ := passing_factors_for pub length regs mem A.stage A.ready A.arena A.reserved A.deckEnd Y
    original A.report A.rows A.tasks A.supp A.count A.controls A.openPlace A.writePlace A.gap A.source A.scalarCount codec
    ticks burst clock pad H.openingTime H.wide H.privateRoom H.oneWord H.wordCap H.choiceCap
  have held := original.transfer Y (OpenSuffix.placed_words A.stage A.arena A.reserved A.deckEnd Y A.ready A.openPlace opened.property
    A.writePlace.ordered.1 A.writePlace.ordered.2.2.2 A.gap A.writePlace.operands)
  let raw (c) := Reports.image A.report (Reports.rebit A.rows ((E c).val.1.flatMap TeamRAM.Event.choices)) (readings opened.val.2.2)
  have middle (c) := TaskReadback.return_image pub mac Y A.report A.rows A.tasks A.supp A.count A.controls
    opened.val.2.1 opened.val.2.2 (A.source _ image) A.writePlace held (E c)
  choose mid published splice using middle
  have receipt (c) := H.sources opened image c (E c) (bits c) (mid c) (published c) (splice c)
  choose X owned hX time using receipt
  have native := calcValue X fun c => ⟨(hX c).prepared,(hX c).cube,time c⟩
  have scores (c) := (hX c).host_rows V R bank z u A H.order codec (raw c) c (X c) (owned c) (published c) (splice c)
  have host := Merged.owned_validators V R bank z u A.report.digits A.rows H.order H.localSites H.schemas H.relative H.fieldCodes
    H.locality H.range H.fit
  refine native.trans ?_
  rw [V.ownedPublicValue_signed R routed u header profile cells cables maxRows stride entry params fixed bank z decoded]
  apply congrArg (· * ∏ i,(Y).scalar i)
  exact (Finset.sum_congr rfl fun c _ => scores c).trans (by simpa only [← decoded] using host)

end FiniteEvaluator.OwnedContinuation

end BorderVNP
end Computability
end OAI
