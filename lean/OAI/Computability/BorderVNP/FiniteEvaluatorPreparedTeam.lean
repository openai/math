import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedPublic
import OAI.Computability.BorderVNP.FiniteEvaluatorCodecWitness

/-! # Checked public values after an actual physical task preparation

The supplied preparation can include stable fragment bucketing and sparse
exterior emission. The numerical proof uses the frame, call owners, logical
cell inputs and field reports of the RAM actually returned by that program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OwnedContinuation

open Crossing Packing Packing.Inherited FiniteDiagonal BorderVNP.Cube Cube.Physical
open VPVNP.BurstRAM RoutingISA TeamContraction
open scoped BigOperators Classical

set_option synthInstance.maxSize 4096
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

variable {D w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (routed : V.Raw R) (bank : Ports bits) (z : V.Public R) (u : Fin (R+1))
  (header profile cells cables maxRows stride : ℕ)
  (entry : TableEntry L.dimension L.bitWidth L.copies L.alternatives L.supply → F) (params : SignedTaskArena.Parameters)
  (codec : Cells.Codec) (prep : Code) (pub : Arg → Word w) (regs : Bank w) (mem : Memory w)
  (length ticks burst clock : ℕ)

local notation "Y" => V.signedInputs R routed u header profile cells cables maxRows stride entry params
local notation "lib" => Cells.library F codec
local notation "ret" => Cells.terminals F codec
local notation "fuel" => CompactMachine.nativeClock length
local notation "mac" => TeamSiteEvents.macros (w:=w) lib fuel

/-- Physical report chronology and the decoded operands at a team's actual
returned preparation, including its separate private, burst and outer clocks. -/
structure PreparedTeam where
  /-- The physical pin tests, cell copies and bundle-control writer. -/
  stage : OpenSuffix.Inputs
  ready : OpenSuffix.Ready stage (pub 0).val (readings mem) w
  /-- Owned report rows in native visit order. -/
  rows : List Reports.Row
  /-- Number of binary digits in each reported field-element count. -/
  digits : ℕ
  /-- Physical ordinal of each host cell assigned to this team. -/
  order : Fin rows.length ≃ {c : L.Cell // V.cellOwner R z c=u}
  localSites : ∀ v, (S.site v).Local
  schemas : ∀ v, (S.site v).Schema
  relative : ∀ v, (S.site v).RelativeBoxes
  fieldCodes : S.values=FieldPowers.entry (Fintype.equivFin F).symm
  locality : ∀ i, (Merged.rowSite V R z u rows order i).Local
  range : ∀ i, let site := Merged.rowSite V R z u rows order i
    ∀ (g : Fin site.work → Bool) obs, site.observe (Inherited.bits g (Merged.rowInput V R bank z u rows order i))=some obs →
      ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F
  fit : ∀ i, let site := Merged.rowSite V R z u rows order i
    ∀ (g : Fin site.work → Bool) obs, site.observe (Inherited.bits g (Merged.rowInput V R bank z u rows order i))=some obs →
      (obs.filterMap Prod.snd).length < 2^digits
  openingTime : stage.cost (pub 0).val (readings mem) ≤ ticks
  native : prep.nativeOnly=true
  wide : 2*Fintype.card F<w
  privateRoom : 2*Fintype.card F<fuel
  oneWord : 1 ≤ TeamScales.width length (1/2)
  wordCap : TeamScales.width length (1/2) ≤ burst
  choiceCap : length^25 ≤ clock
  reports : ∀ opened : Evaluator.Returns OpenSuffix.code pub mac regs mem,
    readings opened.val.2.2=stage.image (pub 0).val (readings mem) → CubePacket.Prepared Y pub mem →
    ∃ E : TaskReadback.Matrices F digits rows ≃ Evaluator.Returns prep pub mac opened.val.2.1 opened.val.2.2,
    ∀ c, let out := E c
      (∀ i : Fin rows.length, ((Reports.rebit rows (out.val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits =
        FiniteScalarRounds.stream F (c i)) ∧
      ∃ (X : Cells.Inputs F) (fields : ℕ → SparseExterior.Field), Cells.Prepared X pub out.val.2.2 length (codec.withFields fields) ∧ CubePacket.Prepared Y pub out.val.2.2 ∧
        CubePacket.Sources Y X.layout ∧ Merged.RowInputs V R bank z u digits rows order X c ∧
        CellDispatch.Frame.ofMemory pub out.val.2.2=⟨X.layout.team,X.layout.calls,X.layout.cells⟩ ∧
        (∀ i < X.layout.cells, (out.val.2.2 (X.layout.call i)).val=X.layout.owner X.publicMem i) ∧
        traceCost opened.val.1+traceCost out.val.1+X.validatorCost pub out.val.2.2+X.scalarCost+(Y).cost ≤ ticks

variable {V R routed bank z u header profile cells cables maxRows stride entry params codec prep pub regs mem length ticks burst clock}

/-- The field contribution of the actual preparation and both native private
routines at a passing routed team equals its checked public factor. -/
theorem PreparedTeam.passing_public
    (H : PreparedTeam V R routed bank z u header profile cells cables maxRows stride entry params codec prep pub regs mem length ticks burst clock)
    (fixed : ∀ p, L.table p=entry) (decoded : V.readPublic R z=routed.1) (original : CubePacket.Prepared Y pub mem)
    (pad : (Padding.Layout.fromFrame (pub 0).val (readings mem)).Valid (readings mem)) :
    boundedWeight pub lib ret fuel (codeFor prep) regs mem ticks burst clock=V.ownedPublicValue R entry bank z u := by
  obtain ⟨opened,image,_,after⟩ := passing_stage (F:=F) pub length regs mem codec prep H.stage H.ready ticks burst clock pad H.openingTime
  obtain ⟨E,receipt⟩ := H.reports opened image original
  choose X fields prepared held loc rowInputs frame owner costs using fun c => (receipt c).2
  let Bnd := Evaluator.BoundedReturns prep pub mac opened.val.2.1 opened.val.2.2 (ticks-traceCost opened.val.1) burst clock
  let := Fintype.ofFinite Bnd
  have clockOne : 1 ≤ clock := by
    have nonzero : length≠0 := by
      intro h
      have one := H.oneWord
      rw [h] at one
      norm_num [TeamScales.width,Real.zero_rpow] at one
    exact (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero nonzero)).trans H.choiceCap
  have within c : Within (ticks-traceCost opened.val.1) burst clock (E c).val.1 :=
    ((E c).property.nativeOnly_limits H.native).mono (by have := costs c; omega) (Nat.zero_le _) clockOne
  let real : TaskReadback.Matrices F H.digits H.rows ≃ Bnd := E.trans
    ⟨fun out => ⟨out,by simpa only [Equiv.apply_symm_apply] using within (E.symm out)⟩,
      Subtype.val,fun _ => rfl,fun _ => rfl⟩
  have scored (c) := Merged.hostFactor_rowScore_memory V R bank z u H.digits H.rows H.order (X c) c (rowInputs c)
    pub (E c).val.2.2 (frame c) (owner c)
  have native c : weight pub lib ret fuel prep opened.val.2.1 (E c).val.1 *
      boundedWeight pub lib ret fuel privateReturns (E c).val.2.1 (E c).val.2.2
        (ticks-traceCost opened.val.1-traceCost (E c).val.1) burst clock =
        (∏ i, Merged.rowScore V R bank z u H.digits H.rows H.order i (c i)) * ∏ i,(Y).scalar i := by
    rw [weight_native pub lib ret fuel (E c).property H.native,one_mul,← scored c]
    refine (codec.bounded_withFields (F:=F) (fields c) pub fuel privateReturns (E c).val.2.1 (E c).val.2.2
      (ticks-traceCost opened.val.1-traceCost (E c).val.1) burst clock).symm.trans ?_
    exact CellsCube.bounded_prepared_for (X c) Y pub (codec.withFields (fields c)) (E c).val.2.1 (E c).val.2.2 length _ _ _ (prepared c)
      (CubePacket.Prepared.post (X c) (prepared c) Y (held c) (loc c)) H.wide H.privateRoom H.oneWord
      (by have := costs c; omega) H.wordCap H.choiceCap
  have host := Merged.owned_validators V R bank z u H.digits H.rows H.order H.localSites H.schemas H.relative H.fieldCodes
    H.locality H.range H.fit
  let hostValue (q : Cube.Physical.NativeAssignments.Routed (b:=L.bitWidth) (s:=L.supply) (V.owners R)) :=
    ∏ c : {c : L.Cell // V.cellOwner R z c=u}, ∑ g, S.rawCell L V.siteID (V.owners R) bank q c.val g
  have counted : (∑ c : TaskReadback.Matrices F H.digits H.rows,
    ∏ i, Merged.rowScore V R bank z u H.digits H.rows H.order i (c i))=hostValue routed.1 :=
    host.trans (congrArg hostValue decoded)
  refine Eq.trans ?_ (V.ownedPublicValue_signed R routed u header profile cells cables maxRows stride entry params fixed bank z decoded).symm
  refine Eq.trans ?_ (congrArg (· * ∏ i,(Y).scalar i) counted)
  rw [after,boundedWeight_seq,← real.sum_comp,Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => native c

end FiniteEvaluator.OwnedContinuation

end BorderVNP
end Computability
end OAI
