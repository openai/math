import OAI.Computability.BorderVNP.DiagonalSourceOwnedVisit
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

/-! # Identifying the physically recovered ownership receipt at the exact source route -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep.DeliveredBuilder

open VPVNP.BurstRAM BorderVNP.Cube Physical Scatter Scatter.Assignment TeamContraction
open private native_injective from OAI.Computability.BorderVNP.CubeScatterTransmissionRouted

variable {R w : ℕ} {ar : CubeArena.Layout}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {raw : Symbols ar.header.d → List Bool}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ} {pub : Fin (R+1) → Arg → Word w}
    {mac : Fin (R+1) → TeamOpcode.Macros w 8} {reg : Fin (R+1) → Bank w} {mem : Fin (R+1) → Memory w}
    (B : DeliveredBuilder ar owners decl raw id pub mac reg mem)
    (z : OwnedRuns ar pub mac (fun u => (B.constants u).val.2.1) (fun u => (B.constants u).val.2.2))
    {group : Fin ar.header.d → Fin (R+1)}

local notation3 (prettyPrint := false) "family" => ownedHistory ar pub mac (fun u => (B.constants u).val.2.1)
  (fun u => (B.constants u).val.2.2) z

/-- Every physical recovery of the native ownership pass has the very selector,
common traffic and private choices returned by its builder. The proof uses
injectivity of the full routed encoding, including each team's ordered tape. -/
theorem observedReceipt (any : ∃ v, ObservedOwned ar decl group family owners raw v) :
    ObservedOwned ar decl group family owners raw (B.owned z).val := by
  obtain ⟨v,obs⟩ := any
  have native := (Routed.realizes_iff owners Fin.valEmbedding ((family).layout ar Fin.valEmbedding decl)
    (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) (fun _ => rfl) (fun _ => rfl) v _).mp obs.observed
  have same : v=(B.owned z).val := native_injective owners (native.trans (B.observes z).symm)
  exact same ▸ obs

end RoutingISA.Evaluator.SignedPrep.DeliveredBuilder

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    (S : SourceReports ar owners) (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (B : F.Builders fixed id owners)


/-- On the exact original prepared registers, the physical recovery witness
returned by the trace scanner belongs to the decoded route. No separate
identification or uniqueness premise on decoded selectors is required. -/
theorem PreparationFrame.sourceEquiv_owned_receipt (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) :
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
    let raw := declaredWords ar owners decl q.val
    let v := fun u => (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    let reached := ownedHistory ar (pub full.1) (mac full.1) (fun u => (v u).constants.val.2.1)
      (fun u => (v u).constants.val.2.2) (fun u => (v u).owned)
    (∃ v, ObservedOwned ar decl F.group reached owners raw.val v) →
      ObservedOwned ar decl F.group reached owners raw.val q.val.val := by
  intro full raw v reached
  let physical := (B raw).owned.symm ⟨q.val.val,q.val.property,rfl⟩
  have restored := F.sourceEquiv_owned_history fixed S B agree q reports
  change reached = _ at restored
  rw [restored]
  intro any
  have seen := (B raw).observedReceipt physical any
  simp only [physical,Equiv.apply_symm_apply] at seen
  exact seen

end TeamContraction

end BorderVNP
end Computability
end OAI
