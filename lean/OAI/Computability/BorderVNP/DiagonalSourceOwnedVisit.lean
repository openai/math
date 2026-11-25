import OAI.Computability.BorderVNP.DiagonalNativeRouteInverse
import OAI.Computability.BorderVNP.DiagonalOwnedVisitReconstruction

/-! # The owned scanner and actual constant installation at a decoded pinned assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

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


set_option maxHeartbeats 1600000 in
/-- The original chronological native returns reconstructed at a pinned
assignment contain the route selected by the exact exterior replay and
the complete owned scan selected by its physical selector. Every
report history above this same underlying scan has these same three stages. -/
theorem PreparationFrame.sourceEquiv_native_visits (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) (u : Fin (R+1)) :
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
    let raw := declaredWords ar owners decl q.val
    let z := F.replay fixed raw
    let physical := (B raw).owned.symm ⟨q.val.val,q.val.property,rfl⟩
    let v := (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    (v.routing.val,v.constants.val,v.owned.val) = ((z.2 u).val,((B raw).constants u).val,(physical u).val) := by
  intro full raw z physical v
  apply visits_rebuilt_observation id (F.schedule z.1 u) (F.empty z.1 u) (z.2 u) ((B raw).constants u) (physical u)

private theorem ownedHistory_eq_by_values
    {p p' : Fin (R+1) → Arg → Word w} {mac₀ mac₁ : Fin (R+1) → TeamOpcode.Macros w 8}
    {b b' : Fin (R+1) → Bank w} {m m' : Fin (R+1) → Memory w}
    (v : OwnedRuns ar p mac₀ b m) (z : OwnedRuns ar p' mac₁ b' m')
    (pubs : p=p') (macros : mac₀=mac₁) (registers : b=b') (memories : m=m')
    (runs : ∀ u, (v u).val=(z u).val) :
    ownedHistory ar p mac₀ b m v = ownedHistory ar p' mac₁ b' m' z := by
  subst p'; subst mac₁; subst b'; subst m'
  exact congrArg (ownedHistory ar p mac₀ b m) (funext fun u => Subtype.ext (runs u))

set_option maxHeartbeats 1250000 in
/-- All public arguments, initial banks, full chronological words and output
banks in the original decoded family equal those on the genuine scanner
receipt for its declared routed assignment. -/
theorem PreparationFrame.sourceEquiv_owned_history (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) :
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩
    let raw := declaredWords ar owners decl q.val
    let z := F.replay fixed raw
    let physical := (B raw).owned.symm ⟨q.val.val,q.val.property,rfl⟩
    let v := fun u => (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    ownedHistory ar (pub full.1) (mac full.1) (fun u => (v u).constants.val.2.1) (fun u => (v u).constants.val.2.2)
        (fun u => (v u).owned) =
      ownedHistory ar (pub z.1) (mac z.1) (fun u => ((B raw).constants u).val.2.1) (fun u => ((B raw).constants u).val.2.2)
        physical := by
  intro full raw z physical v
  have ext : full.1=z.1 := Subtype.ext rfl
  have seen := F.sourceEquiv_native_visits fixed S B agree q reports
  have result (u : Fin (R+1)) : (v u).constants.val=((B raw).constants u).val ∧ (v u).owned.val=(physical u).val :=
    Prod.mk.inj (Prod.mk.inj (seen u)).2
  exact ownedHistory_eq_by_values (ar:=ar) (fun u => (v u).owned) physical (congrArg pub ext) (congrArg mac ext)
    (funext fun u => congrArg (fun x => x.2.1) (result u).1)
    (funext fun u => congrArg (fun x => x.2.2) (result u).1) (fun u => (result u).2)

end TeamContraction

end BorderVNP
end Computability
end OAI
