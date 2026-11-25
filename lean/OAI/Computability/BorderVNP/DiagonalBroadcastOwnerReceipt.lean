import OAI.Computability.BorderVNP.DiagonalBroadcastPreparationRestore
import OAI.Computability.BorderVNP.DiagonalAllBroadcastReadback
import OAI.Computability.BorderVNP.DiagonalSourceOwnedVisit

/-! # The chronological owner receipt on the inverse complete broadcast -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge) (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (S : SourceReports ar owners)
    (L : RawBroadcast ar → WireLayout (R+1) r link) (fixed : Block (R+1)) (header : RawBroadcast ar → List Bool)
    (pin : Fin d → Bool)

variable (pub : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Arg → Word w)
    (mac : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Bank w) (mem : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Memory w)

variable (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c : RawBroadcast ar, BroadcastPreparations ar id L header pub mac reg mem c → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (L c.val) ar (decodedBroadcast ar c.val)
      (header c.val) pin (pub c.val) (mac c.val) (reg c.val) (mem c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))

local notation3 (prettyPrint := false) "joint" => allBroadcastPreparedEquiv G ar owners id S L fixed header pin
  pub mac reg mem allowed checked honest frames builders source

local notation "AllPreps" => Σ c : RawBroadcast ar, BroadcastPreparations ar id L header pub mac reg mem c

/-- The route, installed constants, and owned return in one restored physical preparation. -/
noncomputable def broadcastVisitWords (full : AllPreps) (u : Fin (R+1)) :=
  let v := (visitsEquiv id (pub full.1 full.2.1 u) (mac full.1 full.2.1 u) (reg full.1 full.2.1 u)
    (mem full.1 full.2.1 u)).symm (full.2.2 u)
  (v.routing.val, v.constants.val, v.owned.val)

/-- Joint scanner events in the seven real preparations associated to this broadcast. -/
noncomputable def broadcastOwnedHistory (full : AllPreps) :=
  let v := fun u => (visitsEquiv id (pub full.1 full.2.1 u) (mac full.1 full.2.1 u)
    (reg full.1 full.2.1 u) (mem full.1 full.2.1 u)).symm (full.2.2 u)
  ownedHistory ar (pub full.1 full.2.1) (mac full.1 full.2.1) (fun u => (v u).constants.val.2.1)
    (fun u => (v u).constants.val.2.2) (fun u => (v u).owned)

section
variable (c : RawBroadcast ar)
    (F : PreparationFrame G (L c) ar (decodedBroadcast ar c) (header c) pin (pub c) (mac c) (reg c) (mem c))
    (B : F.Builders fixed id owners) (agreement : F.SourceAgreement fixed S B)
    (dcl : {v : Declared ar owners (decodedBroadcast ar c) // S.pins v.val}) (rows : S.actual dcl.val.val)

private theorem source_broadcast_visits (u : Fin (R+1)) :
    let z := F.replay fixed (declaredWords ar owners (decodedBroadcast ar c) dcl.val)
    let b := B (declaredWords ar owners (decodedBroadcast ar c) dcl.val)
    broadcastVisitWords ar id L header pub mac reg mem
        ⟨c,(F.sourceEquiv fixed S B agreement).symm ⟨dcl,rows⟩⟩ u =
      ((z.2 u).val,(b.constants u).val,(b.owned.symm ⟨dcl.val.val,dcl.val.property,rfl⟩ u).val) :=
  F.sourceEquiv_native_visits fixed S B agreement dcl rows u

private theorem source_broadcast_owned :
    let z := F.replay fixed (declaredWords ar owners (decodedBroadcast ar c) dcl.val)
    let b := B (declaredWords ar owners (decodedBroadcast ar c) dcl.val)
    broadcastOwnedHistory ar id L header pub mac reg mem
        ⟨c,(F.sourceEquiv fixed S B agreement).symm ⟨dcl,rows⟩⟩ =
      ownedHistory ar (pub c z.1) (mac c z.1) (fun u => (b.constants u).val.2.1)
        (fun u => (b.constants u).val.2.2) (b.owned.symm ⟨dcl.val.val,dcl.val.property,rfl⟩) :=
  F.sourceEquiv_owned_history fixed S B agreement dcl rows

end

/-- The inverse of the physical cube-header quotient returns the exact
routed wires, constant installation, and complete owned trace at every
team. These reads precede the subsequent independent report guesses. -/
theorem allBroadcastPreparedEquiv_nativeVisits
    (q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v}) (reports : S.actual q.val)
    (u : Fin (R+1)) :
    let c := routeBroadcast ar owners q.val
    let f := frames c (honest q.val)
    let raw := declaredWords ar owners (decodedBroadcast ar c.val) ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩
    let z := f.replay fixed raw
    let B := builders c (honest q.val) raw
    let physical := B.owned.symm ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm,rfl⟩
    broadcastVisitWords ar id L header pub mac reg mem ((joint).symm ⟨q,reports⟩) u =
      ((z.2 u).val,(B.constants u).val,(physical u).val) := by
  intro c f raw z B physical
  have step := congrArg (fun e => broadcastVisitWords ar id L header pub mac reg mem e u) (allBroadcastPreparedEquiv_restored
    G ar owners id S L fixed header pin pub mac reg mem allowed checked honest frames builders source q reports)
  refine step.trans ?_
  have observed := source_broadcast_visits G ar owners id S L fixed header pin pub mac reg mem c.val f
    (builders c (honest q.val)) (source c (honest q.val))
    ⟨⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩,q.property⟩ reports u
  with_reducible exact observed

/-- The full original ownership history at this returned broadcast can be used
directly wherever the delivered physical scanner receipt is required. -/
theorem allBroadcastPreparedEquiv_ownedHistory
    (q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v}) (reports : S.actual q.val) :
    let c := routeBroadcast ar owners q.val
    let f := frames c (honest q.val)
    let raw := declaredWords ar owners (decodedBroadcast ar c.val) ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩
    let z := f.replay fixed raw
    let B := builders c (honest q.val) raw
    let physical := B.owned.symm ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm,rfl⟩
    broadcastOwnedHistory ar id L header pub mac reg mem ((joint).symm ⟨q,reports⟩) =
      ownedHistory ar (pub c.val z.1) (mac c.val z.1) (fun u => (B.constants u).val.2.1)
        (fun u => (B.constants u).val.2.2) physical := by
  intro c f raw z B physical
  have step := congrArg (broadcastOwnedHistory ar id L header pub mac reg mem) (allBroadcastPreparedEquiv_restored
    G ar owners id S L fixed header pin pub mac reg mem allowed checked honest frames builders source q reports)
  refine step.trans ?_
  have observed := source_broadcast_owned G ar owners id S L fixed header pin pub mac reg mem c.val f
    (builders c (honest q.val)) (source c (honest q.val))
    ⟨⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩,q.property⟩ reports
  with_reducible exact observed

end TeamContraction

end BorderVNP
end Computability
end OAI
