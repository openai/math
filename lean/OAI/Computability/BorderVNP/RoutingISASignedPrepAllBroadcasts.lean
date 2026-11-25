import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows

/-! # Elimination of every raw cube broadcast in the actual joint pre-call program -/

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


/-- The joint physical preparations at the particular bit string for this
candidate's cube rows, including every possible exterior with that prefix. -/
abbrev BroadcastPreparations (c : RawBroadcast ar) :=
  Σ x : HeaderExterior (L c) (header c), (u : Fin (R+1)) →
    Returns (prepareExpansion epochPlacement (scheduleGroups ar.n (selectorWidth ar.n ar.K ar.h))
      (signedInputs id (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s))) (pub c x u) (mac c x u) (reg c x u) (mem c x u)

local notation "Ret" => BroadcastPreparations ar id L header pub mac reg mem

/-- At fixed row pins, profile and subtotal claim, eliminate the entire raw
broadcast, exterior and native preparation. The only resulting indices are a
true pinned routed assignment and its own immutable, per-team source report
slots. Out-of-range, nonminimal and overloaded native candidates contribute no
histories. Every genuine routed assignment uses its unique truthful broadcast. -/
noncomputable def allBroadcastPreparedEquiv
    (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c, Ret c → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (L c.val) ar (decodedBroadcast ar c.val)
      (header c.val) pin (pub c.val) (mac c.val) (reg c.val) (mem c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a)) :
    (Σ c : RawBroadcast ar, Ret c) ≃ Σ q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v},
      S.actual q.val := by
  let Good := {c : CheckedBroadcast ar // allowed c.val}
  let check : (Σ c : RawBroadcast ar, Ret c) ≃ (Σ c : Good, Ret c.val.val) :=
    { toFun := fun z => ⟨⟨⟨z.1,(checked z.1 z.2).1⟩,(checked z.1 z.2).2⟩,z.2⟩
      invFun := fun z => ⟨z.1.val.val,z.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let cuts (c : Good) := (frames c.val c.property).sourceEquiv fixed S
    (builders c.val c.property) (source c.val c.property)
  let collapse :
      (Σ c : Good, Σ v : {q : Declared ar owners (decodedBroadcast ar c.val.val) // S.pins q.val},
        S.actual v.val.val) ≃ Σ q : {v : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners // S.pins v}, S.actual q.val :=
    { toFun := fun z => ⟨⟨z.2.1.val.val,z.2.1.property⟩,z.2.2⟩
      invFun := fun z => ⟨⟨routeBroadcast ar owners z.1.val,honest z.1.val⟩,
        ⟨⟨z.1.val,(decoded_routeBroadcast ar owners z.1.val).symm⟩,z.1.property⟩,z.2⟩
      left_inv := by
        rintro ⟨⟨c,hc⟩,⟨⟨q,shape⟩,pins⟩,reports⟩
        obtain rfl := (declared_iff_routeBroadcast ar owners c q).mp shape
        rfl
      right_inv := fun _ => rfl }
  exact check.trans ((Equiv.sigmaCongrRight cuts).trans collapse)

end TeamContraction

end BorderVNP
end Computability
end OAI
