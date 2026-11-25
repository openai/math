import OAI.Computability.BorderVNP.RoutingISASignedPrepOwnedReports

/-! # Elimination of the extra shared-row index -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment DiagonalTallyCellReports

variable {R : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (decl : LengthDeclaration ar.n ar.header.d)

/-- All shared row words at the declared physical widths. -/
abbrev SharedWords := {raw : Symbols ar.header.d → List Bool //
  ∀ p, (raw p).length=SharedRows.reserved ar.header.blocks ar.K ar.h decl p}

/-- All routed assignments selecting the declared axis and attaining each claimed row subtotal. -/
abbrev Declared := {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners //
  (Routed.encode owners q).declaration=decl}

/-- The physical shared word of a declared assignment fits its transmitted row. -/
noncomputable def declaredWords (q : Declared ar owners decl) : SharedWords ar decl :=
  ⟨(Routed.encode owners q.val).shared,fun p => by
    have width := (Routed.encode_accepts owners q.val).common.lengths p
    rw [q.property] at width
    exact width⟩

/-- Every routed cube assignment determines its shared traffic exactly once. -/
noncomputable def sharedMatchingEquiv :
    (Σ raw : SharedWords ar decl, Matching ar owners decl raw.val) ≃ Declared ar owners decl where
  toFun x := ⟨x.2.val,x.2.property.1⟩
  invFun q := ⟨declaredWords ar owners decl q,⟨q.val,q.property,rfl⟩⟩
  left_inv := fun ⟨⟨raw,width⟩,⟨q,shape,shared⟩⟩ => by
    change (Routed.encode owners q).shared=raw at shared
    subst raw
    rfl
  right_inv _ := rfl

variable (pins : ∀ raw : SharedWords ar decl, Matching ar owners decl raw.val → Prop)

/-- Pinned assignments expressed without a second copy of their physical traffic. -/
abbrev PinnedDeclared := {q : Declared ar owners decl //
  let x := (sharedMatchingEquiv ar owners decl).symm q
  pins x.1 x.2}

/-- Drop the unique shared word while preserving the physical host guard. -/
noncomputable def pinnedMatchingEquiv :
    (Σ raw : SharedWords ar decl, Subtype (pins raw)) ≃ PinnedDeclared ar owners decl pins := by
  let C := sharedMatchingEquiv ar owners decl
  let joined : (Σ raw, Subtype (pins raw)) ≃ {x : Σ raw : SharedWords ar decl, Matching ar owners decl raw.val // pins x.1 x.2} :=
    { toFun x := ⟨⟨x.1,x.2.val⟩,x.2.property⟩
      invFun x := ⟨x.val.1,⟨x.val.2,x.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact joined.trans (Equiv.subtypeEquivOfSubtype' C)

/-- At fixed parsed claims the physically free reports at all teams are indexed
only by the compatible pinned cube assignment and the true received cell rows. -/
noncomputable def jointRowReportsEquiv
    (layout : ∀ (raw : SharedWords ar decl), Subtype (pins raw) → Fin (R+1) → ReportLayout)
    (cells : ∀ (raw : SharedWords ar decl) (q : Subtype (pins raw)) (u : Fin (R+1)), List (ReportCell (layout raw q u))) :
    (Σ raw : SharedWords ar decl, Σ q : Subtype (pins raw), (u : Fin (R+1)) → ReportAssignments (cells raw q u)) ≃
      Σ q : PinnedDeclared ar owners decl pins, let x := (pinnedMatchingEquiv ar owners decl pins).symm q
        (u : Fin (R+1)) → ReportAssignments (cells x.1 x.2 u) :=
  (Equiv.sigmaAssoc _).symm.trans (Equiv.sigmaCongrLeft' (pinnedMatchingEquiv ar owners decl pins))

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
