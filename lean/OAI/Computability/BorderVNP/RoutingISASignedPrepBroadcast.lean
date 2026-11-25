import OAI.Computability.BorderVNP.RoutingISASignedPrepRows
import OAI.Computability.BorderVNP.CubeISALocalRowBootMinimum

/-! # The unique raw public declaration of every passing routed assignment

All bits of the grouping coordinate and the direction-by-direction row lengths
come from the broadcast. The native range check excludes unused codes. At an
in-range code, the selector and row checks determine every decoded integer, hence
the raw broadcast itself. Reports and zero-padding pins remain dependent on the
actual routed assignment throughout this reindexing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment
open private read_write from OAI.Computability.BorderVNP.CubePhysicalDeclarationWords

variable {R : ℕ} (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))

/-- The exact field width used by the secondary geometry header. -/
abbrev RawBroadcast := Broadcast ar.n ar.header.d (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s)

/-- Raw bit strings surviving the native axis and row-field range comparisons. -/
abbrev CheckedBroadcast := {raw : RawBroadcast ar // LocalRow.declarationInRange raw}

/-- The actual machine's grouped axis and integer row array after binary decoding. -/
def decodedBroadcast (raw : RawBroadcast ar) : LengthDeclaration ar.n ar.header.d :=
  (Fin.ofNat (ar.n+1) (readCode _ raw.1),fun p j => readCode _ (raw.2 p j))

/-- Public words selected by the physical packet summands of a routed assignment. -/
noncomputable def routeBroadcast (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) :
    CheckedBroadcast ar :=
  ⟨broadcast ar.b ar.s q.1,(LocalRow.broadcast_passes_minimum ar.b ar.s q.1).1⟩

/-- The advertised values recovered by the actual decoder are exactly the selector's
chosen axis and all of its measured subtotals. -/
theorem decoded_routeBroadcast (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) :
    decodedBroadcast ar (routeBroadcast ar owners q).val = (Routed.encode owners q).declaration := by
  apply Prod.ext
  · apply Fin.ext
    simp only [decodedBroadcast,routeBroadcast,broadcast,read_write,Fin.ofNat,Fin.val_mk,
      Nat.mod_eq_of_lt (chosen ar.b ar.s q.1).isLt]
    rfl
  · funext p j
    simp only [decodedBroadcast,routeBroadcast,broadcast,read_write]
    rfl

/-- At any surviving raw bit string, actual declaration agreement forces
word-for-word equality with the routed assignment's encoding. -/
theorem declared_iff_routeBroadcast (x : CheckedBroadcast ar)
    (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) :
    (Routed.encode owners q).declaration = decodedBroadcast ar x.val ↔ x = routeBroadcast ar owners q := by
  constructor
  · intro same
    apply Subtype.ext
    apply (passesBroadcast_iff ar.b ar.s q.1 x.val).mp
    refine ⟨(decodedBroadcast ar x.val).1,?_,(passesLengths_iff ..).mpr same.symm⟩
    exact (Nat.mod_eq_of_lt x.property.1).symm
  · rintro rfl
    exact (decoded_routeBroadcast ar owners q).symm

/-- Summing over the in-range public declaration and every compatible physical
assignment visits each actual route exactly once. -/
noncomputable def declaredBroadcastEquiv :
    (Σ x : CheckedBroadcast ar, Declared ar owners (decodedBroadcast ar x.val)) ≃
      NativeAssignments.Routed (b := ar.b) (s := ar.s) owners where
  toFun x := x.2.val
  invFun q := ⟨routeBroadcast ar owners q,⟨q,(decoded_routeBroadcast ar owners q).symm⟩⟩
  left_inv := by
    rintro ⟨x,⟨q,same⟩⟩
    obtain rfl := (declared_iff_routeBroadcast ar owners x q).mp same
    rfl
  right_inv _ := rfl

variable (pins : ∀ (x : CheckedBroadcast ar) (raw : SharedWords ar (decodedBroadcast ar x.val)),
  Matching ar owners (decodedBroadcast ar x.val) raw.val → Prop)

/-- The host pins on the true routed assignment, evaluated with its unique
public declaration and its unique physical shared row. -/
abbrev BroadcastPinnedRoute := {q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners //
  let x := (declaredBroadcastEquiv ar owners).symm q
  let y := (sharedMatchingEquiv ar owners (decodedBroadcast ar x.1.val)).symm x.2
  pins x.1 y.1 y.2}

/-- Eliminate the raw declaration without dropping any of the real host pin checks. -/
noncomputable def pinnedBroadcastEquiv :
    (Σ x : CheckedBroadcast ar, PinnedDeclared ar owners (decodedBroadcast ar x.val) (pins x)) ≃
      BroadcastPinnedRoute ar owners pins := by
  let joined : (Σ x : CheckedBroadcast ar, PinnedDeclared ar owners (decodedBroadcast ar x.val) (pins x)) ≃
      {z : Σ x : CheckedBroadcast ar, Declared ar owners (decodedBroadcast ar x.val) //
        let y := (sharedMatchingEquiv ar owners (decodedBroadcast ar z.1.val)).symm z.2
        pins z.1 y.1 y.2} :=
    { toFun x := ⟨⟨x.1,x.2.val⟩,x.2.property⟩
      invFun z := ⟨z.val.1,⟨z.val.2,z.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact joined.trans (Equiv.subtypeEquivOfSubtype' (declaredBroadcastEquiv ar owners))

/-- Reindex the actual team-local report fibers while eliminating the broadcast
axis. The inverse uses the very same declaration and pinned route for the reports. -/
noncomputable def pinnedBroadcastReportsEquiv
    (Report : ∀ x : CheckedBroadcast ar, PinnedDeclared ar owners (decodedBroadcast ar x.val) (pins x) → Type*) :
    (Σ x : CheckedBroadcast ar, Σ q : PinnedDeclared ar owners (decodedBroadcast ar x.val) (pins x), Report x q) ≃
      Σ q : BroadcastPinnedRoute ar owners pins, let z := (pinnedBroadcastEquiv ar owners pins).symm q
        Report z.1 z.2 :=
  (Equiv.sigmaAssoc _).symm.trans (Equiv.sigmaCongrLeft' (pinnedBroadcastEquiv ar owners pins))

/-- Erase precisely the out-of-range raw header fibers when every actual return
of the native stage has passed its range check. -/
def returningBroadcastEquiv (Ret : RawBroadcast ar → Type*) (range : ∀ x, Ret x → LocalRow.declarationInRange x) :
    (Σ x : RawBroadcast ar, Ret x) ≃ (Σ x : CheckedBroadcast ar, Ret x.val) where
  toFun z := ⟨⟨z.1,range z.1 z.2⟩,z.2⟩
  invFun z := ⟨z.1.val,z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
