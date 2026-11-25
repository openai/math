import OAI.Computability.BorderVNP.ShortenPublicDirectoryStage
import OAI.Computability.BorderVNP.ShortenPublicDirectoryOccupancyMerge
import OAI.Computability.BorderVNP.ShortenPublicDenseSiteReads
import OAI.Computability.BorderVNP.ShortenPublicTraceMotion

/-!
# Shared data wires for the physical pack selector

The original occupied directory, merged endpoint table and classified rows
are saved at their production gates. Motion decoding consumes the same
classification outputs and each component is built once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open PublicSegments PublicParallel Cover Cover.AddressCircuit Epoch PreparedBins Crossing Packing
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

variable {X S R Y Z : Type*} [Fintype X] [Fintype S] [Fintype R] [Fintype Y] [Fintype Z]

/-- Combine a saved/raw source, its classification, and the motion decoded
from that classification. The saved and classified outputs are direct taps. -/
noncomputable def frontWires (merge : Frame X (S ⊕ R)) (classify : Frame R Y) (motion : Frame Y Z) :
    Frame X ((S ⊕ R) ⊕ (Z ⊕ Y)) :=
  let read := (classify.subst (Frame.initial Sum.inr)).withInput
  let move := (motion.subst (Frame.initial Sum.inr)).withInput
  let pins : (S ⊕ R) ⊕ (Z ⊕ Y) → ((S ⊕ R) ⊕ Y) ⊕ Z :=
    Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr))
  ((move.select pins).subst read).subst merge

/-- The front-end gate list contains exactly one copy of each stage. -/
theorem frontWires_size (merge : Frame X (S ⊕ R)) (classify : Frame R Y) (motion : Frame Y Z) :
    (frontWires merge classify motion).size = merge.size + (classify.size+motion.size) := by
  simp [frontWires]

/-- Saving rows and the independent occupied bits preserves every merged
field and feeds the literal classification to the literal motion selector. -/
theorem frontWires_eval (merge : Frame X (S ⊕ R)) (classify : Frame R Y) (motion : Frame Y Z)
    (x : X → Bool) :
    let saved := merge.eval x
    let y := classify.eval (saved ∘ Sum.inr)
    (frontWires merge classify motion).eval x = Sum.elim saved (Sum.elim (motion.eval y) y) := by
  intro saved y
  let classRead := (classify.subst (Frame.initial (Sum.inr : R → S ⊕ R))).withInput
  have hread : (Frame.initial (Sum.inr : R → S ⊕ R)).eval saved = saved ∘ Sum.inr := funext fun _ => by simp
  have cls : classRead.eval saved = Sum.elim saved y := by
    funext v
    cases v <;> simp [classRead,y,hread]
  let moved := (motion.subst (Frame.initial (Sum.inr : Y → (S ⊕ R) ⊕ Y))).withInput
  have hin : (Frame.initial (Sum.inr : Y → (S ⊕ R) ⊕ Y)).eval (Sum.elim saved y) = y := funext fun _ => by simp
  have mo : moved.eval (Sum.elim saved y) = Sum.elim (Sum.elim saved y) (motion.eval y) := by
    funext v
    cases v <;> simp [moved,hin]
  funext v
  simp only [frontWires,Frame.subst_eval,Frame.select_eval]
  change moved.eval (classRead.eval saved)
    ((Sum.elim (Sum.inl ∘ Sum.inl) (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr))) v) = _
  rw [cls,mo]
  rcases v with v | (v|v) <;> rfl

variable {D n d k : ℕ} {Port : Type} {bits : Port → ℕ} {K : Type*}

private theorem cast_ne {I : Type} {a b : ℕ} (h : a=b) (x y : SurfaceHost I a) :
    levelCast h x ≠ levelCast h y ↔ x ≠ y := by cases h; rfl

/-- Classifying the positive part after reindexing the depth selects exactly
the positive-length charged cables of the physical child. -/
theorem positiveMask_childSites (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n)) :
    positiveMask (fun i => (child i).pack) (childSites child) (fun i => (child i).charged) =
      fun i => (child i).active := by
  funext i a
  simp only [positiveMask,childSites,PlacedPack.active,cast_ne]

/-- Ownership of each occupied row is read from the corresponding physical
rectangle of the merged directory. -/
theorem parallelName_owner {k E : ℕ} {Edge : Fin k → Type*} (rows : ∀ i, Edge i ↪ Fin E)
    (a : Σ i, Edge i) : (finProdFinEquiv.symm (parallelName rows a)).1 = a.1 := by
  exact congrArg Prod.fst (unflat_flat a.1 (rows a.1 a.2))

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
