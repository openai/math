import OAI.Computability.BorderVNP.PackedInheritedBirthAdjust
import OAI.Computability.BorderVNP.PackedInheritedEndpointViews

/-! # Arithmetic words for the permanent per-site private areas

Fixed gate frames evaluate one expression per named row from shared input
columns. Birth sites read their accepted multiplicities. Work and current
incidence are kept as distinct fields until the next retention step.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening.StaticRows InheritedProfile ParseBatchSort VPVNP.VerifierNetwork Word
open scoped Classical

variable {A B I σ : Type*} [Fintype A] [Fintype B] [Fintype I] [Fintype σ] {w : ℕ}

/-- Read a fixed arithmetic expression at each requested source row, sharing
the circuit that produced all the input words. -/
theorem exists_words (source : Frame σ (A × I × Fin w)) (row : B → A) (expr : B → WidthExpr I) :
    ∃ f : Frame σ (B × Fin w), f.size ≤ source.size + 1 + (∑ b, (expr b).nodes) * (100*(w+1)^2) ∧
      ∀ x b, let args := fun i => value (fun j => source.eval x (row b,i,j))
        (expr b).Fits w args → value (fun j => f.eval x (b,j)) = (expr b).eval args := by
  let leaf (b : B) := ((expr b).frame w).subst (Frame.initial (fun i : I × Fin w => (row b,i)))
  obtain ⟨joint,hs,he⟩ := exists_parallelFrames leaf
  let pick (i : B × Fin w) : Σ _ : B, Fin w := ⟨i.1,i.2⟩
  refine ⟨(joint.select pick).subst source,?_,?_⟩
  · have hsum := Finset.sum_le_sum (s := Finset.univ) fun b _ =>
      show (leaf b).size ≤ (expr b).nodes * (100*(w+1)^2) by
        simpa only [leaf,Frame.subst_size,Frame.initial_size,zero_add] using (expr b).frame_size w
    rw [← Finset.sum_mul] at hsum
    simp only [Frame.subst_size,Frame.select_size]
    omega
  · intro x b args h
    let bits := fun i : I × Fin w => source.eval x (row b,i)
    have hb : (fun j => ((joint.select pick).subst source).eval x (b,j)) = ((expr b).frame w).eval bits := by
      funext j
      simp [pick,he,leaf,bits]
      congr 1
      funext i
      simp
    rw [hb]
    exact (expr b).frame_value w bits h

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- One complete template's arithmetic cost is fixed by the crossing identity. -/
noncomputable def birthNodes := ∑ v : TemplateSite e, (PoolCircuit.scaleExpr (workCount e v) (workScale e v)).nodes

/-- The immutable origin, terminal and paid work fields are computed directly
from the branch's matched count and selected histogram. -/
theorem exists_birth (counts : Frame σ (A × Option (Fin e.count) × Fin w)) :
    ∃ f : Frame σ ((A × TemplateSite e) × Fin w), f.size ≤ counts.size + 1 +
      Fintype.card A * birthNodes e * (100*(w+1)^2) ∧
      ∀ x a v, let cnt := fun i => value (fun j => counts.eval x (a,i,j))
        intrinsicWork e (cnt none) (cnt ∘ some) v < 2^w →
        value (fun j => f.eval x ((a,v),j)) = intrinsicWork e (cnt none) (cnt ∘ some) v := by
  let expr (z : A × TemplateSite e) := PoolCircuit.scaleExpr (workCount e z.2) (workScale e z.2)
  obtain ⟨f,hs,hf⟩ := exists_words counts Prod.fst expr
  refine ⟨f,?_,?_⟩
  · simpa only [expr,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,birthNodes] using hs
  · intro x a v cnt fit
    have eval : (expr (a,v)).eval cnt = intrinsicWork e (cnt none) (cnt ∘ some) v := by
      simp only [expr,PoolCircuit.scale_eval,intrinsicWork]
      cases workCount e v <;> rfl
    rw [← eval] at fit ⊢
    apply hf x (a,v)
    apply PoolCircuit.scale_fits w cnt (workCount e v) (workScale e v) (value_lt _)
    simpa only [expr,PoolCircuit.scale_eval] using fit

/-- A frame covers a live word in each genuine row and produces zero at
every unused slot of the same fixed rectangle. -/
structure Covers {V : Type*} {s : ℕ} (id : V ↪ Fin s) (n : V → ℕ) (f : Frame σ (Fin s × Fin w))
    (x : σ → Bool) : Prop where
  live : ∀ v, value (fun j => f.eval x (id v,j)) = n v
  hole : ∀ i, i ∉ Set.range id → value (fun j => f.eval x (i,j)) = 0

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
