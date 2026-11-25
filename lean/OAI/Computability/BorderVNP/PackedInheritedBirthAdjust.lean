import OAI.Computability.BorderVNP.PackedInheritedBirthRaw
import OAI.Computability.BorderVNP.PackedBankInstall

/-! # Shared word circuit for intrinsic work prefixes

The immutable seed packet reads its multiplicities and canonical virtual
endpoints. Its location fields use zero offsets and zero local box IDs.
Every occupied endpoint obtains one site-work addition, with a fixed scale
determined by the paid template. Absent fields share the zero expression.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening.StaticRows BankJoint ParseBatchSort VPVNP.VerifierNetwork Word
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Intrinsic arithmetic at one pin of the complete shared paid-site directory. -/
noncomputable def adjust : Raw e → WidthExpr (Raw e)
  | .inl i => .field (.inl i)
  | .inr ⟨_,none⟩ | .inr ⟨_,some none⟩ => .const 0
  | .inr ⟨v,some (some b)⟩ =>
    match reference e v b with
    | none => .const 0
    | some _ => .binary .add (PoolCircuit.scaleExpr (.inl (workCount e v)) (workScale e v))
        (.field (.inr ⟨v,some (some b)⟩))

/-- Once the final nonnegative operand fits, the repeated scaling and its final addition fit too. -/
theorem adjust_fits (w : ℕ) (source : Raw e → ℕ) (h : ∀ i, source i < 2^w) (r : Raw e)
    (hout : (adjust e r).eval source < 2^w) : (adjust e r).Fits w source := by
  rcases r with i | ⟨v,(_ | _ | b)⟩
  · exact h _
  · exact Nat.two_pow_pos _
  · exact Nat.two_pow_pos _
  · cases he : reference e v b with
    | none => simp [adjust,he,WidthExpr.Fits]
    | some u =>
      simp only [adjust,he,WidthExpr.eval,Op.apply,PoolCircuit.scale_eval] at hout
      simp only [adjust,he,WidthExpr.Fits,WidthExpr.eval,Op.apply,PoolCircuit.scale_eval]
      exact ⟨PoolCircuit.scale_fits w source _ _ (h _) (by omega),h _,hout⟩

/-- Static cost coefficient of all relative address computations at one seed. -/
noncomputable def adjustNodes := ∑ r : Raw e, (adjust e r).nodes

/-- The common adjustment frame returns all origin, terminal and paid-site
relative operands from one shared source, for every fitting input setting. -/
theorem exists_adjustFrame {S σ : Type*} [Fintype S] [Fintype σ] (w : ℕ)
    (source : Frame σ (S × Raw e × Fin w)) :
    ∃ f : Frame σ (S × Raw e × Fin w), f.size ≤ source.size + 1 +
      Fintype.card S * (adjustNodes e * (100*(w+1)^2)) ∧
      ∀ x s r, let raw := fun i => value (fun j => source.eval x (s,i,j))
        (adjust e r).eval raw < 2^w → value (fun j => f.eval x (s,r,j)) = (adjust e r).eval raw := by
  let leaf (z : S × Raw e) := ((adjust e z.2).frame w).subst
    (Frame.initial (fun i : Raw e × Fin w => (z.1,i)))
  obtain ⟨joint,hs,he⟩ := exists_parallelFrames leaf
  let picks (i : S × Raw e × Fin w) : Σ _ : S × Raw e, Fin w := ⟨(i.1,i.2.1),i.2.2⟩
  refine ⟨(joint.select picks).subst source,?_,?_⟩
  · have hl (z : S × Raw e) : (leaf z).size ≤ (adjust e z.2).nodes * (100*(w+1)^2) := by
      simp only [leaf,Frame.subst_size,Frame.initial_size,zero_add]
      exact (adjust e z.2).frame_size w
    have ht := Finset.sum_le_sum (s := Finset.univ) fun z _ => hl z
    have hsum : (∑ z : S × Raw e, (adjust e z.2).nodes*(100*(w+1)^2)) =
        Fintype.card S * (adjustNodes e*(100*(w+1)^2)) := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
        adjustNodes,← Finset.sum_mul,Nat.mul_assoc]
    rw [hsum] at ht
    simp only [Frame.subst_size,Frame.select_size]
    omega
  · intro x s r raw hout
    let localBits := fun i : Raw e × Fin w => source.eval x (s,i)
    have hval : (fun j => ((joint.select picks).subst source).eval x (s,r,j)) = ((adjust e r).frame w).eval localBits := by
      funext j
      simp [picks,he,leaf,localBits]
      congr 1
      funext i
      simp
    rw [hval]
    exact (adjust e r).frame_value w localBits (adjust_fits e w raw (fun _ => value_lt _) r hout)

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
