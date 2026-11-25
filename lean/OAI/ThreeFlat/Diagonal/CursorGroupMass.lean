import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace
import OAI.ThreeFlat.Diagonal.TickBucketChronology

namespace OAI
/-! # Group mass of the clipped initial cursor lanes -/
namespace ThreeFlat.Diagonal.PhysicalStage.Block

open Computability.VPVNP.Compression HistoryContraction TickChronology TickPhaseModel
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] (B : Block F) {k : ℕ} (hk : 2≤k) (low off cells : ℕ)
local notation "X" => B.cursorState hk low off cells

private theorem clipped_length (n start span : ℕ) :
    min n (start + span) - min n start = min (n - start) span := by
  simp only [Nat.min_def]
  split_ifs <;> omega

/-- The chronological bucket list and the typed predecessor masses use the same
clipped interval on the first cursor layer. All other layers contribute zero. -/
theorem cursor_length_sum (r : Run F X) (bits : r.plan.History → ℕ) (clk : Clock) (width : ℕ)
    (T : Buckets r.plan bits clk width (2^k) (2^low))
    (site : ∀ i,T.site i=(⟨0,by omega⟩,finFunctionFinEquiv.symm i))
    (v : Plan.Terminal r.plan bits) (g : ℕ) :
    T.length v g = ∑ x : (X).Site, if (T.group v.1 (r.plan.destination v.1 x)).val=g then
      B.clippedPairs hk low off cells (clk.chunks*width) x else 0 := by
  let first : Fin k := ⟨0,by omega⟩
  let total := clk.chunks*width
  let mass (x : (X).Site) := if (T.group v.1 (r.plan.destination v.1 x)).val=g then
    B.clippedPairs hk low off cells total x else 0
  have size (i : Fin (2^k)) :
      (ClippedPairBuckets.row T.site total (2^low) i).size = B.clippedPairs hk low off cells total (T.site i) := by
    rw [site i]
    simp only [ClippedPairBuckets.row,Bucket.size,clippedPairs,cursorOrdinal_eq,Equiv.apply_symm_apply,
      Nat.zero_mul,Nat.zero_add,i.isLt,ite_true,Nat.add_mul,Nat.one_mul]
    exact clipped_length total (i.val * 2^low) (2^low)
  calc
    T.length v g = ∑ i : Fin (2^k),mass (T.site i) := by
      simp only [Buckets.length,Buckets.rows,ClippedPairBuckets.rows,BucketRows.count,List.map_ofFn,
        List.sum_ofFn,Function.comp_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (if (T.group v.1 (r.plan.destination v.1 (T.site i))).val=g then
        (ClippedPairBuckets.row T.site total (2^low) i).size else 0)=_
      rw [size]
    _ = ∑ u : BitWord k,mass (T.site (finFunctionFinEquiv u)) := (finFunctionFinEquiv.sum_comp _).symm
    _ = ∑ u : BitWord k,mass (first,u) := by
      apply Finset.sum_congr rfl
      intro u _
      exact congrArg mass ((site (finFunctionFinEquiv u)).trans
        (congrArg (fun lane : BitWord k => (first,lane)) (finFunctionFinEquiv.symm_apply_apply u)))
    _ = _ := by
      change _ = ∑ x : Fin k × BitWord k,mass x
      rw [Fintype.sum_prod_type]
      symm
      apply Finset.sum_eq_single first
      · intro i _ hi
        apply Finset.sum_eq_zero
        intro u _
        have nonzero : 0< i.val := Nat.pos_of_ne_zero (fun e=>hi (Fin.ext e))
        have large : 2^k≤ i.val*2^k+(finFunctionFinEquiv u).val :=
          (Nat.le_mul_of_pos_left _ nonzero).trans (Nat.le_add_right ..)
        have outside : ¬ B.cursorOrdinal hk low off cells i u < 2^k :=
          not_lt_of_ge large
        have empty : B.clippedPairs hk low off cells total (i,u) = 0 := ite_eq_right outside
        simp only [empty, ite_self]
      · simp


end
end ThreeFlat.Diagonal.PhysicalStage.Block

end OAI
