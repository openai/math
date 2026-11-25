import OAI.Computability.BorderVNP.PackedPoolWords

/-! # Emitting the boundaries of every direction band

For each bin the common width of its inverse seed determines the right end of a prefix.
The two adjacent residual cuts and the final tail are computed without iterating over any
cable bits. All output rows share the DAG supplying the bin directory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PoolCircuit

open Word Shortening.SeedIntervals VPVNP.VerifierNetwork ParseBatchSort
open scoped Classical

private def endpointExpr (D : ℕ) (b : Band D) (right : Bool) : WidthExpr (LocalWord D) :=
  let pool := Sum.inl 1
  match b, right with
  | none, false => scaleExpr pool D
  | none, true => .field (.inl 0)
  | some (i,true), false => scaleExpr pool i.val
  | some (i,false), true => scaleExpr pool (i.val+1)
  | some (i,_), _ => .binary .add (scaleExpr pool i.val) (.field (.inr i))

/-- Choose the left or right endpoint of the allocator's actual cut interval. -/
def bandEnd {D : ℕ} (c pool : ℕ) (take : Fin D → ℕ) (b : Band D) (right : Bool) : ℕ :=
  if right then (bandCuts c pool take b).2 else (bandCuts c pool take b).1

private theorem endpoint_eval {D : ℕ} (x : LocalWord D → ℕ) (b : Band D) (r : Bool) :
    (endpointExpr D b r).eval x = bandEnd (x (.inl 0)) (x (.inl 1)) (fun i => x (.inr i)) b r := by
  rcases b with _ | ⟨i,t⟩
  · cases r <;> simp [endpointExpr,bandEnd,bandCuts,WidthExpr.eval,scale_eval]
  · cases t <;> cases r <;> simp [endpointExpr,bandEnd,bandCuts,WidthExpr.eval,Op.apply,scale_eval]

private theorem endpoint_fits {D w : ℕ} (x : LocalWord D → ℕ)
    (h : ∀ j, x j < 2^w) (hd : D * x (.inl 1) ≤ x (.inl 0))
    (ht : ∀ i, x (.inr i) ≤ x (.inl 1)) (b : Band D) (r : Bool) :
    (endpointExpr D b r).Fits w x := by
  let pool := x (.inl 1)
  have hscale (k : ℕ) (hk : k ≤ D) : (scaleExpr (.inl 1) k).Fits w x :=
    scale_fits w _ _ _ (h _) ((Nat.mul_le_mul_right pool hk).trans_lt (hd.trans_lt (h _)))
  rcases b with _ | ⟨i,t⟩
  · cases r
    · exact hscale D le_rfl
    · exact h _
  · have hadd : (.binary .add (scaleExpr (.inl 1) i.val) (.field (.inr i)) :
        WidthExpr (LocalWord D)).Fits w x := by
      refine ⟨hscale i.val i.isLt.le,h _,?_⟩
      simp only [Op.apply,WidthExpr.eval,scale_eval]
      calc
        i.val * pool + x (.inr i) ≤ i.val * pool + pool := Nat.add_le_add_left (ht i) _
        _ = (i.val+1) * pool := (Nat.succ_mul _ _).symm
        _ ≤ D * pool := Nat.mul_le_mul_right _ i.isLt
        _ < _ := hd.trans_lt (h _)
    cases t <;> cases r
    · exact hadd
    · exact hscale _ i.isLt
    · exact hscale _ i.isLt.le
    · exact hadd

/-- Total number of arithmetic operations across the fixed one-bin cuts. -/
def endpointNodes (D : ℕ) : ℕ :=
  ∑ i : Band D × Bool, (endpointExpr D i.1 i.2).nodes

/-- Emit both endpoints for every band of every bin. The gate cost scales linearly with
the number of bins; the geometric dimension occurs only in the fixed multiplier. -/
theorem endpoints_frame {A σ : Type*} [Fintype A] [Fintype σ] (D w : ℕ)
    (directory : Frame σ (A × LocalWord D × Fin w)) :
    ∃ f : Frame σ (A × Band D × Bool × Fin w),
      f.size ≤ directory.size + 1 + Fintype.card A * (endpointNodes D * (100*(w+1)^2)) ∧
      ∀ (x : σ → Bool) (a : A),
        let fields := fun i => value (fun j => directory.eval x (a,i,j))
        D * fields (.inl 1) ≤ fields (.inl 0) →
        (∀ d, fields (.inr d) ≤ fields (.inl 1)) →
        ∀ b r, value (fun j => f.eval x (a,b,r,j)) =
          bandEnd (fields (.inl 0)) (fields (.inl 1)) (fun i => fields (.inr i)) b r := by
  let row (i : A × (Band D × Bool)) :=
    ((endpointExpr D i.2.1 i.2.2).frame w).subst (Frame.initial (fun p => (i.1,p)))
  obtain ⟨joint,hj,he⟩ := Crossing.exists_parallelFrames row
  let names (z : A × Band D × Bool × Fin w) : Σ _ : A × (Band D × Bool), Fin w :=
    ⟨(z.1,z.2.1,z.2.2.1),z.2.2.2⟩
  refine ⟨(joint.select names).subst directory, ?_, ?_⟩
  · have hsum : (∑ i, (row i).size) ≤ Fintype.card A * (endpointNodes D * (100*(w+1)^2)) := by
      simp only [row, Frame.subst_size, Frame.initial_size,zero_add]
      calc
        _ ≤ ∑ i : A × (Band D × Bool), (endpointExpr D i.2.1 i.2.2).nodes * (100*(w+1)^2) :=
          Finset.sum_le_sum (fun i _ => (endpointExpr D i.2.1 i.2.2).frame_size w)
        _ = _ := by
          rw [Fintype.sum_prod_type]
          simp only [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,endpointNodes,mul_assoc,Nat.cast_id]
    rw [Frame.subst_size,Frame.select_size]
    omega
  · intro x a fields hd ht b r
    let z := fun i : LocalWord D × Fin w => directory.eval x (a,i)
    have hz : (fun j => (joint.select names).eval (directory.eval x) (a,b,r,j)) =
        ((endpointExpr D b r).frame w).eval z := by
      funext j
      simp only [Frame.select_eval, names,he,row,Frame.subst_eval]
      congr 1
      funext i
      simp [z]
    have hv : (fun j => ((joint.select names).subst directory).eval x (a,b,r,j)) =
        ((endpointExpr D b r).frame w).eval z := by
      simpa only [Frame.subst_eval] using hz
    rw [hv, (endpointExpr D b r).frame_value w z (endpoint_fits fields (fun i => value_lt _) hd ht b r),
      endpoint_eval]

end Packing.PoolCircuit

end BorderVNP
end Computability
end OAI
