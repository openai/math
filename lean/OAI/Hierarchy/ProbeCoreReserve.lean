import OAI.Hierarchy.ProbeCoreBoard

namespace OAI
/-! # The public initial catalyst bits on the literal board columns -/

namespace Hierarchy.ProbeStage.CoreBoard
noncomputable section
open scoped Classical BigOperators

abbrev ReserveBits (h d k R : ℕ) :=
  (_j : Fin k) × Fin (Fintype.card (Columns h d)*R)

private def seats (h d R : ℕ) : Columns h d × Fin R ≃ Fin (Fintype.card (Columns h d)*R) :=
  ((Fintype.equivFin (Columns h d)).prodCongr (Equiv.refl (Fin R))).trans finProdFinEquiv

def reserveSeats (h d k R : ℕ) :
    ReserveBits h d k R ≃ (Columns h d × Fin k) × Fin R where
  toFun v :=
    let ci := (seats h d R).symm v.2
    ((ci.1,v.1),ci.2)
  invFun x := ⟨x.1.2,(seats h d R) (x.1.1,x.2)⟩
  left_inv := by rintro ⟨j,b⟩; simp
  right_inv := by rintro ⟨⟨c,j⟩,b⟩; simp

def reserveLocation (h d k R : ℕ) (v : ReserveBits h d k R) : Columns h d × Fin k :=
  (reserveSeats h d k R v).1

/-- A catalyst input pin carries its physical low digit in its original ordinal. -/
theorem reserve_digit (h d k R : ℕ) (v : ReserveBits h d k R) :
    (reserveSeats h d k R v).2.val=v.2.val%R := rfl

/-- The straight reserve slab uses contiguous bits at each original column. -/
theorem reserve_column_ordinal (h d k R : ℕ) (v : ReserveBits h d k R) :
    ((Fintype.equivFin (Columns h d)) (reserveLocation h d k R v).1).val=v.2.val/R := by
  change ((Fintype.equivFin _)
    ((Fintype.equivFin _).symm (Fin.divNat v.2))).val=v.2.val/R
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] theorem reserve_axis (h d k R : ℕ) (v : ReserveBits h d k R) :
    (reserveLocation h d k R v).2=v.1 := rfl

/-- The same initial word R applies at every geometric pair, even when R=0,
independently of input tags or any controller choice. -/
theorem reserve_fiber (h d k R : ℕ) (c : Columns h d × Fin k) :
    Fintype.card {v : ReserveBits h d k R // reserveLocation h d k R v=c}=R := by
  let e := reserveSeats h d k R
  let f : {v : ReserveBits h d k R // reserveLocation h d k R v=c} ≃ Fin R := {
    toFun := fun v=>(e v.val).2
    invFun := fun r=>⟨e.symm (c,r),congrArg Prod.fst (e.apply_symm_apply (c,r))⟩
    left_inv := by
      intro v; apply Subtype.ext; apply e.injective; rw [e.apply_symm_apply]
      exact Prod.ext v.property.symm rfl
    right_inv := by intro r; simp }
  simpa only [Fintype.card_fin] using Fintype.card_congr f

theorem reserve_count (h d k R : ℕ) : Fintype.card (ReserveBits h d k R) =
    Fintype.card (Columns h d)*k*R := by
  simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_congr (reserveSeats h d k R)

/-- A fixed number of batches of per-pair edits, each with at most Bw
physical bits, is supported by the same advance reservation for all executions. -/
theorem reserve_usage {B w events : ℕ} (uses : Fin events→ℕ)
    (bound : ∀ j,uses j≤B*w) : (∑ j,uses j)≤(events*B)*w := by
  calc
    _ ≤ ∑ _j : Fin events,B*w := Finset.sum_le_sum (fun j _=>bound j)
    _ = _ := by simp [Nat.mul_assoc]

theorem reserve_total_bound {h d k w R B : ℕ} (hd : 1≤d) (per : R≤B*w) :
    Fintype.card (ReserveBits h d k R) ≤
      ((2+2*(Stages h d)*4^(rounds d+1))*k*B)*(2^h*w) := by
  rw [reserve_count]
  have cols := payloadColumns_card_le h d hd
  calc
    _ ≤ ((2*2^h+2*(Stages h d)*(4^(rounds d+1)*2^h))*k)*(B*w) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ cols) per
    _ = _ := by ring

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
