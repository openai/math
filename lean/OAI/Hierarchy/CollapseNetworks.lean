import OAI.Hierarchy.PointwiseCollapse
import OAI.Hierarchy.CorrectionFrame
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Literal tick arities in a replicated approximation -/

noncomputable section
namespace Hierarchy.CollapseOracle
open Catalyst CorrectionFrame ThreeFlat
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p : ℕ}

def single (k : ℕ) (tick : BitNetwork F p) : Approximation F k (1*p) where
  width _ := 0
  network := tick.restrictPins (fun i => some (Fintype.equivFin _ (.inl
    (finProdFinEquiv ((0:Fin 1),i)))))

private theorem empty_ports (k p : ℕ) :
    Fintype.card (Port (1*p) (fun _ : Fin k => 0)) = p := by
  let : IsEmpty (Wire (fun _ : Fin k => 0) × Bool) := ⟨fun w => w.1.2.elim0⟩
  exact (Fintype.card_congr (Equiv.sumEmpty (Fin (1*p)) _)).trans (by simp)

omit [Field F] in
theorem single_size (tick : BitNetwork F p) :
    (single k tick).size = tick.cells+tick.internal+p := by
  change tick.cells+tick.internal+Fintype.card (Port (1*p) (fun _ : Fin k => 0)) = _
  rw [empty_ports]

omit [Field F] in
theorem single_ports (tick : BitNetwork F p) :
    Fintype.card (Port (1*p) (single k tick).width) = p :=
  empty_ports k p

theorem single_gap (tick : BitNetwork F p) (D : ℝ) :
    (single k tick).PointwiseGap (tickProduct tick 1) D := by
  intro _ pin
  left
  funext w
  change (single k tick).coeff (Sum.elim pin w) - ideal _ _ (Sum.elim pin w) = 0
  have eqs : ∀ z : Wire (single k tick).width,
      Sum.elim pin w (.inr (z,false)) = Sum.elim pin w (.inr (z,true)) :=
    fun z => z.2.elim0
  rw [ideal,ite_eq_left eqs,sub_eq_zero]
  simp only [tickProduct,Fin.prod_univ_one]
  unfold Approximation.coeff single
  rw [BitNetwork.restrictPins_eval]
  apply congrArg tick.eval
  funext i
  simp

def castPins {r t : ℕ} (h : r=t) (X : Approximation F k r) : Approximation F k t := h ▸ X

theorem castPins_gap {r t : ℕ} (h : r=t) (X : Approximation F k r)
    (f : (Fin r → Bool) → F) (g : (Fin t → Bool) → F) {D : ℝ} (gap : X.PointwiseGap f D)
    (eqn : ∀ x, f x = g (x ∘ Fin.cast h.symm)) : (castPins h X).PointwiseGap g D := by
  subst t
  have same : f = g := funext (fun x => eqn x)
  simpa [castPins,same] using gap

omit [Field F] in
@[simp] theorem castPins_width {r t : ℕ} (h : r=t) (X : Approximation F k r) :
    (castPins h X).width = X.width := by cases h; rfl

omit [Field F] in
@[simp] theorem castPins_size {r t : ℕ} (h : r=t) (X : Approximation F k r) :
    (castPins h X).size = X.size := by cases h; rfl

theorem flatten (d q : ℕ) (tick : BitNetwork F p) (x : Fin (d*(q*p)) → Bool) :
    dataProduct d (tickProduct tick q) x =
      tickProduct tick (d*q) (x ∘ Fin.cast (Nat.mul_assoc _ _ _)) := by
  unfold dataProduct tickProduct
  rw [← (finProdFinEquiv (m:=d) (n:=q)).prod_comp]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  apply congrArg tick.eval
  funext a
  apply congrArg x
  apply Fin.ext
  simp [finProdFinEquiv_apply_val,Nat.mul_add,Nat.add_assoc,
    Nat.mul_comm,Nat.mul_left_comm]

end Hierarchy.CollapseOracle

end
end OAI
