import OAI.Hierarchy.TaggedGuard
import OAI.ThreeFlat.Routing.AddWords
import OAI.ThreeFlat.Routing.CompareWord
import Mathlib.Tactic

namespace OAI
/-! # Checking neighboring real destinations in an aligned transport

The increment verifier widens both words by one bit. Pinning that high result
bit to zero enforces successor in the natural numbers.
-/

namespace Hierarchy.Tagged.AlignWord
open ThreeFlat Routing
open scoped Classical
noncomputable section

abbrev Pin (w : ℕ) := Bool × Fin w

def bits {w : ℕ} (x y : BitVec w) (p : Pin w) := (if p.1 then y else x).getLsbD p.2.val

private def feed {w : ℕ} (p : AddWords.Pin (w+1)) : Fin (Fintype.card (Pin w)) ⊕ Bool :=
  if p.1 = 1 then .inr (decide (p.2.val = 0))
  else if h : p.2.val < w then .inl (Fintype.equivFin _ (decide (p.1 = 2), ⟨p.2.val,h⟩))
  else .inr false

def increment (F : Type*) [Zero F] [One F] (w : ℕ) : BitNetwork F (Fintype.card (Pin w)) :=
  Guard.rename (AddWords.network F (w+1)) (feed ∘ (Fintype.equivFin _).symm)

private theorem increment_pins {w : ℕ} (x y : BitVec w) (p : AddWords.Pin (w+1)) :
    Sum.elim ((bits x y) ∘ (Fintype.equivFin _).symm) id (feed p) =
      AddWords.pins (x.setWidth (w+1)) (1 : BitVec (w+1)) (y.setWidth (w+1)) p := by
  rcases p with ⟨t,i⟩
  by_cases hi : i.val < w
  · fin_cases t <;> simp [bits, feed, AddWords.pins, hi, i.isLt]
  · have hx := BitVec.getLsbD_of_ge x i.val (Nat.le_of_not_gt hi)
    have hy := BitVec.getLsbD_of_ge y i.val (Nat.le_of_not_gt hi)
    fin_cases t <;> simp [feed, AddWords.pins, hi, hx, hy, i.isLt]

theorem increment_eval (F : Type*) [CommSemiring F] {w : ℕ} (x y : BitVec w) :
    TypedWiring.value (increment F w) (bits x y) = if y.toNat = x.toNat + 1 then 1 else 0 := by
  change (increment F w).eval ((bits x y) ∘ (Fintype.equivFin _).symm) = _
  rw [increment, Guard.rename_value]
  calc
    _ = TypedWiring.value (AddWords.network F (w+1)) (AddWords.pins (x.setWidth (w+1)) 1
        (y.setWidth (w+1))) := by
      unfold TypedWiring.value
      congr 1
      funext i
      exact increment_pins x y ((Fintype.equivFin _).symm i)
    _ = _ := by
      rw [AddWords.network_eval]
      have xx := x.isLt
      have yy := y.isLt
      have xp : x.toNat+1 < 2^(w+1) := by rw [pow_succ]; omega
      have xok : x.toNat < 2^(w+1) := by omega
      have yok : y.toNat < 2^(w+1) := by rw [pow_succ]; omega
      congr 1
      apply propext
      rw [← BitVec.toNat_inj]
      simp [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.mod_eq_of_lt xp,
        Nat.mod_eq_of_lt xok, Nat.mod_eq_of_lt yok]

theorem increment_size (F : Type*) [Zero F] [One F] (w : ℕ) :
    (increment F w).cells+(increment F w).internal ≤ 500*(w+2) :=
  AddWords.network_size F (w+1)

/-- Testing equality on one row pair costs one trivalent cell per bit. -/
def equal (F : Type*) [Zero F] [One F] (w : ℕ) : BitNetwork F (Fintype.card (Pin w)) where
  internal := 0
  cells := w
  source i t := .pin (Fintype.equivFin _ (decide (0 < t.val),i))
  table _ v := if v 0 = v 1 then 1 else 0

theorem equal_eval (F : Type*) [CommSemiring F] {w : ℕ} (x y : BitVec w) :
    TypedWiring.value (equal F w) (bits x y) = if x = y then 1 else 0 := by
  simp only [TypedWiring.value,BitNetwork.eval,BitNetwork.weight,BitNetwork.factor,equal,
    BitSource.read,Equiv.symm_apply_apply]
  change (∑ _ : Fin 0 → Bool, ∏ i : Fin w, if x.getLsbD i.val = y.getLsbD i.val then (1:F) else 0) = _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_nsmul,
    Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro same
    exact BitVec.eq_of_getLsbD_eq (fun i hi => same ⟨i,hi⟩)
  · rintro rfl i
    rfl

private def comparePin {w : ℕ} (i : Fin (w+w)) : Fin (Fintype.card (Pin w)) ⊕ Bool :=
  .inl (Fintype.equivFin _ (Fin.addCases (fun j => (false,j)) (fun j => (true,j)) i))

def less (F : Type*) [Zero F] [One F] (w : ℕ) : BitNetwork F (Fintype.card (Pin w)) :=
  Guard.rename (compareBits F w) comparePin

theorem less_eval (F : Type*) [CommSemiring F] {w : ℕ} (x y : BitVec w) :
    TypedWiring.value (less F w) (bits x y) = if x.toNat < y.toNat then 1 else 0 := by
  unfold TypedWiring.value less
  rw [Guard.rename_value, compareBits_eval]
  simp only [comparePin, Function.comp_apply, Sum.elim_inl, Equiv.symm_apply_apply,
    Fin.addCases_left, Fin.addCases_right, bits, Bool.false_eq_true, ite_false, ite_true,
    wordValue_addressEquiv]
  change (if (ExactQuantumFactoring.bitsValue (fun i : Fin w => x.getLsbD i.val)).toNat <
    (ExactQuantumFactoring.bitsValue (fun i : Fin w => y.getLsbD i.val)).toNat then (1:F) else 0) = _
  rw [ExactQuantumFactoring.bitsValue_bits, ExactQuantumFactoring.bitsValue_bits]

theorem less_size (F : Type*) [Zero F] [One F] (w : ℕ) :
    (less F w).cells+(less F w).internal ≤ 177*(w+2) := by
  change (compareBits F w).cells+(compareBits F w).internal ≤ _
  rw [compareBits_cells, compareBits_internal]
  omega


end
end Hierarchy.Tagged.AlignWord

end OAI
