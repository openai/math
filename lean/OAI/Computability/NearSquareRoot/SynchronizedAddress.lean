import OAI.Computability.NearSquareRoot.BoxFin
import OAI.Computability.NearSquareRoot.CRTIsomorphism
import OAI.Computability.NearSquareRoot.SynchronizedRecovery

/-! # Lexicographic tape addresses for the padded residue tensor

Axis zero varies fastest. Encoding a valid coordinate places its residue before
the padded tail. The inverse extracts the coordinate's contiguous bit field by a
division and a reduction modulo the axis's power of two.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

variable {box : List (ℕ × ℕ)} {k l : ℕ} (hb : BoxShape.Valid k l box)
    [∀ i, NeZero (modulus box i)]

omit [∀ i, NeZero (modulus box i)] in
private theorem localSize (hb : BoxShape.Valid k l box) (i : Fin box.length) :
    modulus box i + padding box i = 2^(box.get i).1 :=
  Nat.add_sub_of_le (hb.axisBounds _ (List.get_mem box i)).2.2.2

/-- Valid symbols occupy the initial segment of the local axis. -/
def field (i : Fin box.length) :
    ZMod (modulus box i) ⊕ Fin (padding box i) ≃ Fin (2^(box.get i).1) :=
  ((ZMod.finEquiv _).symm.toEquiv.sumCongr (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (localSize hb i)))

omit [∀ i, NeZero (modulus box i)] in
private theorem numRecords (hb : BoxShape.Valid k l box) : (∏ i : Fin box.length, 2^(box.get i).1) = 2^k := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  exact (Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum

/-- The actual scalar address of the padded product, from the first tape record. -/
def recordIndex : ResidueFourier.PaddedBox (modulus box) (padding box) ≃ Fin (2^k) :=
  (Equiv.piCongrRight (field hb)).trans (finPiFinEquiv.trans (finCongr (numRecords hb)))

/-- Bit offset of the low end of a field. -/
def offset (i : Fin box.length) : ℕ := ∑ j : Fin i.val, (box.get (Fin.castLE i.isLt.le j)).1

theorem recordIndex_val (x : ResidueFourier.PaddedBox (modulus box) (padding box)) :
    (recordIndex hb x).val = ∑ i, (field hb i (x i)).val * 2^(offset i) := by
  change (finPiFinEquiv (fun i => field hb i (x i))).val = _
  simp [finPiFinEquiv_apply, Finset.prod_pow_eq_pow_sum, offset]

theorem extract_field (t : Fin (2^k)) (i : Fin box.length) :
    (field hb i ((recordIndex hb).symm t i)).val =
      (t.val / 2^(offset i)) % (2^(box.get i).1) := by
  change (field hb i ((field hb i).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  change t.val / (∏ j : Fin i.val, 2^(box.get (Fin.castLE i.isLt.le j)).1) %
    2^(box.get i).1 = _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem field_inl (i : Fin box.length) (x : ZMod (modulus box i)) :
    (field hb i (.inl x)).val = ((ZMod.finEquiv _).symm x).val := rfl

theorem field_inr (i : Fin box.length) (t : Fin (padding box i)) :
    (field hb i (.inr t)).val = modulus box i + t.val := rfl

/-- The record belongs to the occupied tensor exactly when all extracted
fields are smaller than their local moduli. -/
theorem occupied_iff (t : Fin (2^k)) :
    (recordIndex hb).symm t ∈ Set.range
      (SynchronizedPadding.occupied (A := fun i => ZMod (modulus box i)) (fun i => Fin (padding box i))) ↔
    ∀ i : Fin box.length, (t.val / 2^(offset i)) % 2^(box.get i).1 < modulus box i := by
  simp_rw [← extract_field hb t]
  constructor
  · rintro ⟨x, hx⟩ i
    rw [← hx]
    exact ((ZMod.finEquiv _).symm (x i)).isLt
  · intro H
    have h (i : Fin box.length) : ∃ z, ((recordIndex hb).symm t i) = Sum.inl z := by
      cases he : (recordIndex hb).symm t i with
      | inl z => exact ⟨z, rfl⟩
      | inr z =>
        have h' := H i
        rw [he, field_inr] at h'
        omega
    exact ⟨fun i => (h i).choose, funext fun i => (h i).choose_spec.symm⟩

end BoxFin

end NearSquareRoot
end Computability
end OAI
