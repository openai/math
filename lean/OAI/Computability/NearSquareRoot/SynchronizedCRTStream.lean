import OAI.Computability.NearSquareRoot.SynchronizedRecordStream
import OAI.Computability.NearSquareRoot.CRTBalanced

/-! # Routing dense streams into the padded Fourier array and back

The CRT permutation here is the balanced recursive construction. Conjugating by
the physical tape address equivalence relates the mask and record scans to the
tensor's residue coordinates on both the occupied and unoccupied slots.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open SynchronizedPadding ResidueFourier
noncomputable section

variable {box : List (ℕ × ℕ)} {k l : ℕ} (hb : BoxShape.Valid k l box)
    [∀ i, NeZero (modulus box i)] [NeZero (∏ i, modulus box i)]

/-- The balanced CRT permutation acting on flat tape addresses. -/
def crtSlotPerm : Equiv.Perm (Fin (2^k)) :=
  ((recordIndex hb).symm.trans
    (CRT.paddedPermutation (modulus box) (fun i => Fin (padding box i)))).trans (recordIndex hb)

/-- Physical residue-format address where the natural-rank digit is sent. -/
def residueSlot (t : Fin (∏ i, modulus box i)) : Fin (2^k) :=
  recordIndex hb (occupied (fun i => Fin (padding box i))
    (CRT.scaled _ (pairwise hb) (ZMod.finEquiv _ t)))

private theorem finEquiv_val {n : ℕ} [NeZero n] (i : Fin n) : (ZMod.finEquiv _ i).val = i.val := by
  cases n <;> first | exact Fin.elim0 i | rfl

private theorem finEquiv_cast {n : ℕ} [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  apply ZMod.val_injective
  rw [finEquiv_val, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]

theorem crtSlotPerm_digitSlot (t : Fin (∏ i, modulus box i)) :
    crtSlotPerm hb (digitSlot hb t) = residueSlot hb t := by
  let u := finPiFinEquiv.symm t
  change recordIndex hb (CRT.paddedPermutation _ _ ((recordIndex hb).symm ((recordIndex hb)
    (fun i => Sum.inl (ZMod.finEquiv _ (u i)))))) = _
  rw [Equiv.symm_apply_apply, CRT.paddedPermutation_valid (pairwise hb)]
  have castRank : (CRT.rank (modulus box) (fun i => (ZMod.finEquiv _ (u i)).val) : ZMod _) =
      ZMod.finEquiv (∏ i, modulus box i) t := by
    simp only [finEquiv_val]
    rw [CRT.rank_eq_finPiFinEquiv, finEquiv_cast t]
    simp [u]
  rw [castRank]
  rfl

/-- An arbitrary compact payload array becomes the exact zero-extended tensor after
the scan and the forward CRT permutation. -/
theorem scatter_after_crt {A : Type} [Zero A] (f : Fin (∏ i, modulus box i) → A) :
    scatter hb 0 f ∘ (crtSlotPerm hb).symm =
      zeroExtend (fun i => Fin (padding box i))
        (f ∘ (ZMod.finEquiv _).symm ∘ (CRT.scaled _ (pairwise hb)).symm) ∘
          (recordIndex hb).symm := by
  let E := CRT.scaled _ (pairwise hb)
  funext j
  dsimp only [Function.comp_apply]
  by_cases hj : j ∈ Set.range (residueSlot hb)
  · obtain ⟨t,rfl⟩ := hj
    have h₁ : (crtSlotPerm hb).symm (residueSlot hb t) = digitSlot hb t := by
      rw [← crtSlotPerm_digitSlot, Equiv.symm_apply_apply]
    rw [h₁, scatter, (digitSlot_strictMono hb).injective.extend_apply]
    simp [residueSlot, zeroExtend_occupied]
  · have h₁ : (crtSlotPerm hb).symm j ∉ Set.range (digitSlot hb) := by
      rintro ⟨t, ht⟩
      exact hj ⟨t, (crtSlotPerm_digitSlot hb t).symm.trans ((Equiv.eq_symm_apply _).mp ht)⟩
    have h₂ : (recordIndex hb).symm j ∉ Set.range
        (occupied (A := fun i => ZMod (modulus box i)) (fun i => Fin (padding box i))) := by
      rintro ⟨z,hz⟩
      apply hj
      use (ZMod.finEquiv _).symm (E.symm z)
      simpa only [residueSlot, RingEquiv.apply_symm_apply, E, AddEquiv.apply_symm_apply] using
        ((Equiv.eq_symm_apply _).mp hz)
    rw [scatter, Function.extend_apply' _ _ _ h₁, zeroExtend_off _ _ h₂]

/-- After the inverse CRT, the physical compression reads any residue-array result in
ordinary rank order, even if its unused entries contain arbitrary values. -/
theorem compress_after_inverse_crt {A : Type} (dummy : A) (g : Fin (2^k) → A) :
    BoxMaskedRecords.compress dummy (BoxOrder.expand (BoxOrder.shape box),
      List.ofFn (g ∘ crtSlotPerm hb)) = List.ofFn (g ∘ residueSlot hb) := by
  rw [compress_dense hb]
  congr 1
  funext t
  simp [Function.comp_def, crtSlotPerm_digitSlot hb]

end
end BoxFin

end NearSquareRoot
end Computability
end OAI
