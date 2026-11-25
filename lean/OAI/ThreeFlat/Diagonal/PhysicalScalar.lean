import OAI.ThreeFlat.Diagonal.PhysicalBlock

namespace OAI
/-! # The scalar identity summed over a block's consistent fixings -/

namespace ThreeFlat.Diagonal

variable {F S A I : Type*} [Field F] [Fintype S] [DecidableEq S] [Inhabited S]
  [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I] {n : ℕ}

/-- Sum the scalar-identity fixings of the actual block. Unchanged bits
have an identity matrix; the touched bits determine the inputs of the
ordered product of the auxiliary transition matrices. -/
theorem scalar_fixings_entry (atSlot : Fin n → I) (active : Bool)
    (tick : Fin n → S → S → Matrix A A F) (x y : MachineState I S A) :
    (∑ f : BlockFixing n S A,
      physicalFixing atSlot active f (fixingWeight tick f • (1 : Matrix (I → S) (I → S) F))) x y =
      if x.1 (!active) = y.1 (!active) ∧
          (∀ i ∉ Finset.univ.image atSlot, x.1 active i = y.1 active i) then
        (List.ofFn fun i => tick i (x.1 active (atSlot i)) (y.1 active (atSlot i))).prod x.2 y.2
      else 0 := by
  classical
  rw [Matrix.sum_apply]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (x.1 active ∘ atSlot)]
  rotate_left
  · intro z _ hz
    simp [physicalFixing, physical_fixing_entry, touchedEnd, Ne.symm hz]
  · simp
  rw [Finset.sum_eq_single (y.1 active ∘ atSlot)]
  rotate_left
  · intro z _ hz
    simp [physicalFixing, physical_fixing_entry, touchedEnd, Ne.symm hz]
  · simp
  rw [Finset.sum_eq_single x.2]
  rotate_left
  · intro z _ hz
    simp [physicalFixing, physical_fixing_entry, touchedEnd, Ne.symm hz]
  · simp
  simp only [physicalFixing, physical_fixing_entry, touchedEnd, Prod.mk.injEq,
    true_and, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  by_cases outside : ∀ i, (¬ ∃ j, atSlot j = i) → x.1 active i = y.1 active i
  · replace outside := propext (iff_true_intro outside)
    by_cases inactive : x.1 (!active) = y.1 (!active)
    · simp only [outside, inactive, and_true, ite_true, mul_one]
      rw [← sum_auxPathWeight n _ x.2 y.2]
      apply Finset.sum_congr rfl
      intro v _
      rw [auxPathWeight_eq]
      by_cases last : endWord n x.2 v = y.2 <;>
        simp only [eq_comm (a := y.2), last, fixingWeight, Function.comp_def, ite_true, ite_false]
    · simp only [inactive, false_and, ite_false, mul_zero, ite_self, Finset.sum_const_zero]
  · replace outside := propext (iff_false_intro outside)
    simp only [outside, and_false, ite_false, Finset.sum_const_zero]

end ThreeFlat.Diagonal

end OAI
