import OAI.Computability.NearSquareRoot.SynchronizedPhysicalBits

/-! # Spectator coordinates in the flat selected Walsh transform -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open Finset SynchronizedBlocks ShortFourier

variable {box : List (ℕ × ℕ)} {k L : ℕ} (hb : BoxShape.Valid k L box)

/-- All axis-bit positions form the ordinary interval of physical address bits. -/
def bitPosition : (Σ i : Fin box.length, Fin (box.get i).1) ≃ Fin k :=
  finSigmaFinEquiv.trans (finCongr ((Fin.sum_univ_fun_getElem box Prod.fst).trans hb.widthSum))

theorem bitPosition_val (i : Fin box.length) (q : Fin (box.get i).1) :
    (bitPosition hb ⟨i,q⟩).val = offset i + q.val := by
  simp [bitPosition, offset]

private def highBit (i : Fin box.length) : Fin (box.get i).1 :=
  ⟨(box.get i).1-1, Nat.sub_lt (hb.axisBounds _ (List.get_mem _ i)).1 (by decide)⟩

private theorem bitPosition_high (j : Fin (box.length / 4)) :
    bitPosition hb ⟨axis j (firstAxis j), highBit hb _⟩ = selectedPosition hb j :=
  Fin.ext (bitPosition_val ..)

private theorem mem_selected_iff (hd : 4 ≤ box.length) (active : Finset (Fin (box.length/4)))
    (j : Fin (box.length/4)) (i : Fin (count j)) (q : Fin (box.get (axis j i)).1) :
    bitPosition hb ⟨axis j i,q⟩ ∈ active.image (selectedPosition hb) ↔
      j ∈ active ∧ i = firstAxis j ∧ q = highBit hb _ := by
  constructor
  · rintro h
    obtain ⟨m,hm,he⟩ := mem_image.mp h
    rw [← bitPosition_high hb] at he
    have hs := (bitPosition hb).injective he
    have ha := congrArg Sigma.fst hs
    have hj : m = j := by simpa only [block_axis] using congrArg (SynchronizedBlocks.block hd) ha
    subst m
    have hi : i = firstAxis j := by
      have := congrArg Fin.val ha
      change 4*j.val+(firstAxis j).val = 4*j.val+i.val at this
      exact Fin.ext (by omega)
    subst i
    exact ⟨hm,rfl,(Sigma.mk.inj hs).2.eq.symm⟩
  · rintro ⟨hm,rfl,rfl⟩
    exact mem_image.mpr ⟨j,hm,(bitPosition_high hb j).symm⟩

private theorem testBit_mod_iff {a b n : ℕ} :
    a % 2^n = b % 2^n ↔ ∀ q < n, a.testBit q = b.testBit q := by
  constructor
  · intro he q hq
    simpa only [Nat.testBit_mod_two_pow,decide_eq_true hq,Bool.true_and] using
      congrArg (fun t : ℕ => t.testBit q) he
  · intro h
    apply Nat.eq_of_testBit_eq
    intro q
    by_cases hq : q < n <;> simp [Nat.testBit_mod_two_pow,hq, h]

variable [∀ i, NeZero (modulus box i)]

private theorem field_eq_iff (x y : (i : Fin box.length) → BoxAxis box i) (i : Fin box.length) :
    x i = y i ↔ ∀ q : Fin (box.get i).1,
      (field hb i (x i)).val.testBit q.val = (field hb i (y i)).val.testBit q.val := by
  constructor
  · rintro he q
    rw [he]
  · intro h
    apply (field hb i).injective
    apply Fin.ext
    have he := (testBit_mod_iff (n := (box.get i).1)).mpr (fun q hq => h ⟨q,hq⟩)
    simpa only [Nat.mod_eq_of_lt (field hb i (x i)).isLt, Nat.mod_eq_of_lt (field hb i (y i)).isLt] using he

/-- Physical addresses agree at every bit outside the chosen Walsh set. -/
def offBits (active : Finset (Fin k)) (x y : Fin (2^k)) : Prop :=
  ∀ p : Fin k, p ∉ active → x.val.testBit p.val = y.val.testBit p.val

private def offFields (active : Finset (Fin (box.length/4)))
    (x y : (i : Fin box.length) → BoxAxis box i) : Prop :=
  ∀ (j : Fin (box.length/4)) (i : Fin (count j)) (q : Fin (box.get (axis j i)).1),
    ¬ (j ∈ active ∧ i = firstAxis j ∧ q = highBit hb _) →
    (field hb _ (x (axis j i))).val.testBit q.val = (field hb _ (y (axis j i))).val.testBit q.val

private theorem offFields_iff (hd : 4 ≤ box.length) (active : Finset (Fin (box.length/4)))
    (x y : (i : Fin box.length) → BoxAxis box i) :
    offFields hb active x y ↔ offBits (active.image (selectedPosition hb)) (recordIndex hb x) (recordIndex hb y) := by
  constructor
  · intro h p
    obtain ⟨⟨a,q⟩,rfl⟩ := (bitPosition hb).surjective p
    obtain ⟨⟨j,i⟩,rfl⟩ := (coordinates hd).surjective a
    change bitPosition hb ⟨axis j i,q⟩ ∉ _ → _
    intro hn
    have he := h j i q (mt (mem_selected_iff hb hd active j i q).mpr hn)
    rw [testBit_field hb x (axis j i) q.isLt,testBit_field hb y (axis j i) q.isLt] at he
    rw [bitPosition_val]
    exact he
  · intro h j i q hn
    have he := h (bitPosition hb ⟨axis j i,q⟩) (mt (mem_selected_iff hb hd active j i q).mp hn)
    simpa only [bitPosition_val, testBit_field hb x _ q.isLt, testBit_field hb y _ q.isLt] using he

private theorem sameFiber_offFields (hd : 4 ≤ box.length) (active : Finset (Fin (box.length/4)))
    (x y : (i : Fin box.length) → BoxAxis box i) :
    SynchronizedSelected.sameFiber active (boxBits hb) (regroup hd _ x) (regroup hd _ y) ↔ offFields hb active x y := by
  constructor
  · intro h j i q hn
    have he := h j
    by_cases hj : j ∈ active
    · rw [ite_eq_left hj] at he
      by_cases hi : i = firstAxis j
      · subst i
        have hq : q.val < (box.get (axis j (firstAxis j))).1-1 := by
          have hne : q ≠ highBit hb _ := fun hh => hn ⟨hj,rfl,hh⟩
          have hne' : q.val ≠ (box.get (axis j (firstAxis j))).1-1 := fun hh => hne (Fin.ext hh)
          have := q.isLt
          omega
        have hlo := congrArg (fun t => t.1.val) he
        exact (testBit_mod_iff.mp hlo) _ hq
      · have hh := congrFun (congrArg Prod.snd he) ⟨i,hi⟩
        exact (field_eq_iff hb x y _).mp hh q
    · rw [ite_eq_right hj] at he
      exact (field_eq_iff hb x y _).mp (congrFun he i) q
  · intro h j
    by_cases hj : j ∈ active
    · rw [ite_eq_left hj]
      apply Prod.ext
      · apply Fin.ext
        apply testBit_mod_iff.mpr
        intro q hq
        change q < (box.get (axis j (firstAxis j))).1-1 at hq
        have hw : q < (box.get (axis j (firstAxis j))).1 := by omega
        exact h j (firstAxis j) ⟨q,hw⟩ (fun ⟨_,_,hh⟩ => by
          have hv := congrArg Fin.val hh
          change q = (box.get (axis j (firstAxis j))).1-1 at hv
          omega)
      · funext i
        exact (field_eq_iff hb x y _).mpr (fun q => h j i q (fun he => i.property he.2.1))
    · rw [ite_eq_right hj]
      funext i
      exact (field_eq_iff hb x y _).mpr (fun q => h j i q (fun he => hj he.1))

/-- The physical Walsh fiber is exactly the one used by the synchronized tensor. -/
theorem sameFiber_physical (hd : 4 ≤ box.length) (active : Finset (Fin (box.length/4)))
    (x y : (i : Fin box.length) → BoxAxis box i) :
    SynchronizedSelected.sameFiber active (boxBits hb) (regroup hd _ x) (regroup hd _ y) ↔
      offBits (active.image (selectedPosition hb)) (recordIndex hb x) (recordIndex hb y) :=
  (sameFiber_offFields hb hd active x y).trans (offFields_iff hb hd active x y)

/-- The number of physical Walsh signs contributed at two record addresses. -/
def physicalOverlap (bits : Finset (Fin k)) (x y : Fin (2^k)) : ℕ :=
  (bits.filter fun p => x.val.testBit p.val ∧ y.val.testBit p.val).card

theorem overlap_physical (hd : 4 ≤ box.length) (active : Finset (Fin (box.length/4)))
    (x y : (i : Fin box.length) → BoxAxis box i) :
    SynchronizedSelected.overlap active (boxBits hb) (regroup hd _ x) (regroup hd _ y) =
      physicalOverlap (active.image (selectedPosition hb)) (recordIndex hb x) (recordIndex hb y) := by
  classical
  unfold SynchronizedSelected.overlap physicalOverlap
  rw [filter_image, card_image_of_injective _ (selectedPosition_strictMono hb).injective]
  congr 1
  apply filter_congr
  intro j _
  have h (z : (i : Fin box.length) → BoxAxis box i) :
      (boxBits hb j (regroup hd _ z j)).1 = 1 ↔
        (recordIndex hb z).val.testBit (selectedPosition hb j).val := by
    rw [← boxBits_physical hb hd z j]
    simp [Fin.ext_iff,boxBits]
  exact and_congr (h x) (h y)

/-- Flat normalized Walsh matrix on an arbitrary selected set of binary tape-address bits. -/
noncomputable def flatWalsh (bits : Finset (Fin k)) : Matrix (Fin (2^k)) (Fin (2^k)) ℂ :=
  by
    classical
    exact Matrix.of (fun x y => if offBits bits x y then
      (SynchronizedPair.w : ℂ)^bits.card * (-1)^physicalOverlap bits x y else 0)

/-- The synchronized tensor Walsh layer acts entrywise as the ordinary selected-bit Walsh
matrix on the original linear record tape, on every spectator fiber. -/
theorem tensorWalsh_physical (hd : 4 ≤ box.length) (active : Finset (Fin (box.length/4))) :
    (SynchronizedPadding.tensorMatrix (SynchronizedSelected.block active (boxBits hb))).submatrix
      (regroup hd _) (regroup hd _) =
      (flatWalsh (active.image (selectedPosition hb))).submatrix (recordIndex hb) (recordIndex hb) := by
  classical
  ext x y
  simp only [Matrix.submatrix_apply, flatWalsh, Matrix.of_apply, SynchronizedSelected.tensorMatrix_block_apply]
  rw [overlap_physical hb hd, card_image_of_injective _ (selectedPosition_strictMono hb).injective]
  exact if_congr (sameFiber_physical hb hd active x y) rfl rfl

end BoxFin

end NearSquareRoot
end Computability
end OAI
