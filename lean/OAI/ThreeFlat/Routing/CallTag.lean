import OAI.ThreeFlat.Routing.CallPermutation
import OAI.ThreeFlat.Routing.SwitchPins
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Identification words for completed switch tags

Active positions carry a common identifier for their unit. Each idle position
carries the number of idle positions strictly before it. Equality of these
words along every proposed tag uniquely determines the completed permutation.
-/

namespace ThreeFlat.Routing.CallPool

open scoped Classical

noncomputable section
variable {A B : Type*} [Fintype A] {m : ℕ}

/-- Encode any prescribed unit numbering into a word of address bits. -/
def identifierBits {d : ℕ} (number : A ↪ Fin (2^d)) : A ↪ (Fin d → Bool) :=
  number.trans (addressEquiv d).symm.toEmbedding

/-- A common binary unit identifier exists as soon as the chosen word width
can represent every unit. -/
def identifiersOfCardLe {d : ℕ} (h : Fintype.card A ≤ 2^d) : A ↪ (Fin d → Bool) :=
  identifierBits ((Fintype.equivFin A).toEmbedding.trans (Fin.castLEEmb h))

/-- Count idle positions preceding the given address. -/
def idlePrefix (f : A ↪ Fin m) (i : Fin m) : ℕ :=
  ((Finset.Iio i).filter fun t => t ∉ Set.range f).card

theorem idlePrefix_le (f : A ↪ Fin m) (i : Fin m) : idlePrefix f i ≤ i.val := by
  simpa only [idlePrefix, Fin.card_Iio] using
    (Finset.card_filter_le (s := Finset.Iio i) (fun t => t ∉ Set.range f))

theorem idlePrefix_strict (f : A ↪ Fin m) {i j : Fin m} (h : i ∉ Set.range f) (lt : i < j) :
    idlePrefix f i < idlePrefix f j := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨ha, hb⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr ((Finset.mem_Iio.mp ha).trans lt), hb⟩
  · intro eq
    have yes : i ∈ (Finset.Iio j).filter (fun t => t ∉ Set.range f) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr lt,h⟩
    rw [← eq] at yes
    exact (lt_irrefl i) (Finset.mem_Iio.mp (Finset.mem_filter.mp yes).1)

theorem idlePrefix_orderIso (L R : A ↪ Fin m) (x : {x : Fin m // x ∉ Set.range L}) :
    idlePrefix L x = idlePrefix R (idleOrderIso L R x) := by
  let e := idleOrderIso L R
  change ((Finset.Iio x.val).filter _).card = ((Finset.Iio (e x).val).filter _).card
  apply Finset.card_bij (fun a h => (e ⟨a,(Finset.mem_filter.mp h).2⟩).val)
  · intro a ha
    let a' : {x : Fin m // x ∉ Set.range L} := ⟨a,(Finset.mem_filter.mp ha).2⟩
    have lt : a < x.val := Finset.mem_Iio.mp (Finset.mem_filter.mp ha).1
    have ord : a' < x := lt
    exact Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr (show (e a').val < (e x).val from e.strictMono ord),
      (e a').property⟩
  · intro a ha b hb eq
    exact congrArg Subtype.val (e.injective (Subtype.ext eq))
  · intro b hb
    let b' : {x : Fin m // x ∉ Set.range R} := ⟨b,(Finset.mem_filter.mp hb).2⟩
    have lt : e.symm b' < x := (e.lt_iff_lt).mp (by
      rw [e.apply_symm_apply]
      exact (show b < (e x).val from Finset.mem_Iio.mp (Finset.mem_filter.mp hb).1))
    exact ⟨(e.symm b').val, Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr (show (e.symm b').val < x.val from lt),(e.symm b').property⟩,
      congrArg Subtype.val (e.apply_symm_apply b')⟩

/-- The left summand names active units. The right summand numbers idle slots. -/
def unitLabel (ids : A ↪ B) (f : A ↪ Fin m) (i : Fin m) : B ⊕ Fin m :=
  if h : i ∈ Set.range f then .inl (ids ((Equiv.ofInjective f f.injective).symm ⟨i,h⟩))
  else .inr ⟨idlePrefix f i,(idlePrefix_le f i).trans_lt i.isLt⟩

@[simp] theorem unitLabel_active (ids : A ↪ B) (f : A ↪ Fin m) (a : A) :
    unitLabel ids f (f a) = .inl (ids a) := by
  have h : f a ∈ Set.range f := ⟨a,rfl⟩
  simp only [unitLabel,dite_eq_left h]
  change Sum.inl (ids ((Equiv.ofInjective f f.injective).symm ((Equiv.ofInjective f f.injective) a))) = _
  rw [Equiv.symm_apply_apply]

theorem unitLabel_injective (ids : A ↪ B) (f : A ↪ Fin m) : Function.Injective (unitLabel ids f) := by
  intro i j h
  by_cases hi : i ∈ Set.range f <;> by_cases hj : j ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hi
    obtain ⟨b,rfl⟩ := hj
    simp only [unitLabel_active, Sum.inl.injEq] at h
    exact congrArg f (ids.injective h)
  · simp [unitLabel,hi,hj] at h
  · simp [unitLabel,hi,hj] at h
  · have n : idlePrefix f i = idlePrefix f j := by
      exact congrArg Fin.val (Sum.inr.inj (by simpa only [unitLabel,dite_eq_right hi,dite_eq_right hj] using h))
    exact le_antisymm (le_of_not_gt fun lt => (idlePrefix_strict f hj lt).ne n.symm)
      (le_of_not_gt fun lt => (idlePrefix_strict f hi lt).ne n)

theorem unitLabel_complete (ids : A ↪ B) (L R : A ↪ Fin m) (i : Fin m) :
    unitLabel ids R (completePermutation L R i) = unitLabel ids L i := by
  by_cases hi : i ∈ Set.range L
  · obtain ⟨a,rfl⟩ := hi
    simp only [completePermutation_active,unitLabel_active]
  · rw [completePermutation_idle L R i hi]
    simp only [unitLabel, dite_eq_right hi, dite_eq_right (idleOrderIso L R ⟨i,hi⟩).property]
    exact congrArg Sum.inr (Fin.ext (idlePrefix_orderIso L R ⟨i,hi⟩).symm)

theorem routed_unitLabel_iff (ids : A ↪ B) (L R : A ↪ Fin m) (tag : Fin m → Fin m) :
    Routed tag (unitLabel ids L) (unitLabel ids R) ↔ tag = ⇑(completePermutation L R) := by
  constructor
  · intro h
    funext i
    exact unitLabel_injective ids R ((h.2 i).trans (unitLabel_complete ids L R i).symm)
  · rintro rfl
    exact ⟨(completePermutation L R).bijective,unitLabel_complete ids L R⟩

/-- The metadata verifier accepts exactly one choice of proposed destinations. -/
theorem taggedSwitch_unitLabel (F : Type*) [Zero F] [One F] (ids : A ↪ B)
    (L R : A ↪ Fin m) {V : Type*} (code : (B ⊕ Fin m) ↪ V) (tag : Fin m → Fin m) :
    taggedSwitch F tag (code ∘ unitLabel ids L) (code ∘ unitLabel ids R) =
      if tag = ⇑(completePermutation L R) then 1 else 0 := by
  have same : Routed tag (code ∘ unitLabel ids L) (code ∘ unitLabel ids R) ↔
      Routed tag (unitLabel ids L) (unitLabel ids R) := by
    simp only [Routed, Function.comp_apply, code.injective.eq_iff]
  simp only [taggedSwitch,same,routed_unitLabel_iff]

end
end ThreeFlat.Routing.CallPool

end OAI
