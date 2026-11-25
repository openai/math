import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic
import OAI.Computability.VPVNP.GrassmannTypes

namespace OAI
/-!
# Rigidity of Grassmann distance classes

Frames of size strictly below the ambient dimension are connected by changes
of one column to a vector outside the current span. Changing a common column
of two coordinate planes gives a Grassmann square. For an exclusive column,
first use a common column to store the difference between the old and new
entries. Opposite-side equality on squares then makes every type-`r`
distance constant whenever `r<m`.
-/

namespace Computability.VPVNP.Grassmann.Rigidity

open Submodule Function

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype I] [DecidableEq I]

/-- An ordered independent family of vectors. -/
abbrev Frame (K V I : Type*) [Semiring K] [AddCommMonoid V] [Module K V] :=
  {f : I → V // LinearIndependent K f}

omit [Fintype I] in
/-- A fresh vector may be substituted at any one column of a frame. -/
theorem independent_update {f : I → V} (hf : LinearIndependent K f) (i : I)
    (z : V) (hz : z ∉ span K (Set.range f)) :
    LinearIndependent K (Function.update f i z) := by
  let j (k : I) : Option I := if k = i then none else some k
  have hj : Function.Injective j := by
    intro a b h
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp_all [j]
  have eq : Function.update f i z = (fun o => Option.casesOn' o z f) ∘ j := by
    funext k
    by_cases hk : k = i <;> simp [j, hk, Function.update]
  rw [eq]
  exact (hf.option hz).comp j hj

def fresh (f : Frame K V I) (i : I) (z : V) (hz : z ∉ span K (Set.range f.val)) :
    Frame K V I :=
  ⟨Function.update f.val i z, independent_update f.property i z hz⟩

private theorem outside (A : Submodule K V) (hA : A < ⊤) : ∃ x, x ∉ A := by
  by_contra! h
  exact hA.ne (top_unique (fun v _ => h v))

/-- Two proper subspaces have a common outside vector, including over the binary field. -/
theorem outside_both (A B : Submodule K V) (hA : A < ⊤) (hB : B < ⊤) :
    ∃ z, z ∉ A ∧ z ∉ B := by
  obtain ⟨a, ha⟩ := outside A hA
  obtain ⟨b, hb⟩ := outside B hB
  by_cases hab : a ∈ B
  · by_cases hba : b ∈ A
    · refine ⟨a+b, ?_, ?_⟩
      · intro h
        exact ha (by simpa using A.sub_mem h hba)
      · intro h
        exact hb (by simpa [add_comm a b] using B.sub_mem h hab)
    · exact ⟨b, hba, hb⟩
  · exact ⟨a, ha, hab⟩

/-- An invariant of frames that survives every fresh change in the allowed
columns is constant on frames agreeing on the other columns. -/
theorem eq_of_fresh_invariant [FiniteDimensional K V] {Y : Type*}
    (small : Fintype.card I < Module.finrank K V) (score : Frame K V I → Y)
    (allowed : I → Prop)
    (step : ∀ f i, allowed i → ∀ z hz, score (fresh f i z hz) = score f)
    (f g : Frame K V I) (agree : ∀ i, ¬allowed i → f.val i = g.val i) :
    score f = score g := by
  classical
  have aux (s : Finset I) (hs : ∀ i ∈ s, allowed i) (f g : Frame K V I)
      (agree : ∀ i ∉ s, f.val i = g.val i) : score f = score g := by
    induction s using Finset.induction_on generalizing f g with
    | empty =>
      exact congrArg score (Subtype.ext (funext (fun i => agree i (by simp))))
    | @insert i s hi ih =>
      have lt (k : Frame K V I) : span K (Set.range k.val) < ⊤ :=
        Submodule.lt_top_of_finrank_lt_finrank ((finrank_span_eq_card k.property).trans_lt small)
      obtain ⟨z, hzf, hzg⟩ := outside_both _ _ (lt f) (lt g)
      rw [← step f i (hs _ (Finset.mem_insert_self ..)) z hzf,
          ← step g i (hs _ (Finset.mem_insert_self ..)) z hzg]
      apply ih (fun j hj => hs _ (Finset.mem_insert_of_mem hj))
      intro k hk
      by_cases hki : k = i
      · subst k
        simp [fresh]
      · simpa [fresh, Function.update_of_ne hki] using agree k (by simp [hki, hk])
  apply aux (Finset.univ.filter allowed)
  · simp
  · intro i hi
    exact agree i (by simpa using hi)

end Computability.VPVNP.Grassmann.Rigidity

/-! # Grassmann squares from changing a common column -/

namespace Computability.VPVNP.Grassmann.Rigidity

open Submodule Function

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype I] [DecidableEq I]

def block (f : I → V) (A : Finset I) : Submodule K V := span K (f '' (A : Set I))

omit [Fintype I] [DecidableEq I] in
theorem finrank_block (f : Frame K V I) (A : Finset I) :
    Module.finrank K (block f.val A : Submodule K V) = A.card := by
  have e : f.val '' (A : Set I) = Set.range (f.val ∘ ((↑) : A → I)) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.property, rfl⟩
  rw [block, e, finrank_span_eq_card (f.property.comp _ Subtype.val_injective), Fintype.card_coe]

omit [Fintype I] in
theorem block_union (f : I → V) (A B : Finset I) :
    block f (A ∪ B) = (block f A ⊔ block f B : Submodule K V) := by
  simp [block, Set.image_union, Submodule.span_union]

omit [AddCommGroup V] [Fintype I] in
private theorem union_update (f : I → V) (i : I) (z : V) (A B : Finset I)
    (ha : i ∈ A) (hb : i ∈ B) :
    (f '' (A : Set I)) ∪ (update f i z '' (B : Set I)) =
      (f '' (↑(A ∪ B) : Set I)) ∪ {z} := by
  ext x
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
    · exact Or.inl ⟨k, Finset.mem_union_left _ hk, rfl⟩
    · by_cases h : k = i
      · subst k
        simp
      · exact Or.inl ⟨k, Finset.mem_union_right _ hk, (update_of_ne h z f).symm⟩
  · rintro (⟨k, hk, rfl⟩ | rfl)
    · rcases Finset.mem_union.mp hk with hka | hkb
      · exact Or.inl ⟨_, hka, rfl⟩
      · by_cases h : k = i
        · exact Or.inl ⟨_, (by simpa [h] using ha), rfl⟩
        · exact Or.inr ⟨_, hkb, update_of_ne h z f⟩
    · exact Or.inr ⟨i, hb, update_self ..⟩

omit [Fintype I] in
theorem finrank_mixed (f : Frame K V I) (i : I) (z : V)
    (hz : z ∉ span K (Set.range f.val)) (A B : Finset I) (ha : i ∈ A) (hb : i ∈ B)
    [FiniteDimensional K V] :
    Module.finrank K (block f.val A ⊔ block (fresh f i z hz).val B : Submodule K V) =
      (A ∪ B).card + 1 := by
  have H : z ∉ (block f.val (A ∪ B) : Submodule K V) :=
    fun h => hz (span_mono (Set.image_subset_range ..) h)
  unfold block fresh
  rw [← Submodule.span_union, union_update _ _ _ A B ha hb, Submodule.span_union]
  exact (Submodule.finrank_sup_span_singleton H).trans (congrArg (· + 1) (finrank_block f (A ∪ B)))

variable {m : ℕ}

def plane (f : Frame (ZMod 2) (Space m) I) (A : Finset I) (hA : A.card = m) : Plane m :=
  ⟨block f.val A, (finrank_block f A).trans hA⟩

omit [Fintype I] in
theorem plane_pair_type (f : Frame (ZMod 2) (Space m) I) (A B : Finset I)
    (hA : A.card = m) (hB : B.card = m) (r : ℕ) (hAB : (A ∪ B).card = m + r) :
    HasType r (plane f A hA) (plane f B hB) := by
  unfold HasType plane
  rw [← block_union, finrank_block, hAB]

omit [Fintype I] in
theorem plane_update_square (f : Frame (ZMod 2) (Space m) I)
    (A B : Finset I) (hA : A.card = m) (hB : B.card = m) (r : ℕ)
    (hAB : (A ∪ B).card = m + r) (i : I) (ha : i ∈ A) (hb : i ∈ B)
    (z : Space m) (hz : z ∉ span (ZMod 2) (Set.range f.val)) :
    IsSquare r 1 (plane f A hA) (plane f B hB)
      (plane (fresh f i z hz) B hB) (plane (fresh f i z hz) A hA) := by
  refine ⟨plane_pair_type f A B hA hB r hAB, ?_, ?_, ?_, ?_, ?_⟩
  · exact (finrank_mixed f i z hz B B hb hb).trans (by rw [Finset.union_self, hB])
  · exact plane_pair_type _ B A hB hA r (Finset.union_comm A B ▸ hAB)
  · unfold HasType
    rw [sup_comm]
    exact (finrank_mixed f i z hz A A ha ha).trans (by rw [Finset.union_self, hA])
  · exact (finrank_mixed f i z hz A B ha hb).trans (by rw [hAB, Nat.add_assoc])
  · exact (finrank_mixed f i z hz B A hb ha).trans (by rw [Finset.union_comm B A, hAB, Nat.add_assoc])

end Computability.VPVNP.Grassmann.Rigidity

/-! # Equality rigidity under changes of the common and exclusive columns -/

namespace Computability.VPVNP.Grassmann.Rigidity

open Submodule Function

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem retired_fresh (f : Frame K V I) (i : I) (z : V)
    (hz : z ∉ span K (Set.range f.val)) :
    f.val i ∉ span K (Set.range (fresh f i z hz).val) := by
  let ext : Option I → V := fun o => Option.casesOn' o z f.val
  have h : LinearIndependent K ext := f.property.option hz
  have sub : Set.range (fresh f i z hz).val ⊆ ext '' {o : Option I | o ≠ some i} := by
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = i
    · subst k
      exact ⟨none, by simp, by simp [ext, fresh]⟩
    · exact ⟨some k, by simpa using hk, by simp [ext, fresh, hk]⟩
  exact fun mem => h.notMem_span_image (s := {o : Option I | o ≠ some i}) (x := some i)
    (by simp) (span_mono sub mem)

omit [Fintype I] [DecidableEq I] in
theorem mem_block (f : I → V) {i : I} {A : Finset I} (hi : i ∈ A) :
    f i ∈ (block f A : Submodule K V) := subset_span ⟨_, hi, rfl⟩

omit [Fintype I] in
/-- If two column entries differ by a common column, their selected spans coincide. -/
theorem block_eq_of_difference (f g : I → V) (A : Finset I) {i j : I}
    (hj : j ∈ A) (hji : j ≠ i) (same : ∀ k, k ≠ i → g k = f k)
    (diff : g i - f i = f j) : (block f A : Submodule K V) = block g A := by
  have fj : g j = f j := same j hji
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    by_cases hki : k = i
    · subst k
      have h : g i - g j = f i := by rw [fj, ← diff, sub_sub_cancel]
      rw [← h]
      exact (block g A).sub_mem (mem_block _ hk) (mem_block _ hj)
    · rw [← same k hki]
      exact mem_block _ hk
  · apply span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    by_cases hki : k = i
    · subst k
      rw [sub_eq_iff_eq_add.mp diff]
      exact (block f A).add_mem (mem_block _ hj) (mem_block _ hk)
    · rw [same k hki]
      exact mem_block _ hk

variable {m r : ℕ} (D : Plane m → Plane m → ℝ)

/-- Opposite-side equality on fresh changes of one common column extends
to all changes of frame. A single common column absorbs the difference
between old and new exclusive entries. -/
theorem distance_of_frame
    (symm : ∀ a b, D a b = D b a)
    (opposite : ∀ a b c d, IsSquare r 1 a b c d → D a b = D c d)
    (A B : Finset I) (hA : A.card = m) (hB : B.card = m)
    (hAB : (A ∪ B).card = m+r) (small : Fintype.card I < 2*m)
    (j : I) (ja : j ∈ A) (jb : j ∈ B)
    (f g : Frame (ZMod 2) (Space m) I) :
    D (plane f A hA) (plane f B hB) = D (plane g A hA) (plane g B hB) := by
  let score (k : Frame (ZMod 2) (Space m) I) := D (plane k A hA) (plane k B hB)
  have common (k : Frame (ZMod 2) (Space m) I) (i : I) (ia : i ∈ A) (ib : i ∈ B)
      (z : Space m) (hz : z ∉ span (ZMod 2) (Set.range k.val)) :
      score (fresh k i z hz) = score k := by
    exact (symm _ _).trans (opposite _ _ _ _ (plane_update_square k A B hA hB r hAB i ia ib z hz)).symm
  apply eq_of_fresh_invariant (by simpa only [Space, Module.finrank_pi, Fintype.card_fin] using small) score (fun _ => True) _ f g
    (by simp)
  intro k i _ z hz
  by_cases h : i = j
  · subst i
    exact common _ _ ja jb _ _
  let k' := fresh k i z hz
  let t := z - k.val i
  have zi : k'.val i = z := by simp [k', fresh]
  have ht : t ∉ span (ZMod 2) (Set.range k.val) := by
    intro hm
    have hki : k.val i ∈ span (ZMod 2) (Set.range k.val) := subset_span (Set.mem_range_self i)
    exact hz (by simpa [t] using (span (ZMod 2) (Set.range k.val)).add_mem hm hki)
  have ht' : t ∉ span (ZMod 2) (Set.range k'.val) := by
    intro hm
    apply retired_fresh k i z hz
    have memz : z ∈ span (ZMod 2) (Set.range k'.val) := subset_span ⟨i, zi⟩
    simpa [t] using (span (ZMod 2) (Set.range k'.val)).sub_mem memz hm
  let s := fresh k j t ht
  let s' := fresh k' j t ht'
  have same (n : I) (hn : n ≠ i) : s'.val n = s.val n := by
    by_cases hnj : n = j <;> simp [s', s, k', fresh, hnj, hn]
  have ds : s'.val i - s.val i = s.val j := by simp [s', s, k', fresh, h, t]
  have eqp (T : Finset I) (hT : T.card = m) (hj : j ∈ T) :
      plane s T hT = plane s' T hT :=
    Subtype.ext (block_eq_of_difference _ _ _ hj (Ne.symm h) same ds)
  calc
    score k' = score s' := (common k' j ja jb t ht').symm
    _ = score s := by unfold score; rw [eqp A hA ja, eqp B hB jb]
    _ = score k := common k j ja jb t ht

end Computability.VPVNP.Grassmann.Rigidity

/-! # Constancy on each nonmaximal Grassmann distance class -/

namespace Computability.VPVNP.Grassmann.Rigidity

open Submodule Function

private theorem reference {m r : ℕ} (hr : r < m) :
    ∃ (A B : Finset (Fin (m+r))), A.card = m ∧ B.card = m ∧
      (A ∪ B).card = m+r ∧ ∃ i, i ∈ A ∧ i ∈ B := by
  let l : Fin m ↪ Fin (m+r) := ⟨fun i => ⟨i, by omega⟩, fun _ _ h => Fin.ext (congrArg (@Fin.val (m+r)) h)⟩
  let u : Fin m ↪ Fin (m+r) :=
    ⟨fun i => ⟨r + i, by omega⟩, fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
  let A := Finset.univ.map l
  let B := Finset.univ.map u
  have cover : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_cases h : i.val < m
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨⟨i.val, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    · apply Finset.mem_union_right _
      apply Finset.mem_map.mpr
      refine ⟨⟨i.val-r, by have := i.isLt; omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      change r + (i.val-r) = i.val
      omega
  refine ⟨A, B, by simp [A], by simp [B], by simp [cover], ⟨r, by omega⟩, ?_, ?_⟩
  · exact Finset.mem_map.mpr ⟨⟨r, hr⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · exact Finset.mem_map.mpr ⟨⟨0, by omega⟩, Finset.mem_univ _, Fin.ext (Nat.add_zero r)⟩

/-- Opposite sides agreeing on the type-`(r,1)` squares forces every
individual entry of type `r<m` to equal the mean. -/
theorem distance_eq_mean_of_transitive {m r : ℕ}
    (transitive : ∀ p q : Pair m r, ∃ e : Computability.VPVNP.Grassmann.GL m, e • p = q) (hr : r < m) (D : Plane m → Plane m → ℝ)
    (symm : ∀ a b, D a b = D b a)
    (opposite : ∀ a b c d, IsSquare r 1 a b c d → D a b = D c d)
    (p : Pair m r) : D p.val.1 p.val.2 = mean D r := by
  obtain ⟨A,B,ha,hb,hab,j,hja,hjb⟩ := reference hr
  let embed : Fin (m+r) → Fin (2*m) := fun i => ⟨i, by have := i.isLt; omega⟩
  let f : Frame (ZMod 2) (Space m) (Fin (m+r)) :=
    ⟨_, (Pi.linearIndependent_single_one (Fin (2*m)) (ZMod 2)).comp embed
      (fun a b h => Fin.ext (congrArg (@Fin.val (2*m)) h))⟩
  let base : Pair m r := ⟨(plane f A ha, plane f B hb), plane_pair_type f A B ha hb r hab⟩
  have hq (q : Pair m r) : D q.val.1 q.val.2 = D base.val.1 base.val.2 := by
    obtain ⟨e, he⟩ := transitive base q
    let g : Frame (ZMod 2) (Space m) (Fin (m+r)) :=
      ⟨e ∘ f.val, f.property.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)⟩
    have map_plane (T : Finset (Fin (m+r))) (hT : T.card = m) :
        e • plane f T hT = plane g T hT := by
      apply Subtype.ext
      change (block f.val T).map e.toLinearMap = block (e ∘ f.val) T
      rw [block, block, Submodule.map_span, Set.image_image]
      rfl
    rw [← he]
    change D (e • plane f A ha) (e • plane f B hb) = D (plane f A ha) (plane f B hb)
    rw [map_plane, map_plane]
    exact distance_of_frame D symm opposite A B ha hb hab (by simp; omega) j hja hjb _ _
  let : Nonempty (Pair m r) := ⟨p⟩
  unfold mean
  rw [hq p, Finset.sum_congr rfl (fun q _ => hq q)]
  simp [nsmul_eq_mul, (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card (Pair m r) : ℝ) ≠ 0)]

end Computability.VPVNP.Grassmann.Rigidity

end OAI
