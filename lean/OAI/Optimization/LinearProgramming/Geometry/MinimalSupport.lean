import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.FinRange

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

variable {K ι : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]

/-- The vectors of `W` vanishing outside the support of `x`. -/
def supportSlice (W : Submodule K (ι → K)) (x : ι → K) : Submodule K (ι → K) where
  carrier := {v | v ∈ W ∧ ∀ j, x j = 0 → v j = 0}
  zero_mem' := ⟨W.zero_mem, fun _ _ => rfl⟩
  add_mem' := fun ⟨hv, hvz⟩ ⟨hw, hwz⟩ =>
    ⟨W.add_mem hv hw, fun j hj => by simp [hvz j hj, hwz j hj]⟩
  smul_mem' a v hv :=
    ⟨W.smul_mem a hv.1, fun j hj => by simp [hv.2 j hj]⟩

private theorem support_descent (W : Submodule K (ι → K)) (i : ι) {x v : ι → K}
    (hxW : x ∈ W) (hx : 0 ≤ x) (hvW : v ∈ W) (hvi : v i = 0)
    (hsupp : ∀ j, x j = 0 → v j = 0) (hpos : ∃ j, 0 < v j) :
    ∃ y ∈ W, 0 ≤ y ∧ y i = x i ∧ (∀ j, x j = 0 → y j = 0) ∧
      (Finset.univ.filter (fun j => y j ≠ 0)).card <
        (Finset.univ.filter (fun j => x j ≠ 0)).card := by
  classical
  let p := Finset.univ.filter (fun j => 0 < v j)
  have hp : p.Nonempty := by simpa [p, Finset.Nonempty] using hpos
  obtain ⟨k, hkp, hmin⟩ := p.exists_min_image (fun j => x j / v j) hp
  have hk : 0 < v k := (Finset.mem_filter.mp hkp).2
  let t := x k / v k
  have ht : 0 ≤ t := div_nonneg (hx k) hk.le
  let y := x - t • v
  have hyW : y ∈ W := W.sub_mem hxW (W.smul_mem t hvW)
  have hy : 0 ≤ y := by
    intro j
    change 0 ≤ x j - t * v j
    apply sub_nonneg.mpr
    by_cases hj : 0 < v j
    · exact (le_div_iff₀ hj).mp (hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hj)).trans (hx j)
  have hyi : y i = x i := by simp [y, hvi]
  have hyz (j : ι) (hj : x j = 0) : y j = 0 := by simp [y, hj, hsupp j hj]
  have hyk : y k = 0 := by simp [y, t, hk.ne']
  have hxk : x k ≠ 0 := fun h => hk.ne' (hsupp k h)
  refine ⟨y, hyW, hy, hyi, hyz, Finset.card_lt_card ?_⟩
  apply Finset.ssubset_iff_of_subset ?_ |>.mpr
  · exact ⟨k, by simp [hxk], by simp [hyk]⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact fun h => hj (hyz j h)

/-- A nonnegative witness positive at `i` can be reduced to a support on which the entire
subspace is a line, preserving the value at `i`. -/
theorem exists_witness_support_line (W : Submodule K (ι → K)) (i : ι) {x : ι → K}
    (hxW : x ∈ W) (hx : 0 ≤ x) (hxi : 0 < x i) :
    ∃ c ∈ W, 0 ≤ c ∧ c i = x i ∧ (∀ j, x j = 0 → c j = 0) ∧
      ∀ v ∈ W, (∀ j, c j = 0 → v j = 0) → v = (v i / c i) • c := by
  classical
  let size (v : ι → K) := (Finset.univ.filter (fun j => v j ≠ 0)).card
  let Qualified (n : ℕ) := ∃ c ∈ W, 0 ≤ c ∧ c i = x i ∧
    (∀ j, x j = 0 → c j = 0) ∧ size c = n
  have hex : ∃ n, Qualified n := ⟨size x, x, hxW, hx, rfl, fun _ hj => hj, rfl⟩
  obtain ⟨c, hcW, hc, hci, hxc, hsize⟩ := Nat.find_spec hex
  have hci0 : c i ≠ 0 := by rw [hci]; exact hxi.ne'
  refine ⟨c, hcW, hc, hci, hxc, ?_⟩
  intro v hvW hcv
  let w := v - (v i / c i) • c
  have hwW : w ∈ W := W.sub_mem hvW (W.smul_mem _ hcW)
  have hwi : w i = 0 := by simp [w, hci0]
  have hwz (j : ι) (hj : c j = 0) : w j = 0 := by simp [w, hj, hcv j hj]
  have hno (d : ι → K) (hd : d ∈ W) (hdi : d i = 0)
      (hdz : ∀ j, c j = 0 → d j = 0) : ¬ ∃ j, 0 < d j := by
    intro hp
    obtain ⟨y, hyW, hy, hyi, hyz, hs⟩ := support_descent W i hcW hc hd hdi hdz hp
    have hqual : Qualified (size y) :=
      ⟨y, hyW, hy, hyi.trans hci, fun j hj => hyz j (hxc j hj), rfl⟩
    have hle := Nat.find_min' hex hqual
    change size y < size c at hs
    exact (not_lt_of_ge hle) (hsize ▸ hs)
  have hw : w = 0 := by
    funext j
    apply le_antisymm
    · exact le_of_not_gt fun hj => hno w hwW hwi hwz ⟨j, hj⟩
    · apply le_of_not_gt
      intro hj
      apply hno (-w) (W.neg_mem hwW) (by simp [hwi]) (fun k hk => by simp [hwz k hk])
      exact ⟨j, by simpa using hj⟩
  exact sub_eq_zero.mp hw

/-- The support-restricted space of the reduced witness has dimension exactly one. -/
theorem exists_witness_supportSlice_finrank_one (W : Submodule K (ι → K)) (i : ι) {x : ι → K}
    (hxW : x ∈ W) (hx : 0 ≤ x) (hxi : 0 < x i) :
    ∃ c ∈ W, 0 ≤ c ∧ c i = x i ∧ (∀ j, x j = 0 → c j = 0) ∧
      Module.finrank K (supportSlice W c) = 1 := by
  obtain ⟨c, hcW, hc, hci, hxc, hline⟩ := exists_witness_support_line W i hxW hx hxi
  refine ⟨c, hcW, hc, hci, hxc, ?_⟩
  have heq : supportSlice W c = K ∙ c := by
    apply le_antisymm
    · intro v hv
      exact Submodule.mem_span_singleton.mpr ⟨v i / c i, (hline v hv.1 hv.2).symm⟩
    · apply Submodule.span_le.mpr
      rintro v (rfl : v = c)
      exact ⟨hcW, fun _ hj => hj⟩
  rw [heq]
  apply finrank_span_singleton
  intro heq0
  have : c i = 0 := congrFun heq0 i
  exact hxi.ne' (hci.symm.trans this)

end Geometry
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

variable {K ι : Type*} [Field K] [DecidableEq K] [Fintype ι]

/-- Rank-nullity for the projection of the row space onto the zero coordinates of `x`. -/
theorem rank_vanishing_columns_add_finrank {κ : Type*} [Fintype κ]
    (D : Matrix κ ι K) (x : ι → K) :
    (D.submatrix id (Subtype.val : {j // x j = 0} → ι)).rank +
      Module.finrank K (supportSlice (Submodule.span K (Set.range D.row)) x) = D.rank := by
  classical
  let W := LinearMap.range D.vecMulLinear
  let M := D.submatrix id (Subtype.val : {j // x j = 0} → ι)
  let T := (LinearMap.funLeft K K (Subtype.val : {j // x j = 0} → ι)).domRestrict W
  have hr : LinearMap.range T = LinearMap.range M.vecMulLinear := by
    ext q
    constructor
    · rintro ⟨⟨v, t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨⟨D.vecMulLinear t, t, rfl⟩, rfl⟩
  have hs : (LinearMap.ker T).map W.subtype = supportSlice W x := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, fun j hj => congrFun (LinearMap.mem_ker.mp ha) ⟨j, hj⟩⟩
    · rintro ⟨hv, hz⟩
      exact ⟨⟨v, hv⟩, LinearMap.mem_ker.mpr (funext fun j => hz j.1 j.2), rfl⟩
  have hk := (Submodule.equivMapOfInjective W.subtype W.subtype_injective
    (LinearMap.ker T)).finrank_eq
  rw [hs] at hk
  have hd := T.finrank_range_add_finrank_ker
  rw [hr, hk] at hd
  change M.rank + _ = D.rank
  rw [M.rank_eq_finrank_span_row, D.rank_eq_finrank_span_row, ← range_vecMulLinear D,
    ← range_vecMulLinear M]
  exact hd

/-- For independent basis rows, a witness whose support supports only one dimension leaves
exactly `#rows - 1` independent columns among its zero coordinates. -/
theorem rank_vanishing_columns_add_one {κ : Type*} [Fintype κ] {D : Matrix κ ι K}
    (hD : LinearIndependent K D.row) {c : ι → K}
    (hc : Module.finrank K (supportSlice (Submodule.span K (Set.range D.row)) c) = 1) :
    (D.submatrix id (Subtype.val : {j // c j = 0} → ι)).rank + 1 = Fintype.card κ := by
  simpa only [hc, hD.rank_matrix] using rank_vanishing_columns_add_finrank D c

end Geometry
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

variable {ι : Type*} [DecidableEq ι]

/-- Delete each coordinate if the restricted system still has a witness.
The second component records every query, in the order it was made. -/
def deleteCoordinates (oracle : Finset ι → Bool) : List ι → Finset ι → Finset ι × List (Finset ι)
  | [], s => (s, [])
  | j :: js, s =>
    let q := s.erase j
    let result := deleteCoordinates oracle js (if oracle q then q else s)
    (result.1, q :: result.2)

/-- Every surviving tested coordinate is necessary, including those tested before later deletions.
There is exactly one oracle call for each list entry. -/
theorem deleteCoordinates_spec {P : Finset ι → Prop}
    (hmono : ∀ {s t}, s ⊆ t → P s → P t) {oracle : Finset ι → Bool}
    (horacle : ∀ s, oracle s = true ↔ P s) (order : List ι) {s : Finset ι} (hs : P s) :
    (deleteCoordinates oracle order s).1 ⊆ s ∧ P (deleteCoordinates oracle order s).1 ∧
    (∀ j ∈ order, j ∈ (deleteCoordinates oracle order s).1 →
      ¬ P ((deleteCoordinates oracle order s).1.erase j)) ∧
    (deleteCoordinates oracle order s).2.length = order.length := by
  induction order generalizing s with
  | nil => simp [deleteCoordinates, hs]
  | cons j js ih =>
    let t := if oracle (s.erase j) then s.erase j else s
    have hts : t ⊆ s := by
      dsimp [t]
      split
      · exact Finset.erase_subset _ _
      · exact fun _ h => h
    have ht : P t := by
      dsimp [t]
      split
      · rename_i h
        exact (horacle _).mp h
      · exact hs
    have hj : j ∈ t → ¬ P (t.erase j) := by
      dsimp [t]; split <;> rename_i h
      · simp
      · exact fun _ hp => h ((horacle _).mpr hp)
    obtain ⟨hout, hpout, hmin, hlen⟩ := ih ht
    simp only [deleteCoordinates, List.length_cons]
    refine ⟨hout.trans hts, hpout, ?_, congrArg Nat.succ hlen⟩
    intro k hk hkout
    rcases List.mem_cons.mp hk with rfl | htail
    · intro hp
      exact hj (hout hkout) (hmono (Finset.erase_subset_erase _ hout) hp)
    · exact hmin k htail hkout

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype ι]

/-- The coordinate sets allowed for a nonnegative witness positive at `i`. -/
def witnessSupports (W : Submodule K (ι → K)) (i : ι) : Set (Finset ι) :=
  {s | ∃ v ∈ W, 0 ≤ v ∧ 0 < v i ∧ ∀ j, j ∉ s → v j = 0}

/-- The greedy support returned by subspace-feasibility queries supports a line. Its generator
is nonnegative and positive at the designated coordinate. -/
theorem deleteCoordinates_witness_line (W : Submodule K (ι → K)) (i : ι)
    (oracle : Finset ι → Bool) (horacle : ∀ s, oracle s = true ↔ s ∈ witnessSupports W i)
    (order : List ι) (hcovers : ∀ j, j ≠ i → j ∈ order) (hs : Finset.univ ∈ witnessSupports W i) :
    (deleteCoordinates oracle order Finset.univ).2.length = order.length ∧
    ∃ c ∈ W, 0 ≤ c ∧ 0 < c i ∧
      (∀ j, c j ≠ 0 ↔ j ∈ (deleteCoordinates oracle order Finset.univ).1) ∧
      Module.finrank K (supportSlice W c) = 1 := by
  have hmono {s t : Finset ι} (hsub : s ⊆ t) (h : s ∈ witnessSupports W i) :
      t ∈ witnessSupports W i := by
    obtain ⟨v, hvW, hv, hvi, hvz⟩ := h
    exact ⟨v, hvW, hv, hvi, fun j hj => hvz j (fun hjs => hj (hsub hjs))⟩
  obtain ⟨_, hout, hnecess, hlen⟩ := deleteCoordinates_spec hmono horacle order hs
  obtain ⟨v, hvW, hv, hvi, hvout⟩ := hout
  obtain ⟨c, hcW, hc, hci, hcsupp, hdim⟩ := exists_witness_supportSlice_finrank_one W i hvW hv hvi
  have hpositive : 0 < c i := hci ▸ hvi
  have hzero j (hj : j ∉ (deleteCoordinates oracle order Finset.univ).1) : c j = 0 :=
    hcsupp j (hvout j hj)
  refine ⟨hlen, c, hcW, hc, hpositive, ?_, hdim⟩
  intro j
  constructor
  · exact fun h => not_not.mp fun hj => h (hzero j hj)
  · intro hj hz
    have hji : j ≠ i := by rintro rfl; exact hpositive.ne' hz
    apply hnecess j (hcovers j hji) hj
    refine ⟨c, hcW, hc, hpositive, ?_⟩
    intro k hk
    by_cases heq : k = j
    · simpa [heq] using hz
    · exact hzero k fun hkout => hk (Finset.mem_erase.mpr ⟨heq, hkout⟩)

/-- The paper's concrete schedule tests all coordinates other than the anchor once. -/
theorem witness_line_in_pred_queries {n : ℕ} (W : Submodule K (Fin n → K)) (i : Fin n)
    (oracle : Finset (Fin n) → Bool)
    (horacle : ∀ s, oracle s = true ↔ s ∈ witnessSupports W i)
    (hs : Finset.univ ∈ witnessSupports W i) :
    let result := deleteCoordinates oracle ((List.finRange n).erase i) Finset.univ
    result.2.length + 1 = n ∧ ∃ c ∈ W, 0 ≤ c ∧ 0 < c i ∧
      (∀ j, c j ≠ 0 ↔ j ∈ result.1) ∧ Module.finrank K (supportSlice W c) = 1 := by
  obtain ⟨hlen, hline⟩ := deleteCoordinates_witness_line W i oracle horacle
    ((List.finRange n).erase i) (fun j hji => (List.mem_erase_of_ne hji).mpr (List.mem_finRange j)) hs
  exact ⟨by rw [hlen]; simpa using List.length_erase_add_one (List.mem_finRange i), hline⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
