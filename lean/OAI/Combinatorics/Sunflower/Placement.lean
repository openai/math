import OAI.Combinatorics.Sunflower.Placement.Sites
import OAI.Combinatorics.Sunflower.Planar

/-! # The planar anchor and satellite placement

The anchor lines are one unit tall and slightly more than one unit apart.
The satellites have evenly spaced heights.  The perturbation of the right
anchor is quadratic in the distance from the left anchor to the satellites. -/

noncomputable section
open scoped Classical
open OAI.LinearAlgebra.SpectralBooks OAI.Combinatorics.Sunflower.Planar

namespace OAI
namespace Combinatorics
namespace Sunflower
namespace Placement

variable {n : ℕ}

/-- Horizontal distance of the satellites from the left anchor. -/
def offset (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ)+1))

/-- Distance between the two anchor lines. -/
def spanX (n : ℕ) : ℝ := 1 + (offset n)^2/8

def height (j : Fin (n+2)) : ℝ := (j.val : ℝ) / ((n : ℝ)+1)

@[simp] theorem height_zero : height (0 : Fin (n+2)) = 0 := by simp [height]

@[simp] theorem height_top : height (Fin.last (n+1)) = 1 := by
  simp [height, show (n : ℝ) + 1 ≠ 0 by positivity]

theorem height_nonneg (j : Fin (n+2)) : 0 ≤ height j := by unfold height; positivity

theorem height_le_one (j : Fin (n+2)) : height j ≤ 1 := by
  rw [height, div_le_one (by positivity)]
  exact_mod_cast Nat.le_of_lt_succ j.isLt

theorem height_injective : Function.Injective (@height n) := by
  intro i j h
  apply Fin.ext
  have h' := (div_left_inj' (by positivity : (n : ℝ)+1 ≠ 0)).mp h
  exact_mod_cast h'

theorem interior_injective : Function.Injective (@interior n) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [interior] using this

theorem offset_pos (n : ℕ) : 0 < offset n := by unfold offset; positivity

theorem offset_le_quarter (n : ℕ) : offset n ≤ 1/4 := by
  rw [offset, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hn : (0:ℝ) ≤ n := by positivity
  linarith

theorem one_lt_spanX (n : ℕ) : 1 < spanX n := by
  have h := sq_pos_of_pos (offset_pos n)
  unfold spanX
  linarith

theorem offset_lt_spanX (n : ℕ) : offset n < spanX n := by
  linarith [offset_le_quarter n, one_lt_spanX n]

theorem row_spacing {i j : Fin n} (hij : i < j) :
    offset n < height (interior j) - height (interior i) := by
  have h : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
  simp only [offset, height, interior, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  have d : 0 < (n:ℝ)+1 := by positivity
  field_simp
  linarith

def position : Site n → Plane
  | .inl j => xy 0 (height j)
  | .inr (.inl j) => xy (spanX n) (height j)
  | .inr (.inr i) => xy (offset n) (height (interior i))

@[simp] theorem position_a (j : Fin (n+2)) : position (a j) = xy 0 (height j) := rfl
@[simp] theorem position_b (j : Fin (n+2)) : position (b j) = xy (spanX n) (height j) := rfl
@[simp] theorem position_z (i : Fin n) : position (z i) = xy (offset n) (height (interior i)) := rfl

theorem position_injective : Function.Injective (@position n) := by
  have hs : spanX n ≠ 0 := ne_of_gt (by linarith [one_lt_spanX n])
  have ht := (offset_pos n).ne'
  have hts := (offset_lt_spanX n).ne
  rintro (j|j|i) (k|k|l) h <;>
    simp only [position, xy_eq_iff] at h <;>
    first | exact congrArg _ (height_injective h.2)
          | exact congrArg (fun i ↦ Sum.inr (Sum.inr i)) (interior_injective (height_injective h.2))
          | exact congrArg (fun j ↦ Sum.inr (Sum.inl j)) (height_injective h.2)
          | exact (hs h.1).elim | exact (hs h.1.symm).elim
          | exact (ht h.1).elim | exact (ht h.1.symm).elim
          | exact (hts h.1).elim | exact (hts h.1.symm).elim

def embedding (n : ℕ) : Site n ↪ Plane := ⟨position, position_injective⟩

@[simp] theorem coe_embedding (n : ℕ) : ⇑(embedding n) = position := rfl

/-- The unnormalized semiperimeter of a group of sites. -/
def width (S : Finset (Site n)) : ℝ :=
  if h : S.Nonempty then meanWidth (S.map (embedding n)) h.map else 0

theorem width_eq (S : Finset (Site n)) (h : S.Nonempty) :
    width S = meanWidth (S.map (embedding n)) h.map := by simp [width, h]

private theorem width_of_hull {S : Finset (Site n)} {V : Finset Plane} (hV : V.Nonempty)
    (hVS : V ⊆ S.map (embedding n))
    (hh : (↑(S.map (embedding n)) : Set Plane) ⊆ convexHull ℝ (V : Set Plane)) :
    width S = meanWidth V hV := by
  have hs : S.Nonempty := Finset.map_nonempty.mp (hV.mono hVS)
  rw [width_eq _ hs]
  have h := meanWidth_union_of_subset_convexHull hV hh
  refine (meanWidth_congr ?_ _ _).trans h
  ext p
  simp only [Finset.mem_union]
  exact ⟨Or.inr, fun hp ↦ hp.elim (fun hv ↦ hVS hv) id⟩

def endsA (n : ℕ) : Finset (Site n) := {a 0, a (Fin.last (n+1))}
def endsB (n : ℕ) : Finset (Site n) := {b 0, b (Fin.last (n+1))}
def triA (i : Fin n) : Finset (Site n) := insert (z i) (endsA n)
def triB (i : Fin n) : Finset (Site n) := insert (z i) (endsB n)
def bracket (i : Fin n) : Finset (Site n) := {a (interior i), b (interior i)}
def satPair (i j : Fin n) : Finset (Site n) := {z i, z j}
def matchPair (i j : Fin n) : Finset (Site n) := {a (interior i), a (interior j)}

@[simp] theorem image_endsA (n : ℕ) : (endsA n).map (embedding n) = {xy 0 0, xy 0 1} := by
  simp [endsA]
@[simp] theorem image_endsB (n : ℕ) :
    (endsB n).map (embedding n) = {xy (spanX n) 0, xy (spanX n) 1} := by simp [endsB]

@[simp] theorem width_endsA (n : ℕ) : width (endsA n) = 1 := by
  rw [width_eq (endsA n) (Finset.insert_nonempty _ _)]
  simp [meanWidth_pair]
@[simp] theorem width_endsB (n : ℕ) : width (endsB n) = 1 := by
  rw [width_eq (endsB n) (Finset.insert_nonempty _ _)]
  simp [meanWidth_pair]

private theorem position_in_rect (s : Site n) :
    position s ∈ convexHull ℝ (rectangle 0 (spanX n) 0 1 : Set Plane) := by
  have h := (offset_lt_spanX n).le
  have h' := (offset_pos n).le
  rcases s with j | j | i <;> apply xy_mem_hull_rectangle <;>
    first | exact height_nonneg _ | exact height_le_one _ | linarith

private theorem rectangle_eq_ends (n : ℕ) :
    rectangle 0 (spanX n) 0 1 = ((endsA n ∪ endsB n).map (embedding n)) := by
  ext p
  simp only [rectangle, Finset.map_union, image_endsA, image_endsB, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union]
  tauto

theorem width_of_corners {S : Finset (Site n)} (h : endsA n ∪ endsB n ⊆ S) :
    width S = 1 + spanX n := by
  have hsub : rectangle 0 (spanX n) 0 1 ⊆ S.map (embedding n) := by
    rw [rectangle_eq_ends]
    exact Finset.map_subset_map.mpr h
  have hh : (↑(S.map (embedding n)) : Set Plane) ⊆
      convexHull ℝ (rectangle 0 (spanX n) 0 1 : Set Plane) := by
    intro p hp
    obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hp
    exact position_in_rect s
  rw [width_of_hull (rectangle_nonempty ..) hsub hh, meanWidth_rectangle]
  simp [abs_of_pos (by linarith [one_lt_spanX n] : 0 < spanX n), add_comm]

@[simp] theorem width_univ (n : ℕ) : width (Finset.univ : Finset (Site n)) = 1 + spanX n :=
  width_of_corners (Finset.subset_univ _)


private theorem width_fiber_of_anchor (u : Fin (n+2) → Site n) (x : ℝ)
    (hu : ∀ j, position (u j) = xy x (height j)) :
    width (Finset.univ.image u) = 1 := by
  have he (j : Fin (n+2)) : xy x (height j) ∈ (Finset.univ.image u).map (embedding n) :=
    Finset.mem_map.mpr ⟨u j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, hu _⟩
  have hsub : {xy x 0,xy x 1} ⊆ (Finset.univ.image u).map (embedding n) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · simpa only [height_zero] using he 0
    · obtain rfl := Finset.mem_singleton.mp hp
      simpa only [height_top] using he (Fin.last (n+1))
  have hh : (↑((Finset.univ.image u).map (embedding n)) : Set Plane) ⊆
      convexHull ℝ (↑({xy x 0,xy x 1} : Finset Plane) : Set Plane) := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hs
    change position (u j) ∈ _
    rw [hu]
    exact xy_mem_hull_vpair x (height_nonneg _) (height_le_one _)
  rw [width_of_hull (Finset.insert_nonempty _ _) hsub hh, meanWidth_pair]
  simp

@[simp] theorem width_fiber_zero (n : ℕ) : width (fiber (0 : Fin (n+2))) = 1 := by
  rw [fiber_zero]
  exact width_fiber_of_anchor a 0 position_a

@[simp] theorem width_fiber_one (n : ℕ) : width (fiber (1 : Fin (n+2))) = 1 := by
  rw [fiber_one]
  exact width_fiber_of_anchor b (spanX n) position_b

@[simp] theorem width_singleton (s : Site n) : width {s} = 0 := by
  rw [width_eq _ (Finset.singleton_nonempty _)]
  simpa using meanWidth_pair (position s) (position s)

theorem width_groups_sum (n : ℕ) : ∑ g : Fin (n+2), width (fiber g) = 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  norm_num

theorem deficit_pos (n : ℕ) :
    0 < width (Finset.univ : Finset (Site n)) - ∑ g : Fin (n+2), width (fiber g) := by
  rw [width_univ, width_groups_sum]
  linarith [one_lt_spanX n]

theorem bracket_copy (i : Fin n) :
    width (bracket i ∪ {z i}) = width (bracket i) := by
  let V := (bracket i).map (embedding n)
  have hb : (bracket i).Nonempty := Finset.insert_nonempty _ _
  have hV : V.Nonempty := hb.map
  have hV' : V =
      {xy 0 (height (interior i)), xy (spanX n) (height (interior i))} := by simp [V,bracket]
  have hh : (↑(({z i} : Finset _).map (embedding n)) : Set Plane) ⊆
      convexHull ℝ (V : Set Plane) := by
    intro p hp
    have hp' : p = position (z i) := by simpa using hp
    rw [hp', position_z, hV']
    exact xy_mem_hull_hpair _ (offset_pos n).le (offset_lt_spanX n).le
  have hh' := meanWidth_union_of_subset_convexHull hV hh
  rw [width_eq _ (hb.mono Finset.subset_union_left), width_eq _ hb]
  refine (meanWidth_congr ?_ _ _).trans hh'
  ext p
  simp [V]

private theorem triangle_bound (u : Fin (n+2) → Site n) (x : ℝ) (i : Fin n)
    (hu : ∀ j, position (u j) = xy x (height j)) (hx : offset n ≤ |x-offset n|) :
    1 + (offset n)^2/4 ≤ width {z i, u 0, u (Fin.last (n+1))} := by
  rw [width_eq _ (Finset.insert_nonempty _ _)]
  have h := meanWidth_triangle_vertical_lower (a := x) (z := offset n)
    (height_nonneg (interior i)) (height_le_one _)
    (offset_pos n).le (by linarith [offset_le_quarter n]) hx
  refine h.trans_eq (meanWidth_congr ?_ _ _)
  ext p
  simp only [Finset.map_insert,Finset.map_singleton,coe_embedding,hu,height_zero,height_top,
    position_z,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem gap_left (i : Fin n) :
    0 < width (triA i) + width (endsB n) - width (triA i ∪ endsB n) := by
  have hh : endsA n ∪ endsB n ⊆ triA i ∪ endsB n :=
    Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
  rw [width_of_corners hh, width_endsB]
  have h := triangle_bound a 0 i position_a (by simpa using (le_abs_self (offset n)))
  change 1 + (offset n)^2/4 ≤ width (triA i) at h
  unfold spanX
  nlinarith [sq_pos_of_pos (offset_pos n)]

theorem gap_right (i : Fin n) :
    0 < width (triB i) + width (endsA n) - width (triB i ∪ endsA n) := by
  have hh : endsA n ∪ endsB n ⊆ triB i ∪ endsA n := by
    rw [Finset.union_comm]
    exact Finset.union_subset_union (Finset.subset_insert _ _) (Finset.Subset.refl _)
  rw [width_of_corners hh, width_endsA]
  have hx : offset n ≤ |spanX n - offset n| := by
    rw [abs_of_pos (sub_pos.mpr (offset_lt_spanX n))]
    linarith [one_lt_spanX n, offset_le_quarter n]
  have h := triangle_bound b (spanX n) i position_b hx
  change 1 + (offset n)^2/4 ≤ width (triB i) at h
  unfold spanX
  nlinarith [sq_pos_of_pos (offset_pos n)]

theorem gap_satellites {i j : Fin n} (hij : i < j) :
    0 < width (satPair i j) + width (matchPair i j) -
      width (satPair i j ∪ matchPair i j) := by
  have S : (satPair i j).Nonempty := Finset.insert_nonempty _ _
  have M : (matchPair i j).Nonempty := Finset.insert_nonempty _ _
  have hrect : (satPair i j ∪ matchPair i j).map (embedding n) =
      rectangle (offset n) 0 (height (interior i)) (height (interior j)) := by
    ext p
    simp only [satPair,matchPair,rectangle,Finset.map_union,Finset.map_insert,Finset.map_singleton,
      coe_embedding,position_z,position_a,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  rw [width_eq _ S, width_eq _ M, width_eq _ (S.mono Finset.subset_union_left)]
  have he := meanWidth_rectangle (offset n) 0 (height (interior i)) (height (interior j))
  rw [(meanWidth_congr hrect _ (rectangle_nonempty ..)).trans he]
  simp only [satPair,matchPair,Finset.map_insert,Finset.map_singleton,
    coe_embedding,position_z,position_a,meanWidth_pair,dist_xy_vert,
    sub_zero,abs_of_pos (offset_pos n)]
  rw [abs_of_neg (by linarith [row_spacing hij,offset_pos n] :
    height (interior i) - height (interior j) < 0)]
  linarith [row_spacing hij]

end Placement
end Sunflower
end Combinatorics
end OAI
