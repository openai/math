import OAI.LinearAlgebra.MatrixExponent.Sphere.Block
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import OAI.LinearAlgebra.MatrixExponent.Sphere.Coupled

/-!
# Fusion of simultaneous collisions

Groups are in cluster order. Their offsets determine the independent
fusion coefficients, leaving a Wick sum at the cluster centers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {F R : Type*} {n r : ℕ}

namespace Cluster

private def active (c : Fin n → F) (xs : Fin n → List (Site F r)) : List (Leg F r) :=
  (List.ofFn (fun i => (xs i).map (Leg.moving (c i)))).flatten

private def ready {N : ℕ} (c : Fin n → F) (b : Fin n → LevelLE r N) : List (Site F r) :=
  (List.ofFn (fun i => (b i).val.val.map (c i, ·))).flatten

private theorem active_succ (c : Fin (n + 1) → F) (xs : Fin (n + 1) → List (Site F r)) :
    active c xs = (xs 0).map (Leg.moving (c 0)) ++ active (Fin.tail c) (Fin.tail xs) := by
  rw [active, List.ofFn_succ, List.flatten_cons]
  rfl

private theorem ready_succ {N : ℕ} (c : Fin (n + 1) → F) (b : Fin (n + 1) → LevelLE r N) :
    ready c b = (b 0).val.val.map (c 0, ·) ++ ready (Fin.tail c) (Fin.tail b) := by
  rw [ready, List.ofFn_succ, List.flatten_cons]
  rfl

variable [Field F] [CommRing R] [Algebra F R]

private theorem all_fused (u : R) (N : ℕ) (ys : List (Site F r)) :
    wick (pair u N) (ys.map Leg.fused) = algebraMap F R (wick fieldKernel ys) := by
  rw [wick_map, wick_hom]
  rfl

private theorem all_blocks (u : R) (N : ℕ) (hu : u ^ N = 0)
    (c : Fin n → F) (hc : Function.Injective c) (xs : Fin n → List (Site F r))
    (pre : List (Site F r)) :
    wick (pair u N) (pre.map Leg.fused ++ active c xs) =
      ∑ b : Fin n → LevelLE r N, u ^ (∑ i, energy (b i).val.val) *
        algebraMap F R ((∏ i, blockCoeff (xs i) (b i).val) *
          wick fieldKernel (pre ++ ready c b)) := by
  classical
  induction n generalizing pre with
  | zero => simp [active, ready, all_fused]
  | succ n ih =>
    have htail : Function.Injective (Fin.tail c) := hc.comp (Fin.succ_injective _)
    have ha : ∀ y ∈ active (Fin.tail c) (Fin.tail xs), ¬ belongs (c 0) y := by
      simp only [active, List.mem_flatten, List.mem_ofFn]
      rintro y ⟨_, ⟨i, rfl⟩, hy⟩
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
      exact fun e => Fin.succ_ne_zero i (hc e).symm
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => LevelLE r N)
    rw [active_succ, ← List.append_assoc, block u N (c 0) hu _ _ _ (by simp only [List.forall_mem_map, belongs, not_false_eq_true, implies_true]) ha,
      ← e.sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    have he : pre.map Leg.fused ++ z.val.val.map (fun i => Leg.fused (c 0, i)) =
        (pre ++ z.val.val.map (c 0, ·)).map Leg.fused := by
      simp [Function.comp_def]
    rw [he, ih _ htail, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [show e (z, b) = Fin.cons z b from rfl, Fin.sum_univ_succ, Fin.prod_univ_succ, ready_succ,
      Fin.cons_zero, Fin.cons_succ, Fin.tail_cons, List.append_assoc, pow_add, map_mul]
    dsimp only [Fin.tail]
    ring

end Cluster

open Cluster

/-- The normalized generator pairing sums agree over every nilpotent
extension. Taking the parameter modulo its Nth power recovers any desired
finite precision of the expansion. -/
theorem multifusion [Field F] [CommRing R] [Algebra F R] (c : Fin n → F) (xs : Fin n → List (Site F r))
    (hc : Function.Injective c) (u : R) (N : ℕ) (hu : u ^ N = 0) :
    wick (clusterKernel u N (Prod.fst : F × F → F) Prod.snd)
        (List.ofFn (fun i => (xs i).map (fun z => ((c i, z.1), z.2)))).flatten =
      ∑ b : Fin n → LevelLE r N, u ^ (∑ i, energy (b i).val.val) *
        algebraMap F R ((∏ i, blockCoeff (xs i) (b i).val) *
          wick fieldKernel (List.ofFn (fun i => (b i).val.val.map (c i, ·))).flatten) := by
  let lab (p : (F × F) × Mode r) := Leg.moving p.1.1 (p.1.2, p.2)
  have he : active c xs =
      ((List.ofFn (fun i => (xs i).map (fun z => ((c i, z.1), z.2)))).flatten).map lab := by
    simp [active, List.map_flatten, List.map_ofFn, Function.comp_def, lab]
  have h := all_blocks u N hu c hc xs []
  simp only [List.map_nil, List.nil_append, he, wick_map, lab, pair_moving, ready] at h
  exact h

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# Sphere forms on fixed-energy legs

Permuting the marked sites contributes a sign independent of the
chosen basis words because each word's parity equals its energy parity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Finset
open scoped Classical

variable {A F R : Type*} [Field F] [CommRing R] [Algebra F R] {r n : ℕ}

abbrev States (r : ℕ) (e : A → ℕ) := ∀ i, Level r (e i)

def marksAt {e : A → ℕ} (x : States r e) (i : A) : List (A × Mode r) :=
  (x i).val.val.map (i, ·)

theorem weight_list {e : A → ℕ} (x : States r e) (l : List A) :
    weight (l.flatMap (marksAt x)) = (l.map e).sum := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    have h : weight (marksAt x i) = e i := by
      simpa [weight, marksAt, Function.comp_def] using (x i).2
    simpa [weight, energy] using congrArg₂ (· + ·) h ih

private theorem sign_weight {e : A → ℕ} (x : States r e) (i j : A) :
    (-1 : R) ^ ((marksAt x i).length * (marksAt x j).length) = (-1) ^ (e i * e j) := by
  have he (a : A) : (marksAt x a).length % 2 = e a % 2 := by
    rw [marksAt, List.length_map, ← energy_mod_two, (x a).2]
  rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (e i * e j), Nat.mul_mod,
    he, he, ← Nat.mul_mod]

theorem wick_perm_sites (e : A → ℕ) {l l' : List A} (h : l.Perm l') :
    ∃ c : ℕ, ∀ (k : A × Mode r → A × Mode r → R), (∀ i j, k j i = -k i j) →
      ∀ (x : States r e) (p : List (A × Mode r)),
        wick k (p ++ l.flatMap (marksAt x)) =
          (-1) ^ c * wick k (p ++ l'.flatMap (marksAt x)) := by
  induction h with
  | nil => exact ⟨0, by simp⟩
  | cons i _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c, fun k hk x p => by simpa [List.append_assoc] using hc k hk x (p ++ marksAt x i)⟩
  | swap i j l =>
    refine ⟨e j * e i, fun k hk x p => ?_⟩
    simpa only [List.flatMap_cons, List.append_assoc, sign_weight]
      using wick_swap_blocks hk p (marksAt x j) (marksAt x i) (l.flatMap (marksAt x))
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨c, hc⟩ := ih₁
    obtain ⟨d, hd⟩ := ih₂
    exact ⟨c + d, fun k hk x p => by rw [hc k hk, hd k hk, pow_add, mul_assoc]⟩

variable [Fintype A]

def inputs {e : A → ℕ} (x : States r e) : List (A × Mode r) :=
  univ.toList.flatMap (marksAt x)

theorem weight_inputs {e : A → ℕ} (x : States r e) : weight (inputs x) = ∑ i, e i := by
  rw [inputs, weight_list, ← List.sum_toFinset e (nodup_toList _)]
  simp

private def fiberList (f : A → Fin n) (j : Fin n) :=
  ({i | f i = j} : Finset _).toList

private theorem group_perm (f : A → Fin n) :
    univ.toList.Perm ((List.finRange n).flatMap (fiberList f)) := by
  have hd : ((List.finRange n).flatMap (fiberList f)).Nodup := by
    refine List.nodup_flatMap.mpr ⟨fun _ _ => nodup_toList _, (List.nodup_finRange n).imp ?_⟩
    intro i j h
    apply List.disjoint_left.mpr
    simp only [fiberList, mem_toList, mem_filter, mem_univ, true_and]
    exact fun _ hi hj => h (hi.symm.trans hj)
  apply (List.perm_ext_iff_of_nodup (nodup_toList _) hd).mpr
  simp [fiberList]

def blockInputs {e : A → ℕ} (f : A → Fin n) (o : A → F) (x : States r e) (j : Fin n) :
    List (Site F r) :=
  (fiberList f j).flatMap fun i => (x i).val.val.map (o i, ·)

omit [Field F] in
theorem blockInputs_eq {e : A → ℕ} (f : A → Fin n) (o : A → F) (x y : States r e)
    (j : Fin n) (h : ∀ i, f i = j → x i = y i) :
    blockInputs f o x j = blockInputs f o y j := by
  apply List.flatMap_congr
  intro i hi
  rw [h i (by simpa [fiberList] using hi)]

theorem grouped_fusion {e : A → ℕ} (c : Fin n → F) (hc : Function.Injective c)
    (f : A → Fin n) (o : A → F) (u : R) (N : ℕ) (hu : u ^ N = 0) :
    ∃ s : F, ∀ x : States r e, wick (clusterKernel u N (c ∘ f) o) (inputs x) =
      algebraMap F R s * ∑ b : Fin n → LevelLE r N, u ^ (∑ j, energy (b j).val.val) *
        algebraMap F R ((∏ j, blockCoeff (blockInputs f o x j) (b j).val) *
          wick fieldKernel (List.ofFn (fun j => (b j).val.val.map (c j, ·))).flatten) := by
  let k := clusterKernel (r := r) u N (c ∘ f) o
  have skew (i j : A × Mode r) : k j i = - k i j := by
    have h := Cluster.pair_skew u N (.moving (c (f i.1)) (o i.1, i.2))
      (.moving (c (f j.1)) (o j.1, j.2))
    rw [Cluster.pair_moving, Cluster.pair_moving] at h
    exact h
  obtain ⟨s, hs⟩ := wick_perm_sites (R := R) (r := r) e (group_perm f)
  refine ⟨(-1) ^ s, fun x => ?_⟩
  have h := hs k skew x []
  rw [map_pow, map_neg, map_one]
  simp only [List.nil_append, List.flatMap_assoc] at h
  rw [inputs, h, ← multifusion c (blockInputs f o x) hc u N hu]
  let move (i : A × Mode r) := ((c (f i.1), o i.1), i.2)
  have he : (List.ofFn (fun j =>
      (blockInputs f o x j).map (fun z => ((c j, z.1), z.2)))).flatten =
      ((List.finRange n).flatMap (fun j => (fiberList f j).flatMap (marksAt x))).map move := by
    rw [List.ofFn_eq_map, List.map_flatMap]
    apply List.flatMap_congr
    intro j _
    simp only [blockInputs, List.map_flatMap]
    apply List.flatMap_congr
    intro i hi
    have hij : f i = j := by simpa [fiberList] using hi
    simp [marksAt, move, Function.comp_def, hij]
  rw [he, wick_map]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# Passing an insertion through a seam

After fusing on the near side, sum the old seam state against the far
sphere. The transposed fusion map can be recovered there by regular
evaluations. The interpolation weights are independent of all states.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open scoped Classical
variable {F : Type} [Field F] {r : ℕ} {s : Finset F}

def stationary (c : s) (a : Wedge r) (ys : List (s × Mode r)) : F :=
  wick fieldKernel (a.val.map (c.val, ·) ++ spectators ys)

def moving (c : s) (a x : Wedge r) (ys : List (s × Mode r)) (z : F) : F :=
  wick fieldKernel ((triple c a.val x.val ys).map (atPoint z))

private theorem fusion_odd (a x b : Wedge r) (h : (energy a.val + energy x.val + energy b.val) % 2 = 1) :
    fusion F a.val x.val b.val = 0 := by
  apply wick_odd
  simp only [marks, List.length_append, List.length_map, List.length_reverse]
  have := energy_mod_two a.val
  have := energy_mod_two x.val
  have := energy_mod_two b.val
  omega

theorem recover_level (c : s) (T : Finset F) (hT : Disjoint T s) (e m e' w : ℕ)
    (bound : s.card * ((e + m + w) / 2) < T.card) :
    ∃ f : T → F, ∀ (a : Level r e) (x : Wedge r) (ys : List (s × Mode r)),
      energy x.val = m → (∀ y ∈ ys, y.1 ≠ c) → weight ys = w →
      (∑ b : Level r e', fusion F a.val.val x.val b.val.val * stationary c b.val ys) =
        ∑ z : T, f z * moving c a.val x ys z := by
  by_cases h : (e + m + e') % 2 = 1
  · refine ⟨0, fun a x ys hx _ _ => ?_⟩
    have hb (b : Level r e') : fusion F a.val.val x.val b.val.val = 0 :=
      fusion_odd _ _ _ (by rw [a.property, hx, b.property]; exact h)
    simp [hb]
  let j : ℤ := ((e' : ℤ) - e - m) / 2
  let H := (e + m + w) / 2
  obtain ⟨f, hf⟩ := recover_fusion (r := r) c T hT H bound j
  refine ⟨f, fun a x ys hx hy hw => ?_⟩
  have eqn := hf a.val.val x.val ys hy (by rw [weight_triple, a.property, hx, hw])
  have he : (energy a.val.val : ℤ) + energy x.val + 2 * j = e' := by
    rw [a.property, hx]
    unfold j
    omega
  dsimp only at eqn
  rw [he, ite_eq_right (by omega), Int.toNat_natCast] at eqn
  exact eqn

/-- A fixed lowering map for the whole construction. -/
def lowering (F : Type) [Field F] (r : ℕ) : (Wedge r →₀ F) →ₗ[F] (Wedge r →₀ F) :=
  (seam F r).choose

/-- Transpose the near-side fusion coefficient through the old seam.
One choice of lowering operator works for every position and energy.
The regular evaluation weights depend only on energies and marks. -/
theorem cross_seam (r : ℕ) :
    let S := lowering F r;
      (∀ x y : Wedge r, y ∈ (S (Finsupp.single x 1)).support →
        energy y.val ≤ energy x.val ∧ y.val.length = x.val.length) ∧
      ∀ (s : Finset F) (c : s) (T : Finset F), Disjoint T s →
      ∀ e m e' w : ℕ, s.card * ((e' + m + w) / 2) < T.card →
      ∃ f : ℕ → T → F, ∀ (b : Level r e') (x : Level r m) (ys : List (s × Mode r)),
        (∀ y ∈ ys, y.1 ≠ c) → weight ys = w →
        (∑ a : Level r e, fusion F a.val.val x.val.val b.val.val * stationary c a.val ys) =
        (S (Finsupp.single x.val 1)).sum (fun y q =>
          q * ∑ z : T, f (energy y.val) z * moving c b.val y ys z) := by
  intro S
  obtain ⟨hs, he⟩ := (seam F r).choose_spec
  refine ⟨hs, ?_⟩
  intro s c T hd e m e' w hw
  have hb (t : ℕ) : s.card * ((e' + min t m + w) / 2) < T.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hw
  choose f hf using fun t => recover_level (r := r) c T hd e' (min t m) e w (hb t)
  refine ⟨f, fun b x ys hy hw' => ?_⟩
  let u := S (Finsupp.single x.val 1)
  have e₁ (a : Level r e) : fusion F a.val.val x.val.val b.val.val =
      ∑ y ∈ u.support, u y * fusion F b.val.val y.val a.val.val := by
    have ht := DFunLike.congr_fun (he a.val b.val) (Finsupp.single x.val 1)
    simp only [entry, Finsupp.linearCombination_single, one_smul, LinearMap.comp_apply] at ht
    exact ht
  simp only [e₁, Finset.sum_mul, mul_assoc, Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hym
  have hle := (hs x.val y hym).1.trans_eq x.property
  rw [← Finset.mul_sum, hf (energy y.val) b y ys (min_eq_left hle).symm hy hw']

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-!
# A single seam crossing

The near sphere has the first coordinate, its private sphere the second.
At a seam the private sphere is regular. Negative Laurent orders therefore
force a drop on the shared seam. Only regular evaluations of the private
sphere and the far sphere are needed to reconstruct the crossing.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial
open scoped Classical
variable {F : Type} [Field F] {r t : ℕ} {A B C : Finset F}

/-- New doubled energy after an order-`i` collision. -/
def fusedEnergy (e m : ℕ) (i : ℤ) : ℤ := (e : ℤ) + m + 2 * i

/-- Multiply the weighted energies by `2P` to use integral units.
The loss covers the insertion and its reserve. -/
theorem seam_drop (P e m n H d : ℕ) (j : ℤ) (v : ℤ × ℤ) (hv : v ∈ pairs P d 0 j)
    (hj : (P * m + n + 2 * P * H : ℕ) ≤ -j) :
    P * fusedEnergy e m v.1 + (P * m + n + 2 * P * H : ℕ) ≤ (P : ℤ) * e := by
  obtain ⟨eq, _, pos⟩ := mem_pairs hv
  unfold fusedEnergy
  push_cast at hj pos ⊢
  have h : (0 : ℤ) ≤ (2 : ℤ) * P * H := by positivity
  linarith only [eq, pos, hj, h, Int.natCast_nonneg n]

def sphereCoeff (z : F) (xs : List (Option A × Mode r)) (i : ℤ) : F :=
  (laurent z (numerator A xs) (denominatorPoly A xs)).coeff i

def pairedCoeff (P : ℕ) (z : F) (xs : List (Option A × Mode r)) (ys : List (Option B × Mode t))
    (j : ℤ) : F :=
  (laurent z (coupled P (numerator A xs) (numerator B ys))
    (coupled P (denominatorPoly A xs) (denominatorPoly B ys))).coeff j

/-- At a seam the second coordinate has no principal part. -/
theorem coeff_at_seam (p l : ℕ) [ExpChar F p] (z : F) (ha : z ^ (p ^ l) ∈ A) (hb : z ∉ B)
    (xs : List (Option A × Mode r)) (ys : List (Option B × Mode t)) (j : ℤ) :
    pairedCoeff (p ^ l) z xs ys j =
      ∑ v ∈ pairs (p ^ l) (weight xs / 2) 0 j,
        sphereCoeff (z ^ (p ^ l)) xs v.1 * sphereCoeff z ys v.2 := by
  let q := poles (A.erase (z ^ (p ^ l))) (fun _ => weight xs / 2)
  have hq : q.eval (z ^ (p ^ l)) ≠ 0 := poles_eval _ (Finset.notMem_erase _ _)
  have hB : (denominatorPoly B ys).eval z ≠ 0 := poles_eval _ hb
  have h := coupled_coeff p l z (numerator A xs) (numerator B ys) q (denominatorPoly B ys)
    (weight xs / 2) 0 hq hB j
  have hA : (X - Polynomial.C (z ^ (p ^ l))) ^ (weight xs / 2) * q = denominatorPoly A xs :=
    (poles_split _ ha).symm
  simpa only [hA, pow_zero, one_mul, pairedCoeff, sphereCoeff] using h

theorem recover_sphere (V : Finset F) (hV : Disjoint V B) (d : ℕ)
    (bound : B.card * d < V.card) (z : F) (i : ℤ) :
    ∃ g : V → F, ∀ ys : List (Option B × Mode t), weight ys / 2 = d →
      sphereCoeff z ys i = ∑ y : V, g y * wick fieldKernel (ys.map (atPoint y.val)) := by
  let q := poles B (fun _ => d)
  obtain ⟨g, hg⟩ := recover_coefficient V q (fun _ hy => poles_eval _ (Finset.disjoint_left.mp hV hy))
    q.natDegree (by simpa [q, degree_poles] using bound) z i
  refine ⟨g, fun ys he => ?_⟩
  have h : denominatorPoly B ys = q := by unfold denominatorPoly; rw [he]
  rw [← h] at hg
  rw [sphereCoeff, hg _ (degree_numerator B ys)]
  exact Finset.sum_congr rfl fun y _ =>
    congrArg (g y * ·) (eval_sphere B ys y.val (Finset.disjoint_left.mp hV y.property))

/-- Contract two spheres by equality on the indicated level. Negative
levels carry no states. -/
def sew (r : ℕ) (e : ℤ) (left right : Wedge r → F) : F :=
  if e < 0 then 0 else ∑ a : Level r e.toNat, left a.val * right a.val

theorem sew_nat (e : ℕ) (left right : Wedge r → F) :
    sew r (e : ℤ) left right = ∑ a : Level r e, left a.val * right a.val := by
  simp [sew]

private theorem sew_fusion {m : ℕ} (c : A) (ys : List (A × Mode r)) (hy : ∀ y ∈ ys, y.1 ≠ c)
    (x : Level r m) (e : ℕ) (i : ℤ) (right moved : Wedge r → F)
    (h : ∀ b : Level r (fusedEnergy e m i).toNat,
      (∑ a : Level r e, fusion F a.val.val x.val.val b.val.val * right a.val) = moved b.val) :
    sew r e (fun a => sphereCoeff c.val (triple c a.val x.val.val ys) i) right =
      sew r (fusedEnergy e m i) (fun b => stationary c b ys) moved := by
  let t := fusedEnergy e m i
  have hc (a : Level r e) :
      sphereCoeff c.val (triple c a.val.val x.val.val ys) i =
        if t < 0 then 0 else ∑ b : Level r t.toNat,
          fusion F a.val.val x.val.val b.val.val * stationary c b.val ys := by
    rw [sphereCoeff, coeff_fusion c _ _ _ hy, a.property, x.property]
    rfl
  rw [sew_nat]
  simp only [hc]
  change _ = sew r t _ _
  by_cases neg : t < 0
  · simp [sew, neg]
  simp only [sew, ite_eq_right neg, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← h b, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Value on the far sphere with the transformed insertion. -/
def transported (c : C) (V : Finset F) (S : (Wedge r →₀ F) →ₗ[F] (Wedge r →₀ F))
    (f : ℕ → V → F) (x : Wedge r) (ys : List (C × Mode r)) (b : Wedge r) : F :=
  (S (Finsupp.single x 1)).sum (fun y q =>
    q * ∑ z : V, f (energy y.val) z * moving c b y ys z)

/-- Reconstruct a seam coefficient by regular evaluations on the far
and private spheres, sewing at the lower level. The near and far spectator
energies are `u,w`. The private sphere has total doubled energy `n+v`,
including `n` from the mover. All weights are uniform in the basis entries. -/
theorem seam_step (p l : ℕ) [ExpChar F p] (z : F) (ha : z ^ (p ^ l) ∈ A) (hb : z ∉ B)
    (c : C) (U V : Finset F) (hU : Disjoint U B) (hV : Disjoint V C)
    (e m n H u v w : ℕ) (hB : B.card * ((n + v) / 2) < U.card)
    (hC : C.card * ((e + m + w) / 2) < V.card) :
    let P := p ^ l
    let d : A := ⟨z ^ P, ha⟩
    let S := lowering F r
    ∃ (f : ℕ → ℕ → V → F) (g : ℤ → U → F),
      (∀ x y : Wedge r, y ∈ (S (Finsupp.single x 1)).support →
        energy y.val ≤ energy x.val ∧ y.val.length = x.val.length) ∧
      ∀ (j : ℤ), (P * m + n + 2 * P * H : ℕ) ≤ -j →
      ∀ (x : Level r m) (ys : List (A × Mode r)) (bs : List (Option B × Mode t))
        (fs : List (C × Mode r)), (∀ y ∈ ys, y.1 ≠ d) → (∀ y ∈ fs, y.1 ≠ c) →
        weight ys = u → weight bs = n + v → weight fs = w →
        sew r e (fun a => pairedCoeff P z (triple d a.val x.val.val ys) bs j)
          (fun a => stationary c a fs) =
          ∑ q ∈ pairs P ((e + m + u) / 2) 0 j,
            let E := fusedEnergy e m q.1
            sew r E (fun b => stationary d b ys) (transported c V S (f E.toNat) x.val fs) *
              ∑ y : U, g q.2 y * wick fieldKernel (bs.map (atPoint y.val)) := by
  intro P d S
  obtain ⟨hs, ht⟩ := cross_seam (F := F) r
  have hx (E : ℕ) (he : E ≤ e) : C.card * ((E + m + w) / 2) < V.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hC
  choose! f hf using fun E he => ht C c V hV e m E w (hx E he)
  choose g hg using fun j => recover_sphere (t := t) U hU ((n + v) / 2) hB z j
  refine ⟨f, g, hs, ?_⟩
  intro j hj x ys bs fs hy hfs hu hv hw
  let left (a : Wedge r) := triple d a.val x.val.val ys
  let I := pairs P ((e + m + u) / 2) 0 j
  have h (a : Level r e) : pairedCoeff P z (left a.val) bs j =
      ∑ q ∈ I, sphereCoeff d.val (left a.val) q.1 * sphereCoeff z bs q.2 := by
    rw [coeff_at_seam p l z ha hb, weight_triple, a.property, x.property, hu]
  rw [sew_nat]
  change (∑ a : Level r e, pairedCoeff P z (left a.val) bs j * stationary c a.val fs) = _
  simp only [h, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q hq => ?_
  have he : (fusedEnergy e m q.1).toNat ≤ e := by
    have drop := seam_drop P e m n H _ j q hq hj
    have hp : (0 : ℤ) < P := by exact_mod_cast expChar_pow_pos F p l
    have le : (P : ℤ) * fusedEnergy e m q.1 ≤ P * e := by omega
    have := le_of_mul_le_mul_left le hp
    omega
  have eqn := sew_fusion d ys hy x e q.1 (fun a => stationary c a fs)
    (transported c V S (f _) x.val fs) (fun b => hf _ he b x fs hfs hw)
  rw [sew_nat] at eqn
  rw [← eqn, ← hg q.2 bs (by rw [hv]), Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_right_comm _ _ _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-!
# Motion on paired spheres

In the shared coordinate, the powers in the first sphere's denominator
are multiplied by the characteristic power. Reconstruct from the
prescribed Laurent orders and fuse each insertion coefficient.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial Finset
open scoped Classical
variable {F : Type} [Field F] {r t : ℕ} {A B : Finset F}

def powered (P : ℕ) (s : Finset F) : Finset F := s.image (· ^ P)

def poleOrder (P d e : ℕ) (B : Finset F) (z : F) : ℕ :=
  P * d + if z ∈ B then e else 0

variable (p l : ℕ) [ExpChar F p]

theorem power_injective : Function.Injective (fun z : F => z ^ (p ^ l)) := by
  intro x y h
  dsimp only at h
  apply sub_eq_zero.mp
  by_contra ne
  apply pow_ne_zero (p ^ l) ne
  rw [sub_pow_expChar_pow, h, sub_self]

theorem paired_poles (S B : Finset F) (h : B ⊆ S) (d e : ℕ) :
    coupled (p ^ l) (poles (powered (p ^ l) S) (fun _ => d)) (poles B (fun _ => e)) =
      poles S (poleOrder (p ^ l) d e B) := by
  have hA : (poles (powered (p ^ l) S) (fun _ => d)).comp (X ^ (p ^ l)) =
      poles S (fun _ => p ^ l * d) := by
    unfold poles powered
    rw [prod_image (power_injective p l).injOn, Polynomial.prod_comp]
    refine prod_congr rfl fun z _ => ?_
    rw [pow_comp, sub_comp, X_comp, C_comp, map_pow, ← sub_pow_expChar_pow, pow_mul]
  have hB : poles B (fun _ => e) = poles S (fun z => if z ∈ B then e else 0) := by
    unfold poles
    rw [← prod_subset h (fun z _ hz => by simp [hz])]
    exact prod_congr rfl fun z hz => by simp [hz]
  rw [coupled, hA, hB]
  unfold poles poleOrder
  simp only [pow_add, prod_mul_distrib]

private theorem degree_pair (P : ℕ) (hP : P ≠ 0) (xs : List (Option A × Mode r))
    (ys : List (Option B × Mode t)) :
    (coupled P (numerator A xs) (numerator B ys)).natDegree ≤
      (coupled P (denominatorPoly A xs) (denominatorPoly B ys)).natDegree := by
  have monic (S : Finset F) (H : ℕ) : (poles S (fun _ => H)).Monic :=
    monic_prod_of_monic _ _ fun z _ => (monic_X_sub_C z).pow H
  have hA : ((denominatorPoly A xs).comp (X ^ P)).Monic :=
    (monic A _).comp (monic_X.pow P) (by simp [hP])
  have hB : (denominatorPoly B ys).Monic := monic B _
  unfold coupled
  rw [natDegree_mul hA.ne_zero hB.ne_zero]
  refine natDegree_mul_le.trans ?_
  rw [natDegree_comp, natDegree_comp]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (degree_numerator A xs)) (degree_numerator B ys)

/-- The interpolation weights are independent of every basis mode.
The private sphere may omit stationary marks, including the seams. -/
theorem paired_reconstruction {S seams : Finset F} (hB : B ⊆ S) (hs : seams ⊆ S)
    {collector : F} (hc : collector ∈ S) (hc' : collector ∉ seams)
    (g L : ℕ) (hg : seams.card ≤ g) (d e : ℕ) (z : F) (hz : z ∉ S) :
    let P := p ^ l
    let D := poleOrder P d e B
    ∃ c : (Σ y : S, Fin (orders seams collector D g L y.val)) → F,
      ∀ (xs : List (Option (powered P S) × Mode r)) (ys : List (Option B × Mode t)),
        weight xs / 2 = d → weight ys / 2 = e →
        wick fieldKernel (xs.map (atPoint (z ^ P))) * wick fieldKernel (ys.map (atPoint z)) =
          ∑ i, c i * pairedCoeff P i.1.val xs ys ((i.2.val : ℤ) - D i.1.val) := by
  intro P D
  obtain ⟨c, h⟩ := reconstruct_motion hs hc hc' D hg L z
  refine ⟨c, fun xs ys hd he => ?_⟩
  let A := powered P S
  have hA : z ^ P ∉ A := by
    intro h
    obtain ⟨x, hx, he⟩ := mem_image.mp h
    exact hz (power_injective p l he ▸ hx)
  have eqn : coupled P (denominatorPoly A xs) (denominatorPoly B ys) = poles S D := by
    rw [denominatorPoly, denominatorPoly, hd, he]
    exact paired_poles p l S B hB d e
  rw [← eqn] at h
  have key := h _ (degree_pair P (expChar_pow_pos F p l).ne' xs ys)
  rw [← eval_sphere _ _ _ hA, ← eval_sphere _ _ _ (fun h => hz (hB h))]
  simpa only [pairedCoeff, coupled, eval_mul, eval_comp, eval_pow, eval_X,
    div_mul_div_comm] using key

/-- The weighted energy after fusion is the sum of the two incident
energies plus the Laurent order, in units of `2P`. -/
theorem insertion_energy (P a b x y d e : ℕ) (j : ℤ) (v : ℤ × ℤ) (hv : v ∈ pairs P d e j) :
    (P : ℤ) * fusedEnergy a x v.1 + fusedEnergy b y v.2 =
      (P * a + b : ℕ) + (P * x + y : ℕ) + 2 * j := by
  unfold fusedEnergy
  push_cast
  linear_combination 2 * (mem_pairs hv).1

/-- Fusion through one specified level, or zero at a negative level. -/
def fusedAt (c : A) (a x : Wedge r) (ys : List (A × Mode r)) (i : ℤ) : F :=
  sew r (fusedEnergy (energy a.val) (energy x.val) i)
    (fun b => fusion F a.val x.val b.val) (fun b => stationary c b ys)

private theorem sphereCoeff_eq (c : A) (a x : Wedge r) (ys : List (A × Mode r))
    (hy : ∀ y ∈ ys, y.1 ≠ c) (i : ℤ) :
    sphereCoeff c.val (triple c a.val x.val ys) i = fusedAt c a x ys i :=
  coeff_fusion c a.val x.val ys hy i

/-- At an insertion mark each term fuses both incident legs. -/
theorem insertion_step (z : F) (hA : z ^ (p ^ l) ∈ A) (hB : z ∈ B)
    (a x : Wedge r) (b y : Wedge t) (ys : List (A × Mode r)) (ws : List (B × Mode t))
    (hy : ∀ i ∈ ys, i.1 ≠ ⟨z ^ (p ^ l), hA⟩) (hw : ∀ i ∈ ws, i.1 ≠ ⟨z, hB⟩) (j : ℤ) :
    let c : A := ⟨z ^ (p ^ l), hA⟩
    let f : B := ⟨z, hB⟩
    let u := triple c a.val x.val ys
    let v := triple f b.val y.val ws
    pairedCoeff (p ^ l) z u v j =
      ∑ q ∈ pairs (p ^ l) (weight u / 2) (weight v / 2) j,
        fusedAt c a x ys q.1 * fusedAt f b y ws q.2 := by
  intro c f u v
  let d := weight u / 2
  let e := weight v / 2
  let q₁ := poles (A.erase (z ^ (p ^ l))) (fun _ => d)
  let q₂ := poles (B.erase z) (fun _ => e)
  have h₁ : q₁.eval (z ^ (p ^ l)) ≠ 0 := poles_eval _ (notMem_erase _ _)
  have h₂ : q₂.eval z ≠ 0 := poles_eval _ (notMem_erase _ _)
  have h := coupled_coeff p l z (numerator A u) (numerator B v) q₁ q₂ d e h₁ h₂ j
  have ha : (X - C (z ^ (p ^ l))) ^ d * q₁ = denominatorPoly A u := (poles_split _ hA).symm
  have hb : (X - C z) ^ e * q₂ = denominatorPoly B v := (poles_split _ hB).symm
  dsimp only at h
  rw [ha, hb] at h
  unfold pairedCoeff
  rw [h]
  exact sum_congr rfl fun q _ =>
    congrArg₂ (· * ·) (sphereCoeff_eq c a x ys hy q.1) (sphereCoeff_eq f b y ws hw q.2)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-!
# Fixed-energy tables in paired motion

The order of the exterior arguments is fixed before interpolating. A
collision can take place at any stationary mark. Bringing that mark
and the moving site to the front contributes a scalar depending only
on the energy labels and the mark.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Finset Polynomial
open scoped Classical
variable {F : Type} [Field F] {S T : Finset F} {r t : ℕ}
variable {a : Option S → ℕ} {b : Option T → ℕ}

def rest (z : S) (x : States r a) : List (S × Mode r) :=
  (univ.erase z).toList.flatMap (marksAt (fun j => x (some j)))

def restWeight (z : S) (a : Option S → ℕ) := ∑ j ∈ univ.erase z, a (some j)

omit [Field F] in
theorem weight_rest (z : S) (x : States r a) : weight (rest z x) = restWeight z a := by
  rw [rest, weight_list, ← List.sum_toFinset _ (nodup_toList _), toList_toFinset]
  rfl

omit [Field F] in
theorem rest_avoids (z : S) (x : States r a) : ∀ y ∈ rest z x, y.1 ≠ z := by
  intro y hy
  obtain ⟨i, hi, h⟩ := List.mem_flatMap.mp hy
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
  exact (mem_erase.mp (mem_toList.mp hi)).1

def front (z : S) (x : States r a) : List (Option S × Mode r) :=
  triple z (x (some z)).val.val (x none).val.val (rest z x)

omit [Field F] in
theorem weight_front (z : S) (x : States r a) : weight (front z x) = weight (inputs x) := by
  rw [front, weight_triple, (x (some z)).property, (x none).property, weight_rest,
    weight_inputs, Fintype.sum_option]
  unfold restWeight
  have := sum_erase_add univ (fun i => a (some i)) (mem_univ z)
  omega

omit [Field F] in
theorem front_update (z : S) (x : States r a) (v : Level r (a (some z))) :
    front z (Function.update x (some z) v) = triple z v.val.val (x none).val.val (rest z x) := by
  have he : rest z (Function.update x (some z) v) = rest z x := by
    apply List.flatMap_congr
    intro i hi
    have hn : some i ≠ some z := by simpa using (mem_erase.mp (mem_toList.mp hi)).1
    simp [marksAt, hn]
  rw [front, he, Function.update_self, Function.update_of_ne (by simp : none ≠ some z)]

private theorem ordered (z : S) (a : Option S → ℕ) :
    ∃ c : F, c ≠ 0 ∧ ∀ x : States r a, numerator S (inputs x) = C c * numerator S (front z x) := by
  let l := some z :: none :: (univ.erase z).toList.map some
  have h : univ.toList.Perm l := by
    have hl : l.Nodup := by simp [l, List.nodup_map_iff (Option.some_injective _), nodup_toList]
    apply (List.perm_ext_iff_of_nodup (nodup_toList _) hl).mpr
    rintro (_ | i) <;> simp [l, eq_or_ne]
  obtain ⟨n, hn⟩ := wick_perm_sites (R := F[X]) (r := r) a h
  refine ⟨(-1) ^ n, by simp, fun x => ?_⟩
  have hh := hn _ (Routing.polynomial_skew (trajectories S)) x []
  simpa [l, numerator, Routing.correlatorPoly, front, triple, inputs, marksAt, rest,
    List.flatMap_map, List.map_flatMap, Function.comp_def] using hh

theorem coeff_scale (z c : F) (p q : F[X]) (j : ℤ) :
    (laurent z (C c * p) q).coeff j = c * (laurent z p q).coeff j := by
  simp only [laurent, taylor_mul, taylor_C, Polynomial.coe_mul, Polynomial.coe_C, map_mul,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, mul_div_assoc, HahnSeries.coeff_single_mul,
    sub_zero]

theorem reorder_left (z : S) (a : Option S → ℕ) :
    ∃ c : F, c ≠ 0 ∧ ∀ (x : States r a) (P : ℕ) (u : F) (ys : List (Option T × Mode t)) (j : ℤ),
      pairedCoeff P u (inputs x) ys j = c * pairedCoeff P u (front z x) ys j := by
  obtain ⟨c, hc, he⟩ := ordered (r := r) z a
  refine ⟨c, hc, fun x P u ys j => ?_⟩
  simp only [pairedCoeff, he, denominatorPoly, weight_front, coupled, mul_comp, C_comp, mul_assoc,
    coeff_scale]

theorem reorder_right (z : T) (b : Option T → ℕ) :
    ∃ c : F, c ≠ 0 ∧ ∀ (y : States t b) (P : ℕ) (u : F) (xs : List (Option S × Mode r)) (j : ℤ),
      pairedCoeff P u xs (inputs y) j = c * pairedCoeff P u xs (front z y) j := by
  obtain ⟨c, hc, he⟩ := ordered (r := t) z b
  refine ⟨c, hc, fun y P u xs j => ?_⟩
  simp only [pairedCoeff, he, denominatorPoly, weight_front, coupled]
  rw [mul_left_comm _ (C c), coeff_scale]

/-- Sum an arbitrary joint table on the two movers and all spectators.
Its entries are independent of the internal seam index. -/
theorem table_seam {B : Finset F} (p l : ℕ) [ExpChar F p] (z : F) (hz : z ^ (p ^ l) ∈ S)
    (hz' : z ∉ T) (c : B) (U V : Finset F) (hU : Disjoint U T) (hV : Disjoint V B)
    (a : Option S → ℕ) (b : Option T → ℕ) (H w : ℕ)
    (ht : T.card * ((∑ i, b i) / 2) < U.card)
    (hb : B.card * ((a (some ⟨z ^ (p ^ l), hz⟩) + a none + w) / 2) < V.card) :
    let P := p ^ l
    let d : S := ⟨z ^ P, hz⟩
    let e := a (some d)
    let m := a none
    ∃ (q : F) (L : (Wedge r →₀ F) →ₗ[F] (Wedge r →₀ F)) (f : ℕ → ℕ → V → F) (g : ℤ → U → F),
      q ≠ 0 ∧ (∀ x y : Wedge r, y ∈ (L (Finsupp.single x 1)).support →
        energy y.val ≤ energy x.val ∧ y.val.length = x.val.length) ∧
      ∀ (j : ℤ), (P * m + b none + 2 * P * H : ℕ) ≤ -j →
      ∀ (I : Type) (_ : Fintype I) (W : I → F) (x : I → States r a) (y : I → States t b)
        (fs : I → List (B × Mode r)), (∀ i k, k ∈ fs i → k.1 ≠ c) → (∀ i, weight (fs i) = w) →
        (∑ i, W i * ∑ h : Level r e,
          pairedCoeff P z (inputs (Function.update (x i) (some d) h)) (inputs (y i)) j *
            stationary c h.val (fs i)) =
          q * ∑ v ∈ pairs P ((e + m + restWeight d a) / 2) 0 j,
            let E := fusedEnergy e m v.1
            ∑ i, W i * (sew r E (fun h => stationary d h (rest d (x i)))
              (transported c V L (f E.toNat) (x i none).val (fs i)) *
              ∑ s : U, g v.2 s * wick fieldKernel ((inputs (y i)).map (atPoint s.val))) := by
  intro P d e m
  obtain ⟨q, hq, hr⟩ := reorder_left (r := r) (T := T) (t := t) d a
  rw [Fintype.sum_option] at ht
  let L := lowering F r
  obtain ⟨f, g, hL, h⟩ := seam_step (r := r) (t := t) p l z hz hz' c U V hU hV
    e m (b none) H (restWeight d a) _ w ht hb
  refine ⟨q, L, f, g, hq, hL, ?_⟩
  intro j hj I _ W x y fs hf hw
  have hv (i : I) := h j hj (x i none) (rest d (x i)) (inputs (y i)) (fs i)
    (rest_avoids d (x i)) (hf i) (weight_rest d (x i))
    (by rw [weight_inputs, Fintype.sum_option]) (hw i)
  simp only [hr, front_update, mul_assoc q, ← mul_sum]
  have eval (i : I) := (sew_nat e (fun a => pairedCoeff P z
    (triple d a.val (x i none).val.val (rest d (x i))) (inputs (y i)) j)
    (fun a => stationary c a (fs i))).symm.trans (hv i)
  simp only [eval, mul_left_comm _ q, ← mul_sum]
  congr 1
  simp only [mul_sum]
  rw [sum_comm]

/-- Simultaneous fusion at an insertion for any joint table of inputs. -/
theorem table_insertion (p l : ℕ) [ExpChar F p] (z : F) (hz : z ^ (p ^ l) ∈ S) (hz' : z ∈ T)
    (a : Option S → ℕ) (b : Option T → ℕ) :
    let P := p ^ l
    let c : S := ⟨z ^ P, hz⟩
    let d : T := ⟨z, hz'⟩
    ∃ q : F, q ≠ 0 ∧ ∀ (j : ℤ) (I : Type) (_ : Fintype I) (W : I → F)
      (x : I → States r a) (y : I → States t b),
      (∑ i, W i * pairedCoeff P z (inputs (x i)) (inputs (y i)) j) =
        q * ∑ v ∈ pairs P ((∑ i, a i) / 2) ((∑ i, b i) / 2) j, ∑ i, W i *
          (fusedAt c (x i (some c)).val (x i none).val (rest c (x i)) v.1 *
           fusedAt d (y i (some d)).val (y i none).val (rest d (y i)) v.2) := by
  intro P c d
  obtain ⟨q, hq, hr⟩ := reorder_left (r := r) (T := T) (t := t) c a
  obtain ⟨u, hu, hs⟩ := reorder_right (r := r) (S := S) (t := t) d b
  refine ⟨q * u, mul_ne_zero hq hu, ?_⟩
  intro j I _ W x y
  have H (i : I) : pairedCoeff P z (front c (x i)) (front d (y i)) j =
      ∑ v ∈ pairs P ((∑ i, a i) / 2) ((∑ i, b i) / 2) j,
        fusedAt c (x i (some c)).val (x i none).val (rest c (x i)) v.1 *
        fusedAt d (y i (some d)).val (y i none).val (rest d (y i)) v.2 := by
    rw [← weight_inputs (x i), ← weight_inputs (y i), ← weight_front c, ← weight_front d]
    exact insertion_step p l z hz hz' _ _ _ _ _ _ (rest_avoids c _) (rest_avoids d _) j
  simp only [hr, hs, H, ← mul_assoc q u, mul_left_comm _ (q * u), ← mul_sum]
  congr 1
  simp only [mul_sum]
  rw [sum_comm]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end
