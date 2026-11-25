import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Gadget
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

section
/-! # A strict comparison at six sites -/

open scoped NNReal

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable (K : Type) [Field K]

/-- The sites are A, B, C, D, M, N in that order. -/
def sixPair : Fin 8 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 4), (2, 4), (3, 5), (1, 2), (1, 5), (2, 5), (3, 4)]

def sixDemand : Tensor K (Fin 6) := wire K 0 1 2 * wire K 2 3 2

def sixSupply (i : Fin 8) : Tensor K (Fin 6) :=
  wire K (sixPair i).1 (sixPair i).2 2

private def edge (i : Fin 8) : Finset (Fin 6) := {(sixPair i).1, (sixPair i).2}

private theorem six_connected : (2 : Tensor K (Fin 6)) ≤ ∏ i, sixSupply K i := by
  let covered (U : Finset (Fin 8)) := shared K (U.biUnion edge) 2 ≤ ∏ i ∈ U, sixSupply K i
  have extend {U : Finset (Fin 8)} (h : covered U) (i : Fin 8) (s : Fin 6)
      (hi : i ∉ U) (hs : s ∈ edge i) (ht : s ∈ U.biUnion edge) : covered (insert i U) := by
    unfold covered
    rw [Finset.biUnion_insert, Finset.prod_insert hi]
    exact (shared_join K hs ht 2).trans (mul_le_mul_left _ _ _ h)
  have h0 : covered {0} := by simp [covered, edge, sixSupply, wire]
  have h1 := extend h0 1 0 (by decide) (by decide) (by decide)
  have h2 := extend h1 4 2 (by decide) (by decide) (by decide)
  have h3 := extend h2 5 1 (by decide) (by decide) (by decide)
  have h4 := extend h3 3 5 (by decide) (by decide) (by decide)
  unfold covered at h4
  rw [show ({3, 5, 4, 1, 0} : Finset (Fin 8)).biUnion edge = Finset.univ by decide,
    shared_all, Nat.cast_ofNat] at h4
  let : MulLeftMono (Tensor K (Fin 6)) := ⟨fun c a b h => mul_le_mul_left a b c h⟩
  exact h4.trans (Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
    (fun _ _ _ => one_le_wire K _ _ (by decide)))

/-- Equality would put M and N at the midpoint of CD and then both
C and M at the midpoint of AB. All eight supply lengths would vanish. -/
private theorem six_gap (f : Tensor K (Fin 6) →+* ℝ) (hf : Monotone f) :
    ∃ i, f (sixDemand K) < f (sixSupply K i) ^ 4 := by
  by_contra! bad
  let d := dist f
  let l := (d 0 1 + d 2 3) / 4
  have edge_le (i : Fin 8) : d (sixPair i).1 (sixPair i).2 ≤ l := by
    have h := bad i
    simp only [sixDemand, sixSupply, f.map_mul, price_wire f hf _ _ (n := 2) (by decide),
      Nat.cast_ofNat, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] at h
    have := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h
    unfold l d
    linarith
  have tri : ∀ a b c, d a c ≤ d a b + d b c := dist_triangle f hf
  have sym : ∀ a b, d a b = d b a := dist_comm f
  have ac : d 0 2 ≤ l := edge_le 0
  have am : d 0 4 ≤ l := edge_le 1
  have cm : d 2 4 ≤ l := edge_le 2
  have nd : d 5 3 ≤ l := (sym 5 3).le.trans (edge_le 3)
  have cb : d 2 1 ≤ l := (sym 2 1).le.trans (edge_le 4)
  have nb : d 5 1 ≤ l := (sym 5 1).le.trans (edge_le 5)
  have cn : d 2 5 ≤ l := edge_le 6
  have md : d 4 3 ≤ l := (sym 4 3).le.trans (edge_le 7)
  have ab : d 0 1 = 2 * l := by
    have : 4 * l = d 0 1 + d 2 3 := by unfold l; ring
    linarith [tri 0 2 1, tri 2 4 3]
  have cd : d 2 3 = 2 * l := by unfold l at ab ⊢; linarith
  have mid {a b c x} (hab : d a b = 2 * l) (h₁ : d a c ≤ l) (h₂ : d c b ≤ l)
      (h₃ : d a x ≤ l) (h₄ : d x b ≤ l) : d c x = 0 := by
    have h (z : Fin 6) (ha : d a z ≤ l) (hb : d z b ≤ l) :
        d a z = d a b / 2 ∧ d z b = d a b / 2 := by
      constructor <;> linarith [tri a z b]
    exact unique_midpoint f hf (h c h₁ h₂).1 (h c h₁ h₂).2 (h x h₃ h₄).1 (h x h₃ h₄).2
  have mn := mid cd cm md cn nd
  have mb : d 4 1 ≤ l := by linarith [tri 4 5 1]
  have h := mid ab ac cb am mb
  have hl : l = 0 := by linarith [tri 2 4 3]
  have hu (i : Fin 8) : f (sixSupply K i) = 1 := by
    have he := le_antisymm ((edge_le i).trans_eq hl) (dist_nonneg f hf _ _)
    unfold d at he
    rw [sixSupply, price_wire f hf _ _ (by decide), he, Real.rpow_zero]
  have := hf (six_connected K)
  simp only [map_ofNat, map_prod, hu, Finset.prod_const_one] at this
  norm_num at this

/-- Two demands can be supplied with strictly fewer than four wires
per block, up to a bounded direct sum independent of the power. -/
theorem six_site :
    ∃ (b C : ℕ) (H : Finset (Fin 8 → ℕ)), 0 < b ∧ (∀ h ∈ H, ∑ i, h i < 4 * b) ∧
      ∀ z : ℕ, 0 < z → sixDemand K ^ (b * z) ≤
        (C : Tensor K (Fin 6)) * ∑ h ∈ H, ∏ i, sixSupply K i ^ (h i * z) := by
  refine Spectrum.powered_gadget add_le_add_right mul_le_mul_left zero_le one_le exists_bound
    _ _ _ (by decide) (fun _ => one_le_wire K _ _ (by decide)) ?_ (six_connected K)
  intro g hg
  obtain ⟨i, hi⟩ := six_gap K (NNReal.toRealHom.comp g) (fun a b h => hg h)
  exact ⟨i, NNReal.coe_lt_coe.mp hi⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
end

/-!
# A uniform gap for metric squares

Placement preserves products and can only lower the price of a direct
sum. Taking powers removes the fixed overhead in the six-site comparison.
Identifying two pairs of sites gives a saving for squares at every scale.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

private theorem remove_factor {x y C : ℝ} (hy : 0 < y)
    (h : ∀ z : ℕ, 0 < z → x ^ z ≤ C * y ^ z) : x ≤ y := by
  by_contra! bad
  obtain ⟨z, hz⟩ := pow_unbounded_of_one_lt (max C 1) ((one_lt_div hy).mpr bad)
  have hz' : 0 < z := by
    by_contra! hn
    rw [Nat.eq_zero_of_le_zero hn, pow_zero] at hz
    exact not_lt_of_ge (le_max_right _ _) hz
  rw [div_pow] at hz
  exact not_lt_of_ge (h z hz') ((lt_div_iff₀ (pow_pos hy z)).mp ((le_max_left C 1).trans_lt hz))

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S]

private theorem placed_bound
    {b C : ℕ} {H : Finset (Fin 8 → ℕ)} (hbudget : ∀ h ∈ H, ∑ i, h i < 4 * b)
    (hcomp : ∀ z : ℕ, 0 < z → sixDemand K ^ (b * z) ≤
      (C : Tensor K (Fin 6)) * ∑ h ∈ H, ∏ i, sixSupply K i ^ (h i * z))
    (f : Tensor K S →+* ℝ) (hf : Monotone f) (p : Fin 6 → S) (m : ℝ) (hm : 0 ≤ m)
    (hs : ∀ i, dist f (p (sixPair i).1) (p (sixPair i).2) ≤ m) :
    (dist f (p 0) (p 1) + dist f (p 2) (p 3)) * b ≤ m * (4 * b - 1 : ℕ) := by
  classical
  let g : Tensor K (Fin 6) →* ℝ :=
    { toFun := fun X => f (place p X)
      map_one' := by rw [place_one, f.map_one]
      map_mul' := fun X Y => by rw [place_mul, f.map_mul] }
  have mono : Monotone g := hf.comp (place_mono p)
  have gz : g 0 = 0 := by change f (place p 0) = 0; rw [place_zero, f.map_zero]
  have pos (X) : 0 ≤ g X := gz ▸ mono (zero_le X)
  have sum_le (U : Finset (Fin 8 → ℕ)) (F : (Fin 8 → ℕ) → Tensor K (Fin 6)) :
      g (∑ h ∈ U, F h) ≤ ∑ h ∈ U, g (F h) := by
    induction U using Finset.induction_on with
    | empty => simp [gz]
    | insert h U hh ih =>
      rw [Finset.sum_insert hh, Finset.sum_insert hh]
      refine le_trans ?_ (add_le_add le_rfl ih)
      exact (hf (place_add_le p _ _)).trans_eq (f.map_add _ _)
  have gw (i j : Fin 6) : g (wire K i j 2) = (2 : ℝ) ^ dist f (p i) (p j) := by
    change f (place p _) = _
    rw [place_wire, price_wire f hf _ _ (by decide), Nat.cast_ofNat]
  let R := (2 : ℝ) ^ m
  have hr : 1 ≤ R := Real.one_le_rpow (by norm_num) hm
  have hwire (i) : g (sixSupply K i) ≤ R := by
    rw [sixSupply, gw]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hs i)
  have h : g (sixDemand K) ^ b ≤ R ^ (4 * b - 1) := by
    apply remove_factor (C := g C * H.card) (by positivity)
    intro z hz
    let F (h : Fin 8 → ℕ) := ∏ i, sixSupply K i ^ (h i * z)
    have term (h) (hh : h ∈ H) : g (F h) ≤ (R ^ (4 * b - 1)) ^ z := by
      unfold F
      rw [map_prod]
      simp only [map_pow]
      calc
        _ ≤ ∏ i, R ^ (h i * z) := Finset.prod_le_prod₀
          (fun i _ => pow_nonneg (pos _) _) (fun i _ => pow_le_pow_left₀ (pos _) (hwire i) _)
        _ = R ^ ((∑ i, h i) * z) := by rw [Finset.prod_pow_eq_pow_sum, Finset.sum_mul]
        _ ≤ _ := by
          rw [← pow_mul]
          exact pow_le_pow_right₀ hr (Nat.mul_le_mul_right z (Nat.le_sub_one_of_lt (hbudget h hh)))
    rw [← pow_mul, ← map_pow, mul_assoc]
    refine (mono (hcomp z hz)).trans ?_
    rw [g.map_mul]
    apply mul_le_mul_of_nonneg_left _ (pos _)
    refine (sum_le H F).trans ?_
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul H (fun h => g (F h)) _ term
  rw [sixDemand, g.map_mul, gw, gw, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)] at h
  unfold R at h
  simp only [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h

/-- A gap relative to the longest side gives a squared gap. The loss
controls both the variance of the four sides and the diagonal deficit. -/
private theorem squared_gap {a b c d x y δ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hδ : 0 ≤ δ)
    (hx' : 2 * x ≤ a + b + c + d) (hy' : 2 * y ≤ a + b + c + d)
    (hgap : x + y ≤ (4 - δ) * max (max a b) (max c d)) :
    x ^ 2 + y ^ 2 ≤ (2 - δ ^ 2 / 80) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  let m := max (max a b) (max c d)
  let u := a + b + c + d
  let v := a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
  let e := 2 * v - (x ^ 2 + y ^ 2)
  change x + y ≤ (4 - δ) * m at hgap
  change 2 * x ≤ u at hx'
  change 2 * y ≤ u at hy'
  have ham : a ≤ m := (le_max_left a b).trans (le_max_left _ _)
  have hbm : b ≤ m := (le_max_right a b).trans (le_max_left _ _)
  have hcm : c ≤ m := (le_max_left c d).trans (le_max_right _ _)
  have hdm : d ≤ m := (le_max_right c d).trans (le_max_right _ _)
  have hv : v ≤ 4 * m ^ 2 := by
    unfold v
    linarith only [pow_le_pow_left₀ ha ham 2, pow_le_pow_left₀ hb hbm 2,
      pow_le_pow_left₀ hc hcm 2, pow_le_pow_left₀ hd hdm 2]
  have dev : (4 * m - u) ^ 2 ≤ 4 * (4 * v - u ^ 2) := by
    have eqn : 4 * (4 * v - u ^ 2) = (4 * a - u) ^ 2 + (4 * b - u) ^ 2 + (4 * c - u) ^ 2 + (4 * d - u) ^ 2 := by
      unfold v u
      ring
    rw [eqn]
    have h (s t : ℝ) : (4 * max s t - u) ^ 2 ≤ (4 * s - u) ^ 2 + (4 * t - u) ^ 2 := by
      rcases le_total s t with h | h
      · rw [max_eq_right h]; exact le_add_of_nonneg_left (sq_nonneg _)
      · rw [max_eq_left h]; exact le_add_of_nonneg_right (sq_nonneg _)
    unfold m
    linarith only [h (max a b) (max c d), h a b, h c d]
  have loss : (4 * v - u ^ 2) + (u - x - y) ^ 2 ≤ 2 * e := by
    unfold e
    nlinarith only [mul_le_mul_of_nonneg_left hx' hx, mul_le_mul_of_nonneg_left hy' hy,
      mul_nonneg (show 0 ≤ u - x - y by linarith) (add_nonneg hx hy)]
  have hp := mul_nonneg hδ (ha.trans ham)
  have hs := pow_le_pow_left₀ hp (show δ * m ≤ 4 * m - x - y by linarith only [hgap]) 2
  have hh : (δ * m) ^ 2 ≤ 20 * e := by
    nlinarith only [hs, loss, dev, sq_nonneg (4 * m - u), sq_nonneg (u - x - y),
      sq_nonneg ((4 * m - u) - (u - x - y))]
  unfold e at hh
  change _ ≤ _ * v
  nlinarith only [hh, mul_le_mul_of_nonneg_left hv (sq_nonneg δ)]

/-- A single constant works for every spectral point on every finite site set. -/
theorem square (K : Type) [Field K] :
    ∃ κ : ℝ, 1 < κ ∧ κ < 2 ∧
      ∀ (S : Type) [Fintype S] [Nonempty S] [DecidableEq S]
        (f : Tensor K S →+* ℝ), Monotone f → ∀ a b c d : S,
        (dist f a c) ^ 2 + (dist f b d) ^ 2 ≤
          κ * ((dist f a b) ^ 2 + (dist f b c) ^ 2 + (dist f c d) ^ 2 + (dist f d a) ^ 2) := by
  obtain ⟨n, C, H, hn, hbudget, hcomp⟩ := six_site K
  let δ := (n : ℝ)⁻¹
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hp : 0 < δ := inv_pos.mpr hn'
  have hle : δ ≤ 1 := (inv_le_one₀ hn').mpr (by exact_mod_cast hn)
  refine ⟨2 - δ ^ 2 / 80, by nlinarith, by nlinarith, ?_⟩
  intro S _ _ _ f hf a b c d
  let r := dist f
  have tri : ∀ a b c, r a c ≤ r a b + r b c := dist_triangle f hf
  have sym : ∀ a b, r a b = r b a := dist_comm f
  have nn : ∀ a b, 0 ≤ r a b := dist_nonneg f hf
  refine squared_gap (nn a b) (nn b c) (nn c d) (nn d a) (nn a c) (nn b d) hp.le ?_ ?_ ?_
  · linarith [tri a b c, tri c d a, sym a c]
  · linarith [tri b c d, tri d a b, sym b d]
  let m := max (max (r a b) (r b c)) (max (r c d) (r d a))
  have h₁ : r a b ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have h₂ : r b c ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have h₃ : r c d ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have h₄ : r d a ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hm := (nn a b).trans h₁
  let p : Fin 6 → S := ![a, c, b, d, a, c]
  have hs (i : Fin 8) : r (p (sixPair i).1) (p (sixPair i).2) ≤ m := by
    fin_cases i
    · exact h₁
    · exact (dist_self f a).le.trans hm
    · exact (sym b a).le.trans h₁
    · exact (sym d c).le.trans h₃
    · exact (sym c b).le.trans h₂
    · exact (dist_self f c).le.trans hm
    · exact h₂
    · exact h₄
  have hh : (r a c + r b d) * n ≤ m * (4 * n - 1 : ℕ) :=
    placed_bound hbudget hcomp f hf p m hm hs
  rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hh
  apply (mul_le_mul_iff_left₀ hn').mp
  change (r a c + r b d) * n ≤ (4 - δ) * m * n
  refine hh.trans_eq ?_
  unfold δ
  field_simp

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Simultaneous antipodal wires on a binary cube

Take all ordered antipodal pairs. Their aggregate cost, divided by
the dimension and number of pairs, can be made arbitrarily small.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable (K : Type) [Field K]

def cubeDemand (n : ℕ) : Tensor K (Cube n) :=
  ∏ x, wire K x (Cube.flip Finset.univ x) 2

def cubeSupply (n : ℕ) (i : Cube n × Fin n) : Tensor K (Cube n) :=
  wire K i.1 (Cube.flip {i.2} i.1) 2

private theorem cube_gap {κ : ℝ} (hk : 0 ≤ κ) (k L : ℕ)
    (hs : (L : ℝ) ^ 2 * (2 * κ) ^ k < ((2 : ℝ) ^ k) ^ 2)
    (f : Tensor K (Cube (2 ^ k)) →+* ℝ) (hf : Monotone f)
    (hq : ∀ a b c e, (dist f a c) ^ 2 + (dist f b e) ^ 2 ≤
      κ * ((dist f a b) ^ 2 + (dist f b c) ^ 2 + (dist f c e) ^ 2 + (dist f e a) ^ 2)) :
    ∃ i, f (cubeDemand K (2 ^ k) ^ L) < f (cubeSupply K (2 ^ k) i) ^ (2 ^ k * Fintype.card (Cube (2 ^ k))) := by
  let n := 2 ^ k
  let N := Fintype.card (Cube n)
  let D := ∑ x, dist f x (Cube.flip Finset.univ x)
  let w (i : Cube n × Fin n) := dist f i.1 (Cube.flip {i.2} i.1)
  have hN : (0 : ℝ) < N := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Cube n))
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by unfold n; positivity)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ w Finset.univ_nonempty
  have he (j) : w j ≤ w i := hi j (Finset.mem_univ _)
  have hw : 0 < w i := by
    by_contra! bad
    have hz (j : Cube n × Fin n) : dist f j.1 (Cube.flip {j.2} j.1) = 0 :=
      le_antisymm ((he j).trans bad) (dist_nonneg f hf _ _)
    have hp (j : Cube n × Fin n) : f (wire K j.1 (Cube.flip {j.2} j.1) 2) = 1 := by
      rw [price_wire f hf _ _ (by decide), hz, Real.rpow_zero]
    have h := hf (cube_connected K n)
    simp only [map_ofNat, map_prod, hp, Finset.prod_const_one] at h
    norm_num at h
  have hbound := Cube.energy_bound (dist f) hq hk (m := (w i) ^ 2)
    (fun x j => pow_le_pow_left₀ (dist_nonneg f hf _ _) (he (x, j)) _) k Finset.univ (by simp)
  have hcauchy : D ^ 2 ≤ N * Cube.energy (dist f) Finset.univ := by
    simpa [D, N, Cube.energy] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Cube n => (1 : ℝ)) (fun x => dist f x (Cube.flip Finset.univ x))
  have h : ((L : ℝ) * D) ^ 2 < ((n : ℝ) * N * w i) ^ 2 := calc
    _ ≤ (L : ℝ) ^ 2 * (N * ((2 * κ) ^ k * N * (w i) ^ 2)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (hcauchy.trans (mul_le_mul_of_nonneg_left hbound hN.le))
        (sq_nonneg _)
    _ = ((L : ℝ) ^ 2 * (2 * κ) ^ k) * ((N : ℝ) * w i) ^ 2 := by ring
    _ < ((2 : ℝ) ^ k) ^ 2 * ((N : ℝ) * w i) ^ 2 := mul_lt_mul_of_pos_right hs (by positivity)
    _ = _ := by unfold n; push_cast; ring
  have hl : (L : ℝ) * D < (n : ℝ) * N * w i := by
    by_contra! bad
    exact h.not_ge (pow_le_pow_left₀ (by positivity) bad _)
  refine ⟨i, ?_⟩
  simp only [cubeDemand, cubeSupply, map_pow, map_prod, price_wire f hf _ _ (n := 2) (by decide),
    Nat.cast_ofNat, ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  apply (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr
  rw [Nat.cast_mul]
  exact (mul_comm D _).trans_lt (hl.trans_eq (mul_comm _ _))

private theorem cube_dimension {κ : ℝ} (h1 : 1 < κ) (h2 : κ < 2) (L k₀ : ℕ) :
    ∃ k ≥ k₀, (L : ℝ) ^ 2 * (2 * κ) ^ k < ((2 : ℝ) ^ k) ^ 2 := by
  have hr : 1 < 4 / (2 * κ) := (one_lt_div (by positivity)).mpr (by linarith)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((L : ℝ) ^ 2) hr
  refine ⟨max j k₀, le_max_right _ _, ?_⟩
  have hg := hj.trans_le (pow_le_pow_right₀ hr.le (le_max_left j k₀))
  rw [div_pow, lt_div_iff₀ (by positivity)] at hg
  simpa only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm] using hg

theorem cube_site (L k₀ : ℕ) (hL : 0 < L) :
    ∃ n ≥ k₀, ∃ (b C : ℕ) (H : Finset (Cube n × Fin n → ℕ)), 0 < b ∧
      (∀ h ∈ H, L * ∑ i, h i < n * Fintype.card (Cube n) * b) ∧
      ∀ z : ℕ, 0 < z → cubeDemand K n ^ (b * z) ≤
        (C : Tensor K (Cube n)) * ∑ h ∈ H, ∏ i, cubeSupply K n i ^ (h i * z) := by
  obtain ⟨κ, h1, h2, hq⟩ := square K
  obtain ⟨k, hk, hs⟩ := cube_dimension h1 h2 L k₀
  let n := 2 ^ k
  have hn : 0 < n := by unfold n; positivity
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hsize : 0 < n * Fintype.card (Cube n) := Nat.mul_pos hn Fintype.card_pos
  obtain ⟨b, C, H, hb, hcost, hcomp⟩ := Spectrum.powered_gadget
    add_le_add_right mul_le_mul_left zero_le one_le exists_bound
    (cubeDemand K n ^ L) (cubeSupply K n) _ hsize
    (fun _ => one_le_wire K _ _ (by decide)) (by
      intro g hg
      let f := NNReal.toRealHom.comp g
      have hf : Monotone f := fun _ _ h => hg h
      obtain ⟨i, hi⟩ := cube_gap K (by linarith) k L hs f hf (hq _ f hf)
      exact ⟨i, NNReal.coe_lt_coe.mp hi⟩) (cube_connected K n)
  refine ⟨n, hk.trans (Nat.lt_two_pow_self (n := k)).le, L * b, C, H, Nat.mul_pos hL hb, ?_, ?_⟩
  · intro h hh
    exact (Nat.mul_lt_mul_of_pos_left (hcost h hh) hL).trans_eq (by ring)
  · intro z hz
    rw [Nat.mul_assoc, pow_mul]
    exact hcomp z hz

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
