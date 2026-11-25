import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.System
import OAI.LinearAlgebra.MatrixExponent.Coloring.Pad
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.ViaEmbedding
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Colours
import OAI.LinearAlgebra.MatrixExponent.Coloring.Chart
import Batteries.Tactic.OpenPrivate

section
/-!
# Numbering digit words and product coordinates

A digit vector represents the sum of its entries times the
corresponding radix powers. The spare coordinate occupies the
least significant position of the resulting mixed-radix number.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring

abbrev count (M h : ℕ) := M ^ (length M h) * spare M h

def number (M h : ℕ) : Words M h ≃ Fin (count M h) :=
  (finFunctionFinEquiv.prodCongr (.refl _)).trans finProdFinEquiv

variable {M : ℕ}

theorem spare_le (hM : 1 < M) (h : ℕ) : spare M h ≤ M := by
  have he := Nat.lt_pow_succ_log_self hM (2 ^ h)
  rw [pow_succ] at he
  apply (Nat.div_lt_iff_lt_mul (show 0 < M ^ (length M h) by positivity)).mpr
  rw [mul_comm]
  exact (Nat.sub_le _ _).trans_lt he

theorem count_bounds (hM : 1 < M) (h : ℕ) : 2 ^ h ≤ count M h ∧ count M h < 2 ^ (h + 1) := by
  let a := M ^ (length M h)
  let n := 2 ^ h
  have hn : 0 < n := Nat.two_pow_pos h
  have ha : 0 < a := by unfold a; positivity
  have hlo : a ≤ n := Nat.pow_log_le_self M hn.ne'
  have lower : n - 1 < a * ((n - 1) / a + 1) := by
    rw [mul_comm]
    exact (Nat.div_lt_iff_lt_mul ha).mp (Nat.lt_succ_self _)
  have upper : a * ((n - 1) / a + 1) ≤ n - 1 + a := by
    rw [mul_add, mul_one, mul_comm a]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  rw [pow_succ]
  change n ≤ a * ((n - 1) / a + 1) ∧ a * ((n - 1) / a + 1) < n * 2
  omega

def embed (hM : 1 < M) (h : ℕ) : Words M h ↪ B (h + 1) :=
  (number M h).toEmbedding.trans (Fin.castLEEmb (count_bounds hM h).2.le)

def base (hM : 1 < M) (h : ℕ) : B h ↪ Words M h :=
  (Fin.castLEEmb (count_bounds hM h).1).trans (number M h).symm.toEmbedding

theorem initial (hM : 1 < M) (h : ℕ) (i : B h) : (embed hM h (base hM h i)).val = i.val := by
  change ((number M h) ((number M h).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem embed_range (hM : 1 < M) (h : ℕ) (i : B (h + 1)) :
    i.val < count M h ↔ ∃ x, embed hM h x = i := by
  constructor
  · intro hi
    refine ⟨(number M h).symm ⟨i.val, hi⟩, Fin.ext ?_⟩
    change ((number M h) ((number M h).symm _)).val = _
    rw [Equiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact ((number M h) x).isLt

def packDigit (hM : 1 < M) (p : Equiv.Perm (Fin M)) (h : ℕ) (i : B (h + 1)) : B (h + 1) :=
  if hi : i.val < count M h then
    embed hM h (digitPerm p h ((number M h).symm ⟨i.val, hi⟩))
  else i

theorem packDigit_eq (hM : 1 < M) (p : Equiv.Perm (Fin M)) (h : ℕ) :
    packDigit hM p h = ⇑((digitPerm p h).viaEmbedding (embed hM h)) := by
  funext i
  by_cases hi : i.val < count M h
  · obtain ⟨x, rfl⟩ := (embed_range hM h i).mp hi
    rw [Equiv.Perm.viaEmbedding_apply, packDigit, dite_eq_left hi]
    exact congrArg (embed hM h ∘ digitPerm p h) ((number M h).symm_apply_apply x)
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ (mt (embed_range hM h i).mpr hi),
      packDigit, dite_eq_right hi]

namespace ProductChart
variable (p : ProductChart M) (h : ℕ)

abbrev rows := p.c.val ^ (length M h) * p.a.val ^ (length M h)
abbrev degree := p.b.val ^ (length M h) * spare M h

def row : ((Fin (length M h) → Fin p.c.val) × (Fin (length M h) → Fin p.a.val)) ≃
    Fin (p.rows h) :=
  (finFunctionFinEquiv.prodCongr finFunctionFinEquiv).trans finProdFinEquiv

def column : ((Fin (length M h) → Fin p.b.val) × Fin (spare M h)) ≃ Fin (p.degree h) :=
  (finFunctionFinEquiv.prodCongr (.refl _)).trans finProdFinEquiv

def grid : Words M h ≃ Fin (p.rows h) × Fin (p.degree h) :=
  ((p.apply h).trans (Equiv.prodAssoc _ _ _).symm).trans ((p.row h).prodCongr (p.column h))

theorem area : p.rows h * p.degree h = count M h := by
  simpa only [Fintype.card_fin, Fintype.card_prod] using
    Fintype.card_congr ((p.grid h).symm.trans (number M h))

theorem degree_pos (hM : 1 < M) : 0 < p.degree h := by
  have := (Nat.two_pow_pos h).trans_le (count_bounds hM h).1
  rw [← p.area h] at this
  exact Nat.pos_of_mul_pos_left this

end ProductChart
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Computing the three permutations of a product chart

The two coordinate systems are the digit word and its row and column
in the projected grid. Both use explicit radix arithmetic in both
directions. The labels reserved for matching are the row offsets in
increasing order. No table in the construction needs a search through
all bijections or a choice of a new ordering at each height.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring (B Perm Regular)
open private degree_packed inverse_agrees from OAI.LinearAlgebra.MatrixExponent.Coloring.Chart

structure Chart (h : ℕ) where
  base : B h → B h
  location : B h → B h
  mask : B h → Bool
  support : Reservation h
  degree : ℕ

namespace Chart
variable {h : ℕ} (p : Chart h)

def label (y : B h → B h) := colours p.support p.degree p.base (p.base ∘ y) p.mask

def route (b c : B h → B h) (i : B h) : B h :=
  if p.mask i then p.location (b i + c i) else i

def left (y : B h → B h) := p.route p.base (p.label y)
def right (y : B h → B h) := p.route (p.base ∘ y) (p.label y)

def run (inv : (B h → B h) → (B h → B h)) (y : B h → B h) :=
  (y ∘ inv (p.right y), p.right y ∘ inv (p.left y), p.left y)

end Chart

variable {M : ℕ} (hM : 1 < M) (p : ProductChart M) (h : ℕ)

include hM in
private theorem fits : p.rows h * p.degree h ≤ 2 ^ (h + 1) := by
  rw [p.area h]
  exact (count_bounds hM h).2.le

private def cell : Fin (p.rows h) × Fin (p.degree h) ↪ B (h + 1) :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb (fits hM p h))

private def offset : Fin (p.rows h) ↪ B (h + 1) :=
  ⟨fun i => cell hM p h (i, ⟨0, p.degree_pos h hM⟩),
    fun _ _ he => congrArg Prod.fst ((cell hM p h).injective he)⟩

private theorem offset_add (i : Fin (p.rows h)) (j : B (h + 1)) (hj : j.val < p.degree h) :
    offset hM p h i + j = cell hM p h (i, ⟨j.val, hj⟩) := by
  apply Fin.ext
  change ((finProdFinEquiv (i, ⟨0, p.degree_pos h hM⟩)).val + j.val) % 2 ^ (h + 1) =
    (finProdFinEquiv (i, ⟨j.val, hj⟩)).val
  have hl := (finProdFinEquiv (i, ⟨j.val, hj⟩)).isLt.trans_le (fits hM p h)
  simp only [finProdFinEquiv_apply_val, zero_add] at hl ⊢
  rw [Nat.add_comm, Nat.mod_eq_of_lt hl]

def reservation : Reservation (h + 1) where
  size := p.rows h
  assign i := if hi : i < p.rows h then offset hM p h ⟨i, hi⟩ else 0
  unique := by
    intro i hi j hj he
    change i < p.rows h at hi
    change j < p.rows h at hj
    simp only [dite_eq_left hi, dite_eq_left hj] at he
    exact congrArg Fin.val ((offset hM p h).injective he)

private theorem reservation_support :
    (reservation hM p h).support = Finset.univ.image (offset hM p h) := by
  ext i
  simp only [Reservation.support, Finset.mem_image, Finset.mem_range, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, he⟩
    change j < p.rows h at hj
    exact ⟨⟨j, hj⟩, by simpa only [reservation, dite_eq_left hj] using he⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, j.isLt, by simp only [reservation, dite_eq_left j.isLt, Fin.eta]⟩

def chart : Chart (h + 1) where
  base i := if hi : i.val < count M h then
    offset hM p h (p.grid h ((number M h).symm ⟨i.val, hi⟩)).1
  else i
  location i := if hi : i.val < p.rows h * p.degree h then
    embed hM h ((p.grid h).symm (finProdFinEquiv.symm ⟨i.val, hi⟩))
  else i
  mask i := decide (i.val < count M h)
  support := reservation hM p h
  degree := p.degree h

theorem chart_mask (i : B (h + 1)) :
    (chart hM p h).mask i = true ↔ ∃ x, embed hM h x = i :=
  decide_eq_true_iff.trans (embed_range hM h i)

private theorem chart_base (x : Words M h) :
    (chart hM p h).base (embed hM h x) = offset hM p h (p.grid h x).1 := by
  have hx := (embed_range hM h _).mpr ⟨x, rfl⟩
  simp only [chart, dite_eq_left hx]
  exact congrArg (fun y => offset hM p h (p.grid h y).1) ((number M h).symm_apply_apply x)

private theorem chart_location (a : Fin (p.rows h)) (i : B (h + 1)) (hi : i.val < p.degree h) :
    (chart hM p h).location (offset hM p h a + i) =
      embed hM h ((p.grid h).symm (a, ⟨i.val, hi⟩)) := by
  rw [offset_add hM p h a i hi]
  let v : Fin (p.rows h) × Fin (p.degree h) := (a, ⟨i.val, hi⟩)
  have hv : (cell hM p h v).val < p.rows h * p.degree h := (finProdFinEquiv v).isLt
  change (chart hM p h).location (cell hM p h v) = _
  simp only [chart, dite_eq_left hv]
  exact congrArg (embed hM h ∘ (p.grid h).symm) (finProdFinEquiv.symm_apply_apply v)

variable (inv : (B (h + 1) → B (h + 1)) → (B (h + 1) → B (h + 1)))
    (hi : ∀ g : Equiv.Perm (B (h + 1)), inv g = ⇑g.symm)

include hi in
private theorem product_routes (g : Equiv.Perm (Words M h)) (y : B (h + 1) → B (h + 1))
    (hy : ∀ i, y (embed hM h i) = embed hM h (g i)) :
    let t := p.grid h
    let e := embed hM h
    let r := (chart hM p h).run inv y
    ∃ w v : Equiv.Perm (Words M h), (∀ i, (t (w i)).1 = (t i).1 ∧
      (t (v i)).1 = (t (g i)).1 ∧ (t (w i)).2 = (t (v i)).2) ∧
      (∀ i, r.1 (e (v i)) = e (g i)) ∧ (∀ i, r.2.1 (e (w i)) = e (v i)) ∧
      (∀ i, r.2.2 (e i) = e (w i)) := by
  classical
  let t := p.grid h
  let e := embed hM h
  let o := offset hM p h
  let C := chart hM p h
  let d := p.degree h
  have hmask (i) : C.mask i = true ↔ ∃ j, e j = i := chart_mask hM p h i
  have live (i) : C.mask (e i) = true := (hmask _).mpr ⟨i, rfl⟩
  have base (i) : C.base (e i) = o (t i).1 := chart_base hM p h i
  have loc (a : Fin (p.rows h)) (i : B (h + 1)) (hh : i.val < d) :
      C.location (o a + i) = e (t.symm (a, ⟨i.val, hh⟩)) := chart_location hM p h a i hh
  have target (i) : (C.base ∘ y) (e i) = o (t (g i)).1 :=
    (congrArg C.base (hy i)).trans (base (g i))
  have reg : Regular C.support.support d C.base (C.base ∘ y) C.mask := by
    change Regular (reservation hM p h).support _ _ _ _
    rw [reservation_support]
    exact ⟨degree_packed t e o C.mask hmask _ base, degree_packed (g.trans t) e o C.mask hmask _ target⟩
  have bound : C.support.size * d ≤ 2 ^ (h + 1) := fits hM p h
  have hr : 0 < p.rows h := Nat.zero_lt_of_lt (t (Uniform.base hM h 0)).1.isLt
  have hd : d ≤ 2 ^ (h + 1) := (Nat.le_mul_of_pos_left d hr).trans bound
  have col := edge_coloring C.support d hd bound C.base (C.base ∘ y) C.mask reg
  let c (i : Words M h) : Fin d := ⟨(C.label y (e i)).val, (col _ (live i)).1⟩
  have route (f : B (h + 1) → B (h + 1)) (u : Words M h → Fin (p.rows h))
      (hu : ∀ i, f (e i) = o (u i)) (hf : f = C.base ∨ f = C.base ∘ y) :
      ∃ v : Equiv.Perm (Words M h), (∀ i, t (v i) = (u i, c i)) ∧
        (∀ i, C.route f (C.label y) (e i) = e (v i)) ∧
        (∀ i, inv (C.route f (C.label y)) (e (v i)) = e i) := by
    let move i := t.symm (u i, c i)
    have inject : Function.Injective move := by
      intro i j he
      obtain ⟨hl, hr⟩ := Prod.mk.inj (t.symm.injective he)
      have ends : f (e i) = f (e j) := by rw [hu, hu, hl]
      apply e.injective
      apply (col _ (live i)).2 _ (live j) (Fin.ext (congrArg (fun z : Fin d => z.val) hr))
      rcases hf with rfl | rfl
      · exact .inl ends
      · exact .inr ends
    let v := Equiv.ofBijective move inject.bijective_of_finite
    have hv (i) : C.route f (C.label y) (e i) = e (v i) := by
      rw [Chart.route, ite_eq_left (live i), hu, loc _ _ (c i).isLt]
      rfl
    exact ⟨v, fun _ => t.apply_symm_apply _, hv,
      inverse_agrees e v _ hv (fun i h => ite_eq_right (mt (hmask i).mp h)) inv hi⟩
  obtain ⟨w, hw, hl, hil⟩ := route _ (fun i => (t i).1) base (.inl rfl)
  obtain ⟨v, hv, hr, hir⟩ := route _ (fun i => (t (g i)).1) target (.inr rfl)
  refine ⟨w, v, ?_, ?_, ?_, hl⟩
  · intro i
    change (t (w i)).1 = (t i).1 ∧ (t (v i)).1 = (t (g i)).1 ∧ (t (w i)).2 = (t (v i)).2
    simp only [hw, hv, and_self]
  · exact fun i => (congrArg y (hir i)).trans (hy i)
  · exact fun i => (congrArg (C.right y) (hil i)).trans (hr i)

include hi in
/-- The returned permutations realize the specified first- and second-coordinate
restrictions. The same explicit chart is used for every input at a given height. -/
theorem chart_exists (g : Equiv.Perm (Words M h))
    (hg : ∀ i, (p.apply h (g i)).1 = (p.apply h i).1)
    (y : (Perm (h + 1)).obj) (hy : ∀ i, y (embed hM h i) = embed hM h (g i)) :
    ∃ u v w : Equiv.Perm (Words M h), g = u * v * w ∧
      (∀ i, (p.apply h (u i)).1 = (p.apply h i).1 ∧ (p.apply h (u i)).2.1 = (p.apply h i).2.1) ∧
      (∀ i, (p.apply h (v i)).1 = (p.apply h i).1 ∧ (p.apply h (v i)).2.2 = (p.apply h i).2.2) ∧
      (∀ i, (p.apply h (w i)).1 = (p.apply h i).1 ∧ (p.apply h (w i)).2.1 = (p.apply h i).2.1) ∧
      (∀ i, ((chart hM p h).run inv y).1 (embed hM h i) = embed hM h (u i)) ∧
      (∀ i, ((chart hM p h).run inv y).2.1 (embed hM h i) = embed hM h (v i)) ∧
      (∀ i, ((chart hM p h).run inv y).2.2 (embed hM h i) = embed hM h (w i)) := by
  let s := p.apply h
  obtain ⟨w, z, hz, hu, hv, hw⟩ := product_routes hM p h inv hi g y hy
  have first (i) : (s (w i)).1 = (s i).1 ∧ (s (w i)).2.1 = (s i).2.1 :=
    Prod.mk.inj ((p.row h).injective (hz i).1)
  have last (i) : (s (g i)).1 = (s (z i)).1 ∧ (s (g i)).2.1 = (s (z i)).2.1 :=
    Prod.mk.inj ((p.row h).injective (hz i).2.1.symm)
  have middle (i) : (s (z i)).1 = (s (w i)).1 ∧ (s (z i)).2.2 = (s (w i)).2.2 :=
    ⟨(last i).1.symm.trans ((hg i).trans (first i).1.symm),
      (p.column h).injective (hz i).2.2.symm⟩
  refine ⟨g * z⁻¹, z * w⁻¹, w, by simp [mul_assoc], ?_, ?_, first, ?_, ?_, hw⟩
  · intro i
    simpa using last (z.symm i)
  · intro i
    simpa using middle (w.symm i)
  · intro i
    simpa using hu (z.symm i)
  · intro i
    simpa using hv (w.symm i)

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-!
# Packing rows into dyadic groups

Round each row length up to a power of two. The row slots consume
at most twice the size of the chart. Put the unused ambient sites
immediately after this reserved region.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.ProductChart
open Coloring

variable {M : ℕ} (p : ProductChart M) (h : ℕ)

def position (i : B (h + 1)) : ℕ :=
  if hi : i.val < count M h then
    let x := p.grid h ((number M h).symm ⟨i.val, hi⟩)
    x.1.val * 2 ^ (Nat.clog 2 (p.degree h)) + x.2.val
  else count M h + i.val

variable (hM : 1 < M)

theorem position_embed (x : Words M h) :
    p.position h (embed hM h x) =
      (p.grid h x).1.val * 2 ^ (Nat.clog 2 (p.degree h)) + (p.grid h x).2.val := by
  rw [position, dite_eq_left ((embed_range hM h _).mpr ⟨x, rfl⟩)]
  change (p.grid h ((number M h).symm (number M h x))).1.val * _ +
    (p.grid h ((number M h).symm (number M h x))).2.val = _
  rw [Equiv.symm_apply_apply]

private theorem rounded (n : ℕ) (hn : 0 < n) : 2 ^ (Nat.clog 2 n) ≤ n * 2 := by
  cases he : Nat.clog 2 n with
  | zero => simp; omega
  | succ k =>
    rw [pow_succ]
    exact Nat.mul_le_mul_right 2 (Nat.pow_lt_of_lt_clog (show k < Nat.clog 2 n by omega)).le

private theorem position_inside (x : Words M h) :
    p.position h (embed hM h x) < count M h * 2 := by
  let z := p.grid h x
  let t := Nat.clog 2 (p.degree h)
  have hz : z.2.val < 2 ^ t := z.2.isLt.trans_le (Nat.le_pow_clog (by decide) _)
  rw [position_embed]
  calc
    _ < (z.1.val + 1) * 2 ^ t := by rw [add_mul, one_mul]; exact Nat.add_lt_add_left hz _
    _ ≤ p.rows h * (p.degree h * 2) := Nat.mul_le_mul z.1.isLt (rounded _ (p.degree_pos h hM))
    _ = _ := by rw [← mul_assoc, p.area]

theorem position_row (x : Words M h) :
    p.position h (embed hM h x) / 2 ^ (Nat.clog 2 (p.degree h)) = (p.grid h x).1.val := by
  have hx := (p.grid h x).2.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)
  rw [position_embed, add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hx, zero_add]

include hM in
theorem position_lt (i : B (h + 1)) : p.position h i < 2 ^ (h + 2) := by
  have hn := (count_bounds hM h).2
  rw [show 2 ^ (h + 2) = 2 ^ (h + 1) * 2 from pow_succ _ _]
  by_cases hi : i.val < count M h
  · obtain ⟨x, rfl⟩ := (embed_range hM h i).mp hi
    exact (p.position_inside h hM x).trans_le (Nat.mul_le_mul_right _ hn.le)
  · rw [position, dite_eq_right hi]
    have := i.isLt
    omega

include hM in
theorem position_injective : Function.Injective (p.position h) := by
  intro i j he
  have test (v : B (h + 1)) : v.val < count M h ↔ p.position h v < count M h * 2 := by
    constructor
    · intro hv
      obtain ⟨x, rfl⟩ := (embed_range hM h v).mp hv
      exact p.position_inside h hM x
    · contrapose!
      intro hv
      rw [position, dite_eq_right (by omega)]
      omega
  have eq : i.val < count M h ↔ j.val < count M h := by rw [test, test, he]
  by_cases hi : i.val < count M h
  · obtain ⟨y, rfl⟩ := (embed_range hM h j).mp (eq.mp hi)
    obtain ⟨x, rfl⟩ := (embed_range hM h i).mp hi
    have hr : (p.grid h x).1 = (p.grid h y).1 := by
      apply Fin.ext
      rw [← p.position_row h hM, ← p.position_row h hM, he]
    rw [position_embed, position_embed, hr] at he
    have hc : (p.grid h x).2 = (p.grid h y).2 := Fin.ext (Nat.add_left_cancel he)
    rw [(p.grid h).injective (Prod.ext hr hc)]
  · rw [position, dite_eq_right hi, position, dite_eq_right (mt eq.mpr hi)] at he
    exact Fin.ext (Nat.add_left_cancel he)

def packing (b : ℕ) (hb : b ≤ h) : B (h + 1) ↪ B (h + 2 - b) × B b where
  toFun i := (⟨p.position h i / 2 ^ b, by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← pow_add, show h + 2 - b + b = h + 2 by omega]
    exact p.position_lt h hM i⟩, ⟨p.position h i % 2 ^ b, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
  inj' := by
    intro i j he
    apply p.position_injective h hM
    have e₁ := congrArg (fun z => z.1.val) he
    have e₂ := congrArg (fun z => z.2.val) he
    change p.position h i / 2 ^ b = p.position h j / 2 ^ b at e₁
    change p.position h i % 2 ^ b = p.position h j % 2 ^ b at e₂
    rw [← Nat.mod_add_div (p.position h i) (2 ^ b), e₁, e₂, Nat.mod_add_div]

theorem position_group (b : ℕ) (hb : p.degree h ≤ 2 ^ b) (x y : Words M h)
    (he : (p.grid h x).1 = (p.grid h y).1) :
    p.position h (embed hM h x) / 2 ^ b = p.position h (embed hM h y) / 2 ^ b := by
  let t := Nat.clog 2 (p.degree h)
  have ht : t ≤ b := Nat.clog_le_of_le_pow hb
  rw [show 2 ^ b = 2 ^ t * 2 ^ (b - t) by rw [← pow_add, Nat.add_sub_of_le ht],
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, position_row, position_row, he]

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.ProductChart
end

section
/-!
# Arithmetic programs for producing the literals of word programs

An expression is fixed independently of the height. Its inputs are
the height, a block exponent, the site number, and a loop index.
Products, integer quotient and remainder are unsigned word operations.
The only tables are finite literal arrays. A power and a sum each use
at most h+2 iterations.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
variable {M : ℕ}

inductive Register where
  | height | block | site | place
  | lit (n : ℕ)

def Register.eval (h b x i : ℕ) : Register → ℕ
  | .height => h
  | .block => b
  | .site => x
  | .place => i
  | .lit n => n

inductive Arith (M : ℕ) where
  | add | sub | mul | div | mod | lt
  | power (q : ℕ)
  | table {n : ℕ} (entries : Vector (Fin (M + 1)) n)

def Arith.eval (h x y : ℕ) : Arith M → ℕ
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .div => x / y
  | .mod => x % y
  | .lt => if x < y then 1 else 0
  | .power q => q ^ min (h + 2) x
  | .table (n := n) a => if hx : x < n then a[x].val else 0

inductive Index (M : ℕ)
  | arg (r : Register)
  | op (f : Arith M) (x y : Index M)
  | sum (n body : Index M)

namespace Index

def eval : Index M → ℕ → ℕ → ℕ → ℕ → ℕ
  | .arg r, h, b, x, i => r.eval h b x i
  | .op f u v, h, b, x, i => f.eval h (u.eval h b x i) (v.eval h b x i)
  | .sum n u, h, b, x, i =>
    ∑ j ∈ Finset.range (min (h + 2) (n.eval h b x i)), u.eval h b x j

/-- One pass computes a sum or power. The allowance includes a loop
counter, comparison, accumulator updates and both operand reads. -/
def cost (h : ℕ) : Index M → ℕ
  | .arg _ => 1
  | .op _ u v => 16 * (h + 3) + u.cost h + v.cost h
  | .sum n u => 16 * (h + 3) + n.cost h + (h + 2) * u.cost h

def size : Index M → ℕ
  | .arg _ => 1
  | .op _ u v | .sum u v => 16 + u.size + v.size

def degree : Index M → ℕ
  | .arg _ => 1
  | .op _ u v => max u.degree v.degree
  | .sum u v => max u.degree v.degree + 1

theorem degree_pos (e : Index M) : 0 < e.degree := by
  induction e <;> simp only [degree] <;> omega

theorem cost_le (e : Index M) (h : ℕ) : e.cost h ≤ e.size * (h + 3) ^ e.degree := by
  have grow {a b : ℕ} (hab : a ≤ b) : (h + 3) ^ a ≤ (h + 3) ^ b :=
    Nat.pow_le_pow_right (by omega) hab
  induction e with
  | arg r => simp [cost, size, degree]
  | op f u v hu hv =>
    let d := max u.degree v.degree
    have hd : h + 3 ≤ (h + 3) ^ d := by simpa using grow (show 1 ≤ d from u.degree_pos.trans_le (le_max_left ..))
    have hu' := hu.trans (Nat.mul_le_mul_left _ (grow (le_max_left u.degree v.degree)))
    have hv' := hv.trans (Nat.mul_le_mul_left _ (grow (le_max_right u.degree v.degree)))
    simp only [cost, size, degree, add_mul]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hd) hu') hv'
  | sum u v hu hv =>
    let d := max u.degree v.degree + 1
    have hd : h + 3 ≤ (h + 3) ^ d := by simpa using grow (show 1 ≤ d by unfold d; omega)
    have hu' := hu.trans (Nat.mul_le_mul_left _ (grow (show u.degree ≤ d by unfold d; omega)))
    have hv' : (h + 2) * v.cost h ≤ v.size * (h + 3) ^ d := calc
      _ ≤ (h + 3) * (v.size * (h + 3) ^ v.degree) := Nat.mul_le_mul (by omega) hv
      _ = v.size * (h + 3) ^ (v.degree + 1) := by rw [pow_succ]; ac_rfl
      _ ≤ _ := Nat.mul_le_mul_left _ (grow (by unfold d; omega))
    change 16 * (h + 3) + u.cost h + (h + 2) * v.cost h ≤ (16 + u.size + v.size) * (h + 3) ^ d
    rw [add_mul (16 + u.size), add_mul 16]
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hd) hu') hv'

end Index
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

section
/-! # Computing word lengths, spare labels and radix conversions -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
variable {M : ℕ}

def lit (n : ℕ) : Index M := .arg (.lit n)
def height : Index M := .arg .height
def block : Index M := .arg .block
def site : Index M := .arg .site
def place : Index M := .arg .place
def pow (a : ℕ) (n : Index M) := op (.power a) n (lit 0)
def cond (u v a b : Index M) :=
  let z := op .lt u v
  op .add (op .mul z a) (op .mul (op .sub (lit 1) z) b)

variable (h b x i : ℕ)

theorem eval_cond (u v a d : Index M) :
    (cond u v a d).eval h b x i =
      if u.eval h b x i < v.eval h b x i then a.eval h b x i else d.eval h b x i := by
  simp only [cond, lit, eval, Arith.eval, Register.eval]
  split <;> simp

def len (M : ℕ) : Index M :=
  sum height (cond (pow 2 height) (pow M (op .add place (lit 1))) (lit 0) (lit 1))

theorem len_le (hM : 1 < M) : length M h ≤ h := by
  have he := Nat.log_anti_left (n := 2 ^ h) (by decide : 1 < 2) hM
  simpa using he

private theorem count_indices (m n : ℕ) (hm : m ≤ n) :
    (∑ j ∈ Finset.range n, if j < m then 1 else 0) = m := by
  have he : (Finset.range n).filter (fun j => j < m) = Finset.range m := by ext; simp; omega
  rw [← Finset.sum_filter, he]
  simp

theorem eval_len (hM : 1 < M) : (len M).eval h b x i = length M h := by
  change (∑ j ∈ Finset.range (min (h + 2) h), _) = _
  rw [min_eq_right (by omega)]
  refine (Finset.sum_congr rfl (fun j hj => ?_)).trans (count_indices _ h (len_le h hM))
  have hj' := Finset.mem_range.mp hj
  rw [eval_cond]
  simp only [pow, lit, height, place, eval, Arith.eval, Register.eval,
    min_eq_right (show h ≤ h + 2 by omega), min_eq_right (show j + 1 ≤ h + 2 by omega)]
  have he : j < length M h ↔ M ^ (j + 1) ≤ 2 ^ h := Nat.le_log_iff_pow_le hM (Nat.two_pow_pos h).ne'
  simp only [he]
  split <;> split <;> omega

def radix (M a : ℕ) : Index M := pow a (len M)
def rest (M : ℕ) : Index M :=
  op .add (op .div (op .sub (pow 2 height) (lit 1)) (radix M M)) (lit 1)
def total (M : ℕ) : Index M := op .mul (radix M M) (rest M)
def ceil (a : Index M) := sum (op .add height (lit 1)) (op .lt (pow 2 place) a)

theorem eval_radix (hM : 1 < M) (a : ℕ) :
    (radix M a).eval h b x i = a ^ (length M h) := by
  have := len_le h hM
  simp only [radix, pow, eval, Arith.eval, eval_len _ _ _ _ hM, min_eq_right (show length M h ≤ h + 2 by omega)]

theorem eval_rest (hM : 1 < M) : (rest M).eval h b x i = spare M h := by
  simp only [rest, lit, height, pow, eval, Arith.eval, Register.eval, eval_radix _ _ _ _ hM,
    min_eq_right (show h ≤ h + 2 by omega)]

theorem eval_total (hM : 1 < M) : (total M).eval h b x i = count M h := by
  simp only [total, eval, Arith.eval, eval_radix _ _ _ _ hM, eval_rest _ _ _ _ hM]

theorem eval_ceil (a : Index M) (n : ℕ) (ha : ∀ i, a.eval h b x i = n) (hn : n ≤ 2 ^ (h + 1)) :
    (ceil a).eval h b x i = Nat.clog 2 n := by
  change (∑ j ∈ Finset.range (min (h + 2) (h + 1)), _) = _
  rw [min_eq_right (by omega)]
  refine (Finset.sum_congr rfl (fun j hj => ?_)).trans
    (count_indices _ (h + 1) (Nat.clog_le_of_le_pow hn))
  have hj' := Finset.mem_range.mp hj
  simp only [pow, place, eval, Arith.eval, Register.eval, ha, min_eq_right (show j ≤ h + 2 by omega),
    Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)]

/-- Encode by adding the digits times their radix powers. -/
def encode (a : ℕ) (u : Index M) := sum (len M) (op .mul u (pow a place))

/-- Read digit i from a word by quotient and remainder. -/
def decode (a : ℕ) (u : Index M) := op .mod (op .div u (pow a place)) (lit a)

theorem eval_encode (hM : 1 < M) {a : ℕ} (u : Index M) (f : Fin (length M h) → Fin a)
    (hu : ∀ j, u.eval h b x j.val = (f j).val) :
    (encode a u).eval h b x i = (finFunctionFinEquiv f).val := by
  have hr := len_le h hM
  simp only [encode, eval, eval_len _ _ _ _ hM, min_eq_right (show length M h ≤ h + 2 by omega),
    finFunctionFinEquiv_apply, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow, place, eval, Arith.eval, Register.eval, hu, min_eq_right (show j.val ≤ h + 2 by have := j.isLt; omega)]

theorem eval_decode (hM : 1 < M) {a : ℕ} (u : Index M) (y : Fin (a ^ (length M h)))
    (j : Fin (length M h)) (hu : u.eval h b x j.val = y.val) :
    (decode a u).eval h b x j.val = (finFunctionFinEquiv.symm y j).val := by
  have hr := len_le h hM
  have := j.isLt
  simp only [decode, pow, lit, place, eval, Arith.eval, Register.eval, hu,
    min_eq_right (show j.val ≤ h + 2 by omega)]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
end

section
/-! # Compiling static projections of a digit word into arithmetic -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
variable {M : ℕ}

def lookup {n q : ℕ} (f : Fin n → Fin q) (hq : q ≤ M + 1) (u : Index M) :=
  op (.table (Vector.ofFn fun j => (f j).castLE hq)) u (lit 0)

theorem eval_lookup {n q h b x i : ℕ} (f : Fin n → Fin q) (hq : q ≤ M + 1)
    (u : Index M) (j : Fin n) (hu : u.eval h b x i = j.val) :
    (lookup f hq u).eval h b x i = (f j).val := by
  simp only [lookup, eval, Arith.eval, hu, dite_eq_left j.isLt, Vector.getElem_ofFn, Fin.val_castLE]

def join (n u v : Index M) := op .add v (op .mul n u)

theorem eval_join {h b x i m n : ℕ} (q u v : Index M) (y : Fin m × Fin n)
    (hq : q.eval h b x i = n) (hu : u.eval h b x i = y.1.val) (hv : v.eval h b x i = y.2.val) :
    (join q u v).eval h b x i = (finProdFinEquiv y).val := by
  simp only [join, eval, Arith.eval, hq, hu, hv, finProdFinEquiv_apply_val]

def word (M : ℕ) : Index M := decode M (op .div site (rest M))
def tail (M : ℕ) : Index M := op .mod site (rest M)
def project (a : ℕ) (f : Fin M → Fin a) (ha : a ≤ M + 1) :=
  encode a (lookup f ha (word M))

variable (hM : 1 < M) (h b : ℕ) (x : Fin (count M h))

include hM in
theorem eval_word (i : Fin (length M h)) :
    (word M).eval h b x.val i.val = (((number M h).symm x).1 i).val := by
  apply eval_decode h b x.val hM _ (finProdFinEquiv.symm x).1
  simp only [site, eval, Arith.eval, Register.eval, eval_rest _ _ _ _ hM]
  rfl

include hM in
theorem eval_tail (i : ℕ) : (tail M).eval h b x.val i = ((number M h).symm x).2.val := by
  simp only [tail, site, eval, Arith.eval, Register.eval, eval_rest _ _ _ _ hM]
  rfl

include hM in
theorem eval_project (a : ℕ) (f : Fin M → Fin a) (ha : a ≤ M + 1) (i : ℕ) :
    (project a f ha).eval h b x.val i =
      (finFunctionFinEquiv (f ∘ ((number M h).symm x).1)).val := by
  apply eval_encode h b x.val i hM
  exact fun j => eval_lookup f ha _ _ (eval_word hM h b x j)

def packDigit (π : Equiv.Perm (Fin M)) :=
  cond site (total M) (join (rest M) (project M π (Nat.le_succ _)) (tail M)) site

theorem eval_packDigit (π : Equiv.Perm (Fin M)) (x : Coloring.B (h + 1)) (i : ℕ) :
    (packDigit π).eval h b x.val i = (Uniform.packDigit hM π h x).val := by
  rw [packDigit, eval_cond, eval_total _ _ _ _ hM, Uniform.packDigit]
  simp only [site, eval, Register.eval]
  split
  · rename_i hx
    let y : Fin (count M h) := ⟨x, hx⟩
    exact eval_join _ _ _ (finFunctionFinEquiv (π ∘ ((number M h).symm y).1), ((number M h).symm y).2)
      (eval_rest _ _ _ _ hM) (eval_project hM h b y _ π _ i) (eval_tail hM h b y i)
  · rfl

variable (p : ProductChart M)

def columns := op .mul (radix M p.b.val) (rest M)
def rows := op .mul (radix M p.c.val) (radix M p.a.val)

include hM in
theorem eval_columns (x i : ℕ) : (columns p).eval h b x i = p.degree h := by
  simp only [columns, eval, Arith.eval, eval_radix _ _ _ _ hM, eval_rest _ _ _ _ hM]

include hM in
theorem eval_rows (x i : ℕ) : (rows p).eval h b x i = p.rows h := by
  simp only [rows, eval, Arith.eval, eval_radix _ _ _ _ hM]

def row := join (radix M p.a.val)
  (project _ (fun y => (p.split y).1) p.c.isLt.le)
  (project _ (fun y => (p.split y).2.1) p.a.isLt.le)
def col := join (rest M) (project _ (fun y => (p.split y).2.2) p.b.isLt.le) (tail M)

include hM in
theorem eval_row (i : ℕ) :
    (row p).eval h b x.val i = (p.grid h ((number M h).symm x)).1.val := by
  let y := p.apply h ((number M h).symm x)
  exact eval_join _ _ _ (finFunctionFinEquiv y.1, finFunctionFinEquiv y.2.1)
    (eval_radix _ _ _ _ hM _) (eval_project hM h b x _ _ _ i) (eval_project hM h b x _ _ _ i)

include hM in
theorem eval_col (i : ℕ) :
    (col p).eval h b x.val i = (p.grid h ((number M h).symm x)).2.val := by
  let y := p.apply h ((number M h).symm x)
  exact eval_join _ _ _ (finFunctionFinEquiv y.2.2.1, y.2.2.2)
    (eval_rest _ _ _ _ hM) (eval_project hM h b x _ _ _ i) (eval_tail hM h b x i)

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
end

section
/-! # Arithmetic programs for both directions of chart addressing -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
open Coloring (B)
variable {M : ℕ} (p : ProductChart M)

private def code : Fin p.c.val × Fin p.a.val × Fin p.b.val ≃ Fin (p.c.val * (p.a.val * p.b.val)) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

private def getRow := op .div site (columns p)
private def getCol := op .mod site (columns p)
private def getC := decode p.c.val (op .div (getRow p) (radix M p.a.val))
private def getA := decode p.a.val (op .mod (getRow p) (radix M p.a.val))
private def getB := decode p.b.val (op .div (getCol p) (rest M))
private def restore := lookup ((code p).symm.trans p.split.symm) (Nat.le_succ _)
  (join (lit (p.a.val * p.b.val)) (getC p) (join (lit p.b.val) (getA p) (getB p)))

def location := cond site (total M)
  (join (rest M) (encode M (restore p)) (op .mod (getCol p) (rest M))) site

variable (hM : 1 < M) (h b : ℕ)

include hM in
private theorem eval_restore (x : Fin (p.rows h * p.degree h)) (j : Fin (length M h)) :
    (restore p).eval h b x.val j.val =
      (((p.grid h).symm (finProdFinEquiv.symm x)).1 j).val := by
  let a := finProdFinEquiv.symm (finProdFinEquiv.symm x).1
  let d := finProdFinEquiv.symm (finProdFinEquiv.symm x).2
  let z := (finFunctionFinEquiv.symm a.1 j, finFunctionFinEquiv.symm a.2 j,
    finFunctionFinEquiv.symm d.1 j)
  have hc : (getC p).eval h b x.val j.val = z.1.val := by
    refine eval_decode h b x.val hM _ a.1 j ?_
    simp only [getRow, site, eval, Register.eval, Arith.eval, eval_columns hM, eval_radix _ _ _ _ hM]
    rfl
  have ha : (getA p).eval h b x.val j.val = z.2.1.val := by
    refine eval_decode h b x.val hM _ a.2 j ?_
    simp only [getRow, site, eval, Register.eval, Arith.eval, eval_columns hM, eval_radix _ _ _ _ hM]
    rfl
  have hd : (getB p).eval h b x.val j.val = z.2.2.val := by
    refine eval_decode h b x.val hM _ d.1 j ?_
    simp only [getCol, site, eval, Register.eval, Arith.eval, eval_columns hM, eval_rest _ _ _ _ hM]
    rfl
  have he : (restore p).eval h b x.val j.val = (p.split.symm ((code p).symm (code p z))).val :=
    eval_lookup _ _ _ (code p z) (eval_join _ _ _ (z.1, finProdFinEquiv z.2) rfl hc
      (eval_join _ _ _ z.2 rfl ha hd))
  rw [he, Equiv.symm_apply_apply]
  rfl

theorem eval_location (x : B (h + 1)) (i : ℕ) :
    (location p).eval h b x.val i = ((chart hM p h).location x).val := by
  rw [location, eval_cond, eval_total _ _ _ _ hM, ← p.area h]
  simp only [site, eval, Register.eval, chart]
  split
  · rename_i hx
    let y : Fin (p.rows h * p.degree h) := ⟨x, hx⟩
    let z := (p.grid h).symm (finProdFinEquiv.symm y)
    refine eval_join _ _ _ (finFunctionFinEquiv z.1, z.2) (eval_rest _ _ _ _ hM)
      (eval_encode _ _ _ _ hM _ _ (eval_restore p hM h b y)) ?_
    simp only [getCol, site, eval, Register.eval, Arith.eval, eval_columns hM, eval_rest _ _ _ _ hM]
    rfl
  · rfl

def base (p : ProductChart M) := cond site (total M) (op .mul (columns p) (row p)) site
def assign (p : ProductChart M) := cond site (rows p) (op .mul (columns p) site) (lit 0)
def mask (M : ℕ) := op .lt site (total M)

theorem eval_base (x : B (h + 1)) (i : ℕ) :
    (base p).eval h b x.val i = ((chart hM p h).base x).val := by
  rw [base, eval_cond, eval_total _ _ _ _ hM]
  simp only [site, eval, Register.eval, Arith.eval, eval_columns hM, chart]
  split
  · rename_i hx
    let y : Fin (count M h) := ⟨x, hx⟩
    change _ = 0 + p.degree h * (p.grid h ((number M h).symm y)).1.val
    rw [zero_add]
    exact congrArg (p.degree h * ·) (eval_row hM h b y p i)
  · rfl

theorem eval_assign (x i : ℕ) :
    (assign p).eval h b x i = ((reservation hM p h).assign x).val := by
  rw [assign, eval_cond, eval_rows hM]
  simp only [site, lit, eval, Register.eval, Arith.eval, eval_columns hM, reservation]
  split
  · change _ = 0 + p.degree h * x
    rw [zero_add]
  · rfl

theorem eval_mask (x : B (h + 1)) (i : ℕ) :
    (mask M).eval h b x.val i = if (chart hM p h).mask x then 1 else 0 := by
  simp only [mask, site, eval, Arith.eval, Register.eval, eval_total _ _ _ _ hM, chart, decide_eq_true_eq]

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
end

section
/-!
# Finite descriptions of permutation procedures at every height

The only parameters of a leaf or a factor operation are functions
between fixed finite digit alphabets. The same expression specifies
the padding, product decomposition and permutation at every height.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring (B)

abbrev ArrayOf (h : ℕ) := B h → B h
def invert {h : ℕ} (g : ArrayOf h) : ArrayOf h := ⇑(Coloring.permutation g (fun _ => true))

theorem invert_perm {h : ℕ} (g : Equiv.Perm (B h)) : invert g = ⇑g.symm := by
  let key (i : B h) := toLex (false, toLex (g i, i))
  have hs : StrictMono (key ∘ g.symm) := by
    intro i j hij
    simp only [Function.comp_apply, key, Equiv.apply_symm_apply, Prod.Lex.toLex_lt_toLex]
    exact .inr ⟨trivial, .inl hij⟩
  have he : g.symm = Tuple.sort key :=
    Tuple.eq_sort_iff.mpr ⟨hs.monotone, fun _ _ hij he => ((hs hij).ne he).elim⟩
  rw [he]
  rfl

inductive Recipe (M : ℕ)
  | id
  | target
  | digit (p : Equiv.Perm (Fin M))
  | inv (r : Recipe M)
  | mul (r s : Recipe M)
  | factor (p : ProductChart M) (j : Fin 3) (r : Recipe M)

namespace Recipe
variable {M : ℕ}

def pick {α : Type} (j : Fin 3) (p : α × α × α) :=
  if j = 0 then p.1 else if j = 1 then p.2.1 else p.2.2

def clean (M h : ℕ) (x : ArrayOf (h + 1)) (i : B (h + 1)) := if i.val < count M h then x i else i

def eval (hM : 1 < M) : Recipe M → (h : ℕ) → ArrayOf (h + 1) → ArrayOf (h + 1)
  | .id, _, _ => _root_.id
  | .target, _, x => x
  | .digit p, h, _ => packDigit hM p h
  | .inv r, h, x => invert (r.eval hM h x)
  | .mul r s, h, x => r.eval hM h x ∘ s.eval hM h x
  | .factor p j r, h, x => clean M h (pick j ((chart hM p h).run invert (r.eval hM h x)))

end Recipe
end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end
