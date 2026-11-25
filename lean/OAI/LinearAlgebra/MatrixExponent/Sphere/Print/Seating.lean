import OAI.LinearAlgebra.MatrixExponent.Sphere.Coupled
import OAI.LinearAlgebra.MatrixExponent.Spectral.Span
import Mathlib.Data.Fin.Tuple.Basic
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.Prices.WireRecovery
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam

/-!
# Products with one shared rational parameter

Principal parts and constant terms suffice to reconstruct the whole
product. The convolution uses only nonpositive total Laurent orders,
even though an individual factor may contribute a regular term.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial Finset
open scoped Classical
variable {K ι D : Type*} [Field K]

private theorem regular_prod (s : Finset ι) (z : K) (a b : ι → K[X])
    (hb : ∀ i ∈ s, (b i).eval z ≠ 0) :
    regular z (∏ i ∈ s, a i) (∏ i ∈ s, b i) = ∏ i ∈ s, regular z (a i) (b i) := by
  have ht (f : ι → K[X]) : (taylor z (∏ i ∈ s, f i) : PowerSeries K) =
      ∏ i ∈ s, (taylor z (f i) : PowerSeries K) := by
    clear hb
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp only [prod_insert hi, taylor_mul, Polynomial.coe_mul, ih]
  have he : (∏ i ∈ s, b i).eval z ≠ 0 := by rw [eval_prod]; exact prod_ne_zero_iff.mpr hb
  have hn : (taylor z (∏ i ∈ s, b i) : PowerSeries K) ≠ 0 := by
    intro h
    apply he
    simpa only [constantCoeff_coe, taylor_coeff_zero, map_zero] using congrArg PowerSeries.constantCoeff h
  apply mul_right_cancel₀ hn
  rw [regular_mul _ _ _ he, ht, ht, ← prod_mul_distrib]
  exact prod_congr rfl fun i hi => (regular_mul _ _ _ (hb i hi)).symm

variable [Fintype ι]

private theorem prod_poles (s : Finset K) (d : ι → ℕ) :
    ∏ i, poles s (fun _ => d i) = poles s (fun _ => ∑ i, d i) := by
  unfold poles
  rw [prod_comm]
  simp only [prod_pow_eq_pow_sum]

/-- An entrywise statement for a subspace of tables. The summation
indices in the hypothesis are Laurent orders shifted by the pole bounds. -/
theorem product_mem (W : Submodule K (D → K)) (s : Finset K) (hs : s.Nonempty)
    (a : ι → D → K[X]) (d : ι → ℕ) (hd : ∀ i y, (a i y).natDegree ≤ s.card * d i)
    (h : ∀ z ∈ s, ∀ u : ι → ℕ, (∑ i, u i) ≤ ∑ i, d i →
      (fun y => ∏ i, jet z (poles (s.erase z) (fun _ => d i)) (u i) (a i y)) ∈ W) (x : K) :
    (fun y => ∏ i, (a i y).eval x / (poles s (fun _ => d i)).eval x) ∈ W := by
  let H := ∑ i, d i
  let q := poles s (fun _ => H)
  let u (z : K) := poles (s.erase z) (fun _ => H)
  let P (y : D) := ∏ i, a i y
  have deg (y : D) : (P y).natDegree ≤ s.card * H := calc
    _ ≤ ∑ i, (a i y).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ i, s.card * d i := sum_le_sum fun i _ => hd i y
    _ = _ := (mul_sum _ _ _).symm
  have size : s.card * H < ∑ _ ∈ s, (H + 1) := by
    simpa using Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self H) hs.card_pos
  obtain ⟨c, hc⟩ := reconstruct_jets s (fun _ => H + 1) u (fun z _ => poles_eval _ (notMem_erase z s))
    _ size (jet x q 0)
  have he : (fun y => ∏ i, (a i y).eval x / (poles s (fun _ => d i)).eval x) =
      ∑ v, c v • (fun y => jet v.1.val (u v.1.val) v.2.val (P y)) := by
    funext y
    rw [prod_div_distrib, ← eval_prod, ← eval_prod, prod_poles, ← jet_zero, hc _ (deg y)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  refine W.sum_mem (fun v _ => W.smul_mem _ ?_)
  let z := v.1.val
  let n := v.2.val
  have eqn : (fun y => jet z (u z) n (P y)) =
      ∑ l ∈ finsuppAntidiag univ n,
        (fun y => ∏ i, jet z (poles (s.erase z) (fun _ => d i)) (l i) (a i y)) := by
    funext y
    rw [Finset.sum_apply]
    change PowerSeries.coeff n (regular z _ _) = _
    unfold u H P
    rw [← prod_poles, regular_prod _ _ _ _ (fun i _ => poles_eval _ (notMem_erase z s)),
      PowerSeries.coeff_prod]
    rfl
  rw [eqn]
  exact W.sum_mem fun l hl => h z v.1.property l (by
    rw [(mem_finsuppAntidiag.mp hl).1]; exact Nat.lt_succ_iff.mp v.2.isLt)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-! # Products of arrays and bounds after closing an auxiliary leg -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S : Type} [Field K] [Fintype S] [Nonempty S] {n : ℕ}

theorem product_tables (X : Fin n → S → Type) [∀ i s, Fintype (X i s)]
    (V : ∀ i, (∀ s, X i s) → K) :
    (∏ i, ofRaw (Raw.ofTable (X i) (V i))) = ofRaw (Raw.ofTable (fun s => ∀ i, X i s)
      (fun x => ∏ i, V i (fun s => x s i))) := by
  classical
  induction n with
  | zero =>
    rw [Finset.prod_of_isEmpty]
    apply ofRaw_eq
    refine Raw.equiv_coeff (fun s => Equiv.ofUnique Unit (∀ i, X i s)) fun x => ?_
    erw [Raw.coeff_ofTable]
    change (∑ _ : Unit, ∏ _ : S, (1 : K)) = _
    simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, ih (fun i => X i.succ), ← ofRaw_mul]
    apply ofRaw_eq
    refine Raw.equiv_coeff (fun s => Fin.consEquiv (fun i => X i s)) fun x => ?_
    rw [Raw.coeff_mul]
    erw [Raw.coeff_ofTable, Raw.coeff_ofTable, Raw.coeff_ofTable]
    change (∀ s, X 0 s × (∀ i : Fin n, X i.succ s)) at x
    change _ = ∏ i, V i (fun s => Fin.cons (α := fun k => X k s) (x s).1 (x s).2 i)
    simp only [Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]

variable {I : Type} [Fintype I]

theorem product_span_le (X : Fin n → S → Type) [∀ i s, Fintype (X i s)]
    (V : ∀ i, (∀ s, X i s) → K) (L : I → ∀ i, (∀ s, X i s) → K)
    (c : I → K) (h : ∀ x : ∀ i s, X i s, (∏ i, V i (x i)) = ∑ j, c j * ∏ i, L j i (x i)) :
    ∏ i, ofRaw (Raw.ofTable (X i) (V i)) ≤ ∑ j, ∏ i, ofRaw (Raw.ofTable (X i) (L j i)) := by
  simp_rw [product_tables]
  exact span_le _ _ _ c (fun x => h (fun i s => x s i))

variable [DecidableEq S]

/-- The auxiliary site can be placed at a different old site in each
summand without increasing the cost of any closed restriction. -/
theorem padded_sum_le (P : I → Tensor K (S ⊕ Unit)) (loc : I → S) (T : Tensor K S)
    (h : pad Unit T ≤ ∑ j, P j) :
    T ≤ ∑ j, place (Sum.elim id (fun _ => loc j)) (P j) := by
  classical
  suffices ∀ s : Finset I, ∀ T : Tensor K S, pad Unit T ≤ ∑ j ∈ s, P j →
      T ≤ ∑ j ∈ s, place (Sum.elim id (fun _ => loc j)) (P j) from this _ _ h
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro U hU
    rw [Finset.sum_empty, ← (padding Unit).zero] at hU
    rw [Finset.sum_empty]
    exact ((padding Unit).le_iff _ _).mp hU
  | insert j s hj ih =>
    intro U hU
    rw [Finset.sum_insert hj] at hU ⊢
    obtain ⟨A, B, hA, hB, hAB⟩ := (padding Unit).split hU

    let g : S ⊕ Unit → S := Sum.elim id (fun _ => loc j)
    have ht := place_mono g hA
    rw [← place_inl, ← place_comp, show g ∘ Sum.inl = id from rfl, place_id] at ht
    refine hAB.trans ((add_le_add_right A _ B ht).trans ?_)
    have h := add_le_add_right _ _ (place g (P j)) (ih B hB)
    rw [add_comm B, add_comm _ (place g (P j))] at h
    exact h

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Printing one station from its intrinsic star

Each internal bundle has a short name shared by its two ends. Split
it into equal units, preserving the order of the bits. Two additional
spans contain all exterior bits, one per side of the station.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Coloring Classical Assembly

abbrev Band (A : Type) (c : ℕ) := Bool × Option (A × Fin c)

structure Star (F A : Type) (d : ℕ) where
  ext : Bool → ℕ
  link : Bool → A → Option (B d × ℕ)
  value : List Bool → List Bool → (Bool → A → List Bool) → F

variable {F A : Type} {d c e : ℕ}

namespace Star
variable (S : Star F A d) (ix : Band A c ↪ B e) (u : ℕ)

abbrev Port (d e : ℕ) := ℕ × Bool × Option (B d × B 0 × B e)

def spec (s : Band A c) : Port d e :=
  match s with
  | (b, none) => (S.ext b, b, none)
  | (b, some (i, j)) => match S.link b i with
    | some (q, n) => if j.val < n / u then (u, b, some (q, 0, ix (!b, some (i, j)))) else (0, b, none)
    | none => (0, b, none)

def desc : B e → Port d e := Function.extend ix (S.spec ix u) (fun _ => (0, false, none))

theorem desc_band (s : Band A c) : S.desc ix u (ix s) = S.spec ix u s :=
  ix.injective.extend_apply _ _ _

theorem desc_ext (b : Bool) : S.desc ix u (ix (b, none)) = (S.ext b, b, none) := S.desc_band ix u _

theorem desc_link {b : Bool} {i : A} {q : B d} {n : ℕ}
    (h : S.link b i = some (q, n)) (j : Fin c) (hj : j.val < n / u) :
    S.desc ix u (ix (b, some (i, j))) = (u, b, some (q, 0, ix (!b, some (i, j)))) := by
  rw [desc_band]; simp only [spec, h, ite_eq_left hj]

def body (f : B e → ℕ → Bool) (b : Bool) (l : A) : List Bool :=
  match S.link b l with
  | none => []
  | some (_, n) => List.ofFn fun i : Fin n =>
    if h : i.val / u < c then f (ix (b, some (l, ⟨i.val / u, h⟩))) (i.val % u) else false

def output (f : B e → ℕ → Bool) : F :=
  let ext b := List.ofFn fun i : Fin (S.ext b) => f (ix (b, none)) i
  S.value (ext false) (ext true) (S.body ix u f)

def pattern : Pattern F d 0 e where
  width _ s := (S.desc ix u s).1
  direction _ s := (S.desc ix u s).2.1
  peer _ s := (S.desc ix u s).2.2
  value _ t := S.output ix u (fun j k => if h : k < (S.desc ix u j).1 then t j ⟨k, h⟩ else false)

def vacant [One F] : Pattern F d 0 e :=
  {width := fun _ _ => 0, direction := fun _ _ => false, peer := fun _ _ => none, value := fun _ _ => 1}

theorem active {i : B e} (h : 0 < (S.desc ix u i).1 ∨ (S.desc ix u i).2.2 ≠ none) :
    (∃ b, i = ix (b, none)) ∨
      ∃ b l j q n, i = ix (b, some (l, j)) ∧ S.link b l = some (q, n) ∧ j.val < n / u := by
  by_cases hi : ∃ s, ix s = i
  swap
  · simp [desc, Function.extend, hi] at h
  obtain ⟨⟨b, _ | ⟨l, j⟩⟩, rfl⟩ := hi
  · exact .inl ⟨b, rfl⟩
  · right
    rw [desc_band] at h
    cases hn : S.link b l with
    | none => simp [spec, hn] at h
    | some p =>
      refine ⟨b, l, j, p.1, p.2, rfl, hn, ?_⟩
      by_contra hg
      simp [spec, hn, hg] at h

end Star
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! Construct a seating by assigning addresses to global wire ends. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Assembly Classical

variable {F : Type} [Field F] {a b : Wire}
  (S : Scheme F) (r : S.format.obj) (G : Diagram F a b)

structure Seating where
  vertex : G.V ↪ S.Vtx
  ends : G.End ≃ S.Pin r
  station : ∀ p, (ends p).1.1 = vertex (G.station p)
  value : ∀ (t : S.Pin r → Bool) (v : G.V),
    S.table r (vertex v) (t ∘ S.port r (vertex v)) =
      G.weight v (t ∘ ends ∘ .inl) (t ∘ ends ∘ .inr)
  empty : ∀ v ∉ Set.range vertex, ∀ t, S.table r v t = 1

namespace Seating
variable {S r G} (H : Seating S r G) (v : G.V)

omit [Field F] in
private theorem port_injective (u : S.Vtx) : Function.Injective (S.port r u) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ h
  have hs : s = t := congrArg (fun p => p.1.2) h
  subst t
  have : i = j := Fin.ext (congrArg (fun p => p.2.val) h)
  rw [this]

private def localSlots : S.LocalPin r (H.vertex v) ≃ {i : S.Pin r // i.1.1 = H.vertex v} :=
  Equiv.ofBijective (fun i => ⟨S.port r (H.vertex v) i, rfl⟩)
    ⟨fun _ _ h => port_injective _ (congrArg Subtype.val h), by
      rintro ⟨⟨⟨u, j⟩, l⟩, he⟩
      change u = H.vertex v at he
      subst u
      exact ⟨⟨j, l⟩, rfl⟩⟩

def pin : G.Port v ≃ S.LocalPin r (H.vertex v) :=
  (G.incident v).trans <| (H.ends.subtypeEquiv (fun _ => by
    rw [H.station, H.vertex.injective.eq_iff])).trans (H.localSlots v).symm

theorem pin_eq (i : G.Port v) :
    S.port r (H.vertex v) (H.pin v i) = H.ends (G.portEquiv ⟨v, i⟩) :=
  congrArg Subtype.val ((H.localSlots v).apply_symm_apply _)

def seat : S.Seating r G where
  vertex := H.vertex
  pin := H.pin
  cover j := by
    obtain ⟨t, rfl⟩ := H.ends.surjective j
    exact ⟨_, (H.station t).symm⟩
  vacant := H.empty
  sample v t := by
    let f := Function.extend (S.port r (H.vertex v)) t (fun _ => false)
    have hf : f ∘ S.port r (H.vertex v) = t :=
      funext fun i => (port_injective (S := S) (r := r) (H.vertex v)).extend_apply t (fun _ => false) i
    have h := H.value f v
    rw [hf] at h
    rw [h]
    change Transcript.sample (G.table v) (fun i => f (H.ends (G.portEquiv ⟨v, i⟩))) = _
    congr 1
    funext i
    rw [← H.pin_eq]
    exact congrFun hf _

theorem ends_eq : H.seat.ends = H.ends := by
  apply Equiv.ext
  intro t
  obtain ⟨⟨v, i⟩, rfl⟩ := G.portEquiv.surjective t
  exact (H.seat.ends_at v i).trans (H.pin_eq v i)

end Seating
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # Terms in the shared-parameter expansion of a product -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Added

open Sphere

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A] {n : ℕ}

/-- A pole and a list of output energies. Only nonpositive total
Laurent orders are needed. -/
abbrev Choice (e : Fin n → A ⊕ Unit → ℕ) (M : ℕ) :=
  {v : A × (Fin n → Fin (2 * n * M + 1)) //
    (∑ j, (v.2 j).val) ≤ ∑ j, (e j (.inl v.1) + e j (.inr ()))}

/-- Contract the two incident inputs with a fusion map and place its
output at the pole. -/
def term (z : A → F) (e : A ⊕ Unit → ℕ) (i : A) (g : ℕ) (x : States 1 e) : F :=
  ∑ y : Level 1 g, fusion F (x (.inl i)).val.val (x (.inr ())).val.val y.val.val *
    sphereForm z (Function.update (fun j => e (.inl j)) i g)
      (Insertion.changeAt i (fun j => x (.inl j)) y)

end OAI.LinearAlgebra.MatrixExponent.Routing.Added
end

/-!
# Counting nonpositive-order choices

Weight each output energy geometrically. On the budgeted lists the
product weight is at least one half per factor, while summing over all
energies costs only a linear factor in the average energy budget.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Added

open Finset

variable {A : Type} [Fintype A] {n : ℕ}

private theorem count (q H : ℕ) (ok : A × (Fin n → Fin q) → Prop) [DecidablePred ok]
    (budget : ∀ x, ok x → (∑ j, (x.2 j).val) ≤ H * n) :
    (Fintype.card {x // ok x} : ℝ) ≤ Fintype.card A * (4 * ((H : ℝ) + 1)) ^ n := by
  classical
  let b := 2 * ((H : ℝ) + 1)
  have hb : 2 ≤ b := by dsimp [b]; linarith
  have hb' : 0 < b := by linarith
  let r := 1 - b⁻¹
  have h_inv : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hr : 0 ≤ r := sub_nonneg.mpr h_inv
  have hr' : r ≤ 1 := sub_le_self _ (inv_nonneg.mpr hb'.le)
  have small : (1 / 2 : ℝ) ≤ r ^ H := by
    have e := one_add_mul_le_pow (by linarith : -2 ≤ -b⁻¹) H
    have hdiv : (H : ℝ) / b ≤ 1 / 2 := (div_le_iff₀ hb').mpr (by dsimp [b]; linarith)
    rw [div_eq_mul_inv] at hdiv
    change _ ≤ (1 + -b⁻¹) ^ H
    linarith
  have series : (∑ j : Fin q, r ^ j.val) ≤ b := by
    rw [Fin.sum_univ_eq_sum_range]
    have e := geom_sum_mul_neg r q
    have h : 1 - r = b⁻¹ := by unfold r; ring
    rw [h, ← div_eq_mul_inv] at e
    exact (div_le_one hb').mp (by rw [e]; exact sub_le_self _ (pow_nonneg hr _))
  let w (x : A × (Fin n → Fin q)) := r ^ (∑ j, (x.2 j).val)
  have low (x) (hx : ok x) : (1 / 2 : ℝ) ^ n ≤ w x := calc
    _ ≤ (r ^ H) ^ n := pow_le_pow_left₀ (by norm_num) small _
    _ ≤ w x := by rw [← pow_mul]; exact pow_le_pow_of_le_one hr hr' (budget x hx)
  have high : (∑ x, w x) ≤ (Fintype.card A : ℝ) * b ^ n := by
    simp only [Fintype.sum_prod_type, w, ← prod_pow_eq_pow_sum]
    rw [← Fintype.prod_sum (fun (_ : Fin n) (i : Fin q) => r ^ i.val)]
    simp only [sum_const, prod_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sum_nonneg fun _ _ => pow_nonneg hr _) series _) (Nat.cast_nonneg _)
  let S := univ.filter ok
  have h : (Fintype.card {x // ok x} : ℝ) * (1 / 2 : ℝ) ^ n ≤ (Fintype.card A : ℝ) * b ^ n := calc
    _ = ∑ _ ∈ S, (1 / 2 : ℝ) ^ n := by simp [S, Fintype.card_subtype]
    _ ≤ ∑ x ∈ S, w x := sum_le_sum fun x hx => low x (mem_filter.mp hx).2
    _ ≤ ∑ x, w x := sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => pow_nonneg hr _
    _ ≤ _ := high
  calc
    _ ≤ ((Fintype.card A : ℝ) * b ^ n) / (1 / 2 : ℝ) ^ n := (le_div_iff₀ (by positivity)).mpr h
    _ = _ := by rw [mul_div_assoc, ← div_pow]; congr 2; unfold b; ring

theorem card_choice (e : Fin n → A ⊕ Unit → ℕ) (M : ℕ) (hn : 0 < n) (he : ∀ j i, e j i ≤ M) :
    (Fintype.card (Choice e M) : ℝ) ≤ (((M : ℝ) + 2) ^ (Fintype.card A + 8)) ^ n := by
  have h : (Fintype.card (Choice e M) : ℝ) ≤ Fintype.card A * (4 * ((2 * M : ℕ) + 1 : ℝ)) ^ n := by
    apply count
    intro x hx
    apply hx.trans
    calc
      _ ≤ ∑ _ : Fin n, 2 * M := sum_le_sum fun j _ => by
        have h₁ := he j (.inl x.1)
        have h₂ := he j (.inr ())
        omega
      _ = _ := by simp [mul_comm]
  let t := (M : ℝ) + 2
  have ht : 2 ≤ t := by unfold t; linarith
  have ht' : 1 ≤ t := by linarith
  have h₁ : (Fintype.card A : ℝ) ≤ t ^ Fintype.card A :=
    le_trans (by exact_mod_cast (Nat.lt_two_pow_self (n := Fintype.card A)).le)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) ht _)
  have h₂ : 4 * ((2 * M : ℕ) + 1 : ℝ) ≤ t ^ 8 := calc
    _ ≤ t * 2 ^ 7 := by dsimp [t]; push_cast; linarith
    _ ≤ t * t ^ 7 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) ht _) (by linarith)
    _ = _ := by ring
  rw [pow_add, mul_pow]
  refine h.trans (mul_le_mul ?_ (pow_le_pow_left₀ (by positivity) h₂ _) (by positivity) (by positivity))
  exact h₁.trans (le_self_pow₀ (one_le_pow₀ ht') hn.ne')

variable [DecidableEq A] {e : Fin n → A ⊕ Unit → ℕ} {M : ℕ}

def reassigned (v : Choice e M) (j : Fin n) : A → ℕ :=
  Function.update (fun i => e j (.inl i)) v.val.1 (v.val.2 j).val

/-- A common collision site allows the energy of one factor to pay for
another, even with different penalties at the different sites. -/
theorem penalty (B : ℝ) (t : A ⊕ Unit → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ t (.inr ())) (v : Choice e M) :
    (∑ j, (B + ∑ i, t (.inl i) * (reassigned v j i : ℝ))) ≤
      ∑ j, (B + ∑ i, t i * (e j i : ℝ)) := by
  let a := v.val.1
  let rest j := B + ∑ i ∈ univ.erase a, t (.inl i) * (e j (.inl i) : ℝ)
  have left (j : Fin n) : B + ∑ i, t (.inl i) * (reassigned v j i : ℝ) =
      rest j + t (.inl a) * (v.val.2 j).val := by
    rw [← sum_erase_add _ _ (mem_univ a), ← add_assoc]
    have h : reassigned v j a = (v.val.2 j).val := Function.update_self _ _ _
    rw [h]
    congr 2
    apply sum_congr rfl
    intro i hi
    rw [reassigned, Function.update_of_ne (mem_erase.mp hi).1]
  have right (j : Fin n) :
      rest j + t (.inl a) * ((e j (.inl a) + e j (.inr ()) : ℕ) : ℝ) ≤
        B + ∑ i, t i * (e j i : ℝ) := by
    rw [Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit), ← sum_erase_add _ _ (mem_univ a)]
    unfold rest
    have h := mul_le_mul_of_nonneg_right (ht (.inl a)).2 (Nat.cast_nonneg (α := ℝ) (e j (.inr ())))
    push_cast
    linarith
  simp_rw [left]
  refine le_trans ?_ (sum_le_sum (fun j _ => right j))
  simp only [sum_add_distrib, ← mul_sum, ← Nat.cast_sum]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by simpa only [sum_add_distrib] using v.property)) (ht _).1)

end OAI.LinearAlgebra.MatrixExponent.Routing.Added
end

/-! # Locating a fusion map at the site of the collision -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Added

open Finset Sphere Spectral

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

/-- A sum ranging over one site's internal states is a local restriction
when the other sites' input coordinates are independent of that state. -/
private theorem local_sum {I : Type} [Fintype I] (U V : Raw F A) (i : A)
    (c : V.leg i → I → F) (f : ∀ j, V.leg j → I → U.leg j)
    (hi : ∀ j ≠ i, ∀ x a b, f j x a = f j x b)
    (he : ∀ x, V.coeff x = ∑ a, c (x i) a * U.coeff (fun j => f j (x j) a)) :
    U.Restricts V := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    exact (Raw.Restricts.zero U).trans ((Raw.zero_restricts_iff _).mpr (by simp [he]))
  | inr h =>
    let b := Classical.arbitrary I
    let L (j : A) : V.leg j → U.leg j → F :=
      Function.update (fun j x y => if y = f j x b then (1 : F) else 0) i
        (fun x y => ∑ a, if y = f i x a then c x a else 0) j
    refine ⟨L, fun x => ?_⟩
    have cent (t : U.term) :
        (∑ y, L i (x i) y * U.factor t i y) = ∑ a, c (x i) a * U.factor t i (f i (x i) a) := by
      simp only [L, Function.update_self, sum_mul]
      rw [sum_comm]
      simp [ite_mul]
    have tail (t : U.term) (a : I) :
        (∏ j ∈ univ.erase i, ∑ y, L j (x j) y * U.factor t j y) =
          ∏ j ∈ univ.erase i, U.factor t j (f j (x j) a) := by
      apply prod_congr rfl
      intro j hj
      have hn := (mem_erase.mp hj).1
      simp [L, hn, ite_mul, hi j hn (x j) b a]
    rw [he]
    simp only [Raw.coeff, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro t _
    rw [← mul_prod_erase _ _ (mem_univ i), cent, sum_mul]
    apply sum_congr rfl
    intro a _
    rw [tail t a, ← mul_prod_erase _ _ (mem_univ i), mul_assoc]

theorem place_term (z : A → F) (e : A ⊕ Unit → ℕ) (i : A) (g : ℕ) :
    Tensor.place (Sum.elim id (fun _ => i))
        (Tensor.ofRaw (Raw.ofTable (fun j => Level 1 (e j)) (term z e i g))) ≤
      sphereTensor z (Function.update (fun j => e (.inl j)) i g) := by
  classical
  let loc : A ⊕ Unit → A := Sum.elim id (fun _ => i)
  let e' := Function.update (fun j => e (.inl j)) i g
  let U := Raw.ofTable (fun j => Level 1 (e' j)) (sphereForm z e')
  let V := (Raw.ofTable (fun j => Level 1 (e j)) (term z e i g)).group loc
  let fromOld (j : A) (x : V.leg j) : Level 1 (e (.inl j)) := x ⟨.inl j, rfl⟩
  let fromNew (x : V.leg i) : Level 1 (e (.inr ())) := x ⟨.inr (), rfl⟩
  let c (x : V.leg i) (w : Level 1 g) :=
    fusion F (fromOld i x).val.val (fromNew x).val.val w.val.val
  let f (j : A) (x : V.leg j) (w : Level 1 g) : Level 1 (e' j) :=
    ⟨if j = i then w.val else (fromOld j x).val, by
      by_cases h : j = i
      · subst j; simpa [e'] using w.2
      · simpa [h, e'] using (fromOld j x).2⟩
  change U.Restricts V
  apply local_sum U V i c f
  · intro j hj x a b
    exact Subtype.ext (by simp [f, hj])
  · intro x
    unfold V U
    erw [Raw.coeff_group, Raw.coeff_ofTable]
    unfold term
    apply sum_congr rfl
    intro y _
    erw [Raw.coeff_ofTable]
    congr 2
    funext j
    exact Subtype.ext (Insertion.changeAt_val i (fun l => fromOld l (x l)) y j)

end OAI.LinearAlgebra.MatrixExponent.Routing.Added
end

/-!
# Principal parts of a product of sphere forms

All factors use one moving position. Nonpositive total Laurent order
at one pole implies an additive bound on the sum of fused energies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Added

open Finset Polynomial Sphere Sphere.Motion
open scoped Classical
variable {F A : Type} [Field F] [Fintype A] [DecidableEq A]

private def word (z : A → F) (i : A) {e : A ⊕ Unit → ℕ} (x : States 1 e) :=
  triple (Insertion.mark z i) (x (.inl i)).val.val (x (.inr ())).val.val
    (Insertion.rest z i (fun j => x (.inl j)))

private def bound (e : A ⊕ Unit → ℕ) := ((∑ i, e (.inl i)) + e (.inr ())) / 2

omit [Field F] in
private theorem weight_word (z : A → F) (i : A) {e : A ⊕ Unit → ℕ} (x : States 1 e) :
    weight (word z i x) / 2 = bound e := by
  rw [word, weight_triple, (x (.inl i)).property, (x (.inr ())).property, Insertion.weight_rest]
  unfold bound
  have := Finset.sum_erase_add univ (fun j => e (.inl j)) (mem_univ i)
  omega

private theorem value_word (z : A → F) (i : A) (e : A ⊕ Unit → ℕ) :
    ∃ c : F, ∀ s x, sphereForm (Sum.elim z (fun _ => s)) e x =
      c * wick fieldKernel ((word z i x).map (atPoint s)) := by
  obtain ⟨b, m, rfl⟩ : ∃ b m, e = Insertion.energy b m := by
    refine ⟨fun i => e (.inl i), e (.inr ()), funext ?_⟩
    rintro (j|⟨⟩) <;> rfl
  obtain ⟨c, _, hc⟩ := Insertion.order_added z i b m
  refine ⟨c, fun s x => ?_⟩
  have he : Insertion.add (e := b) (g := m) (fun j => x (.inl j)) (x (.inr ())) = x := by
    funext j
    rcases j with j|⟨⟩ <;> rfl
  have h := hc s (fun j => x (.inl j)) (x (.inr ()))
  rw [he] at h
  exact h

private def level (e : A ⊕ Unit → ℕ) (i : A) (u : ℕ) : ℤ :=
  e (.inl i) + e (.inr ()) + 2 * ((u : ℤ) - bound e)

private theorem jet_term (z : A → F) (hz : Function.Injective z) (i : A)
    (e : A ⊕ Unit → ℕ) (u : ℕ) :
    let g := level e i u
    let Z := Insertion.marks z
    ∃ c : F, ∀ x : States 1 e,
      jet (z i) (poles (Z.erase (z i)) (fun _ => bound e)) u (numerator Z (word z i x)) =
        if g < 0 then 0 else c * term z e i g.toNat x := by
  intro g Z
  obtain ⟨c, hc, hf⟩ := Insertion.order_base z i (Function.update (fun j => e (.inl j)) i g.toNat)
  refine ⟨c⁻¹, fun x => ?_⟩
  have h := coeff_fusion (Insertion.mark z i) (x (.inl i)).val.val (x (.inr ())).val.val
    (Insertion.rest z i (fun j => x (.inl j))) (Insertion.rest_avoids z hz i _) ((u : ℤ) - bound e)
  dsimp only at h
  rw [(x (.inl i)).property, (x (.inr ())).property] at h
  change (laurent (z i) (numerator Z (word z i x)) (denominatorPoly Z (word z i x))).coeff _ =
    if g < 0 then 0 else _ at h
  rw [denominatorPoly, weight_word, poles_split _ (show z i ∈ Z from (Insertion.mark z i).property),
    coeff_laurent _ _ _ _ (poles_eval _ (notMem_erase _ _))] at h
  rw [h]
  split_ifs
  · rfl
  unfold term
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  erw [hf, Insertion.changeAt_val, ite_eq_left rfl, Insertion.rest_changeAt]
  unfold outcome
  rw [mul_left_comm, ← mul_assoc c⁻¹, inv_mul_cancel₀ hc, one_mul]
  rfl

variable {n : ℕ}

omit [DecidableEq A] in
private theorem choose_levels (e : Fin n → A ⊕ Unit → ℕ) (M : ℕ) (he : ∀ j i, e j i ≤ M)
    (i : A) (v : Fin n → ℕ) (hv : (∑ j, v j) ≤ ∑ j, bound (e j))
    (h : ∀ j, 0 ≤ level (e j) i (v j)) :
    ∃ y : Choice e M, y.val.1 = i ∧ ∀ j, (y.val.2 j).val = (level (e j) i (v j)).toNat := by
  let g j := (level (e j) i (v j)).toNat
  let k j := e j (.inl i) + e j (.inr ())
  have eqn (j) : (g j : ℤ) = k j + 2 * ((v j : ℤ) - bound (e j)) := by
    dsimp only [g]
    rw [Int.toNat_of_nonneg (h j)]
    simp only [k, level, Nat.cast_add]
  have lim : (∑ j, g j) ≤ ∑ j, k j := by
    have hh : (∑ j, (g j : ℤ)) ≤ ∑ j, (k j : ℤ) := by
      simp only [eqn, sum_add_distrib, ← mul_sum, sum_sub_distrib, ← Nat.cast_sum]
      omega
    exact_mod_cast hh
  have total : (∑ j, k j) ≤ 2 * n * M := calc
    _ ≤ ∑ _ : Fin n, (M + M) := sum_le_sum fun j _ => Nat.add_le_add (he j _) (he j _)
    _ = _ := by simp; ring
  have each (j) : g j ≤ 2 * n * M :=
    (single_le_sum (fun i _ => Nat.zero_le (g i)) (mem_univ j)).trans (lim.trans total)
  exact ⟨⟨(i, fun j => ⟨g j, Nat.lt_succ_of_le (each j)⟩), lim⟩, rfl, fun _ => rfl⟩

/-- Expand a product at one common moving position, with coefficients
independent of all basis states. -/
theorem principal [Nonempty A] (z : A → F) (hz : Function.Injective z) (s : F) (hs : s ∉ Set.range z)
    (e : Fin n → A ⊕ Unit → ℕ) (M : ℕ) (he : ∀ j i, e j i ≤ M) :
    ∃ coeff : Choice e M → F, ∀ x : (j : Fin n) → States 1 (e j),
      (∏ j, sphereForm (Sum.elim z (fun _ => s)) (e j) (x j)) =
        ∑ v, coeff v * ∏ j, term z (e j) v.val.1 (v.val.2 j).val (x j) := by
  let Z := Insertion.marks z
  have hs' : s ∉ Z := by simpa [Z, Insertion.marks, Set.mem_range] using hs
  let i₀ : A := Classical.arbitrary A
  choose P hP using fun j => Insertion.order_polynomial z (e j)
  choose t ht hp using hP
  have pn (j i x) : P j x = C (t j i) * numerator Z (word z i x) := hp j i x
  let X := (j : Fin n) → States 1 (e j)
  let val (v : Choice e M) (x : X) := ∏ j, term z (e j) v.val.1 (v.val.2 j).val (x j)
  let W := Submodule.span F (Set.range val)
  have mem : (fun x : X => ∏ j, (P j (x j)).eval s / (poles Z (fun _ => bound (e j))).eval s) ∈ W := by
    apply product_mem W Z ⟨_, (Insertion.mark z i₀).property⟩
    · intro j x
      rw [pn j i₀, natDegree_C_mul (ht j i₀)]
      rw [← weight_word z i₀ (x j)]
      simpa [denominatorPoly, degree_poles] using degree_numerator Z (word z i₀ (x j))
    intro y hy u hu
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    choose b hb using fun j => jet_term z hz i (e j) (u j)
    let Q j := poles (Z.erase (z i)) (fun _ => bound (e j))
    have key (j) (x : X) : jet (z i) (Q j) (u j) (P j (x j)) =
        if level (e j) i (u j) < 0 then 0
        else t j i * b j * term z (e j) i (level (e j) i (u j)).toNat (x j) := by
      rw [pn j i, ← Polynomial.smul_eq_C_mul, map_smul, hb j (x j)]
      simp only [smul_eq_mul, mul_ite, mul_zero, mul_assoc]
    change (fun x : X => ∏ j, jet (z i) (Q j) (u j) (P j (x j))) ∈ W
    by_cases pos : ∀ j, 0 ≤ level (e j) i (u j)
    · obtain ⟨v, hv, hv'⟩ := choose_levels e M he i u hu pos
      have hval : val v ∈ W := Submodule.subset_span ⟨v, rfl⟩
      convert W.smul_mem (∏ j, t j i * b j) hval using 1
      funext x
      simp only [key, not_lt.mpr (pos _), ite_false, Pi.smul_apply, smul_eq_mul, val, hv, hv',
        prod_mul_distrib]
    · push Not at pos
      obtain ⟨j, hj⟩ := pos
      convert W.zero_mem using 1
      funext x
      exact prod_eq_zero (mem_univ j) (by rw [key, ite_eq_left hj])
  choose c hc using fun j => value_word z i₀ (e j)
  have target : (fun x : X => ∏ j, sphereForm (Sum.elim z (fun _ => s)) (e j) (x j)) ∈ W := by
    convert W.smul_mem (∏ j, c j / t j i₀) mem using 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, ← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    rw [hc j s (x j), ← eval_sphere Z _ s hs', pn j i₀, eval_mul, eval_C, denominatorPoly, weight_word]
    rw [mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _ (ht j i₀)]
  obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp target
  refine ⟨k, fun x => ?_⟩
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, val] using (congrFun hk x).symm

end OAI.LinearAlgebra.MatrixExponent.Routing.Added
end

/-!
# Closing a product of spheres at a shared insertion

Expand the product in nonpositive Laurent orders at one of the original
marks. For each term, any closed restriction costs at most the product
with updated energies at that single site. The number of terms costs
only a polynomial factor per sphere.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Sphere Spectral Finset

namespace Added

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A] {n : ℕ}

private theorem price_product (f : Tensor F A →+* ℝ) (hf : Monotone f) (z : A → F)
    (B : ℝ) (t : A ⊕ Unit → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ t (.inr ()))
    (hbase : ∀ e, f (sphereTensor z e) ≤ Real.exp (B + ∑ i, t (.inl i) * (e i : ℝ)))
    (s : F) (M : ℕ) (e : Fin n → A ⊕ Unit → ℕ) (hn : 0 < n) (he : ∀ j i, e j i ≤ M)
    (T : Tensor F A)
    (hT : Tensor.pad Unit T ≤ ∏ j, sphereTensor (Sum.elim z (fun _ => s)) (e j))
    (c : Choice e M → F)
    (hc : ∀ x : (j : Fin n) → States 1 (e j),
      (∏ j, sphereForm (Sum.elim z (fun _ => s)) (e j) (x j)) =
        ∑ v, c v * ∏ j, term z (e j) v.val.1 (v.val.2 j).val (x j)) :
    f T ≤ ∏ j, (((M : ℝ) + 2) ^ (Fintype.card A + 8) * Real.exp (B + ∑ i, t i * (e j i : ℝ))) := by
  classical
  let J := Choice e M
  let X (j : Fin n) i := Level 1 (e j i)
  let U (v : J) (j : Fin n) :=
    Tensor.ofRaw (Raw.ofTable (X j) (term z (e j) v.val.1 (v.val.2 j).val))
  let loc (v : J) : A ⊕ Unit → A := Sum.elim id (fun _ => v.val.1)
  have hp : Tensor.pad Unit T ≤ ∑ v, ∏ j, U v j :=
    hT.trans (Tensor.product_span_le X _ _ c hc)
  have bound := Tensor.padded_sum_le (fun v => ∏ j, U v j) (fun v => v.val.1) T hp
  let E := Real.exp (∑ j, (B + ∑ i, t i * (e j i : ℝ)))
  have each (v : J) : f (Tensor.place (loc v) (∏ j, U v j)) ≤ E := by
    have hs : Function.Surjective (loc v) := fun i => ⟨.inl i, rfl⟩
    rw [Tensor.place_eq_group _ hs, map_prod, map_prod]
    calc
      _ ≤ ∏ j, Real.exp (B + ∑ i, t (.inl i) * (reassigned v j i : ℝ)) := by
        apply prod_le_prod₀
        · intro j _
          rw [← map_zero f]
          exact hf (Tensor.zero_le _)
        · intro j _
          rw [← Tensor.place_eq_group]
          exact (hf (place_term z (e j) _ _)).trans (hbase _)
      _ ≤ E := by rw [← Real.exp_sum]; exact Real.exp_le_exp.mpr (penalty B t ht v)
  calc
    f T ≤ ∑ v, f (Tensor.place (loc v) (∏ j, U v j)) := by rw [← map_sum]; exact hf bound
    _ ≤ (Fintype.card J : ℝ) * E := by
      simpa using sum_le_sum (s := univ) (fun v _ => each v)
    _ ≤ (((M : ℝ) + 2) ^ (Fintype.card A + 8)) ^ n * E :=
      mul_le_mul_of_nonneg_right (card_choice e M hn he) (Real.exp_pos _).le
    _ = _ := by simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, E, Real.exp_sum]

end Added

/-- Joint closure of an arbitrary list of sphere forms at one shared
parameter. The polynomial surcharge depends only on the old site count
and the maximum incident energy. -/
theorem bounded_forms (F : Type) [Field F] : BoundedForms F := by
  intro A _ _ _ f hf z hz B t ht hbase s hs M w hw T hT
  by_cases hempty : w = []
  · subst w
    simp only [List.map_nil, List.prod_nil] at hT ⊢
    rw [← (Tensor.padding Unit).one] at hT
    rw [← map_one f]
    exact hf (((Tensor.padding Unit).le_iff _ _).mp hT)
  have hn := List.length_pos_of_ne_nil hempty
  have he : ∀ j i, w.get j i ≤ M := fun j => hw _ (w.get_mem j)
  obtain ⟨c, hc⟩ := Added.principal z hz s hs w.get M he
  rw [← List.ofFn_get w, List.map_ofFn] at hT ⊢
  erw [List.prod_ofFn] at hT ⊢
  exact Added.price_product f hf z B t ht hbase s M w.get hn he T hT c hc

end OAI.LinearAlgebra.MatrixExponent.Routing
end
