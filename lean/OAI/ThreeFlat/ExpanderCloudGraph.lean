import OAI.ThreeFlat.ExpanderCloudEnergy
import OAI.ThreeFlat.ExpanderCloudMatching

namespace OAI
/-! # The regular multigraph obtained by cloud replacement -/

namespace ThreeFlat.Expander

open Finset
open scoped BigOperators Classical

variable {V P X : Type*} [Fintype V] [Fintype P] [PseudoMetricSpace X]

/-- A copy of the inner graph in each cloud, and as many copies of the
matching arc as the inner degree at each port. -/
noncomputable def cloudArcs (c : P → P → ℕ) (h : ℕ) (e : Equiv.Perm (V × P))
    (a b : V × P) : ℕ :=
  (if a.1 = b.1 then c a.2 b.2 else 0) + (if e a = b then h else 0)

omit [Fintype V] [Fintype P] in
theorem cloudArcs_symm (c : P → P → ℕ) (h : ℕ) (e : Equiv.Perm (V × P))
    (hc : ∀ p q, c p q = c q p) (he : Function.Involutive e) (a b : V × P) :
    cloudArcs c h e a b = cloudArcs c h e b a := by
  have hm : e a = b ↔ e b = a :=
    ⟨fun h => by rw [← h, he], fun h => by rw [← h, he]⟩
  simp only [cloudArcs, hm, (eq_comm : a.1 = b.1 ↔ b.1 = a.1), hc a.2 b.2]

theorem cloudArcs_degree (c : P → P → ℕ) (h : ℕ) (e : Equiv.Perm (V × P))
    (hc : ∀ p, ∑ q, c p q = h) (a : V × P) : ∑ b, cloudArcs c h e a b = 2 * h := by
  simp only [cloudArcs, sum_add_distrib]
  rw [Fintype.sum_prod_type]
  simp [sum_ite_irrel, hc, two_mul]

omit [Fintype V] [Fintype P] in
private theorem transition_cloudArcs (c : P → P → ℕ) {h : ℕ} (hh : 0 < h)
    (e : Equiv.Perm (V × P)) (a b : V × P) :
    transition (cloudArcs c h e) (2*h) a b =
    ((if a.1 = b.1 then transition c h a.2 b.2 else 0) +
     (if e a = b then 1 else 0)) / 2 := by
  have hreal : (h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hh.ne'
  simp only [transition, cloudArcs, Nat.cast_add, Nat.cast_ite, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_zero]
  split_ifs <;> field_simp <;> ring

theorem energy_cloudArcs (c : P → P → ℕ) {h : ℕ} (hh : 0 < h)
    (e : Equiv.Perm (V × P)) (x : V × P → X) :
    energy (transition (cloudArcs c h e) (2 * h)) x =
    (internalEnergy (transition c h) x + matchingEnergy e x) / 2 := by
  let inner (a : V × P) := ∑ q, transition c h a.2 q * dist (x a) (x (a.1,q))^2
  have hrow (a : V × P) :
      ∑ b, transition (cloudArcs c h e) (2*h) a b * dist (x a) (x b)^2 =
      (1/2 : ℝ) * (inner a + dist (x a) (x (e a))^2) := by
    let D (b : V × P) := dist (x a) (x b)^2
    let I (b : V × P) := if a.1 = b.1 then transition c h a.2 b.2 else 0
    let M (b : V × P) : ℝ := if e a = b then 1 else 0
    have hint : ∑ b, I b * D b = inner a := by
      rw [Fintype.sum_prod_type]
      simp [I, D, inner, ite_mul, sum_ite_irrel]
    have hmatch : ∑ b, M b * D b = D (e a) := by simp [M, ite_mul]
    calc
      _ = (1/2 : ℝ) * ∑ b, (I b * D b + M b * D b) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro b _
        rw [transition_cloudArcs c hh e]
        change (I b + M b) / 2 * D b = _
        ring
      _ = _ := by rw [sum_add_distrib, hint, hmatch]
  calc
    _ = avg (fun a => (1/2 : ℝ) * (inner a + dist (x a) (x (e a))^2)) := avg_congr _ _ hrow
    _ = _ := by
      rw [avg_mul, avg_add]
      have hi : avg inner = internalEnergy (transition c h) x :=
        avg_prod (fun u p => ∑ q, transition c h p q * dist (x (u,p)) (x (u,q))^2)
      rw [hi]
      change (1/2 : ℝ) * (_ + matchingEnergy e x) = _
      ring

/-- Uniform matching arcs between clouds recover the prescribed outer matrix. -/
theorem matchingEnergy_projected [DecidableEq V] {q : ℕ} (c : V → V → ℕ)
    (e : Equiv.Perm (V × Fin q))
    (hcount : ∀ u v,
      (univ.filter (fun p : Fin q => (e (u,p)).1 = v)).card = c u v)
    (y : V → X) :
    matchingEnergy e (fun a => y a.1) = energy (transition c q) y := by
  unfold matchingEnergy energy
  rw [avg_prod (fun u (p : Fin q) => dist (y u) (y (e (u,p)).1)^2)]
  apply avg_congr
  intro u
  rw [avg, Fintype.card_fin, ThreeFlat.cloudMatching_sum hcount u
    (fun v => dist (y u) (y v)^2), sum_div]
  apply sum_congr rfl
  intro v _
  simp only [transition, nsmul_eq_mul]
  ring

universe u

/-- Replace each outer vertex by an inner graph on the ports. One graph of
twice the inner degree works simultaneously for every metric target. -/
theorem exists_cloud_graph [Nonempty V] {q h : ℕ} (hq : 0 < q) (hh : 0 < h)
    (c : V → V → ℕ) (hs : ∀ i j, c i j = c j i) (hr : ∀ i, ∑ j, c i j = q)
    (H : Fin q → Fin q → ℕ) (hHs : ∀ i j, H i j = H j i) (hHr : ∀ i, ∑ j, H i j = h) :
    ∃ c' : (V × Fin q) → (V × Fin q) → ℕ,
      (∀ i j, c' i j = c' j i) ∧ (∀ i, ∑ j, c' i j = 2*h) ∧
      ∀ (Y : Type u) [PseudoMetricSpace Y] {β γ : ℝ}, 1 ≤ β → 0 ≤ γ →
        Bound (transition H h) Y β → Bound (transition c q) Y γ →
        Bound (transition c' (2*h)) Y (2*(6+18*γ)*β) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  obtain ⟨e, he, hcount⟩ := exists_cloudMatching c hs hr
  refine ⟨cloudArcs H h e, cloudArcs_symm H h e hHs he, cloudArcs_degree H h e hHr, ?_⟩
  intro Y _ β γ hβ hγ inner outer x
  have ho (y : V → Y) : variance y ≤ γ * matchingEnergy e (fun i => y i.1) := by
    rw [matchingEnergy_projected c e hcount]
    exact outer y
  have hc := cloud_variance_le (transition H h) e hγ inner ho x
  have hm : 0 ≤ matchingEnergy e x := avg_nonneg fun _ => sq_nonneg _
  have coeff : 9*γ ≤ (6+18*γ)*β := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (show 0 ≤ 6 + 18*γ by positivity)]
  have gain := mul_le_mul_of_nonneg_right coeff hm
  rw [energy_cloudArcs H hh e]
  linarith

end ThreeFlat.Expander

end OAI
