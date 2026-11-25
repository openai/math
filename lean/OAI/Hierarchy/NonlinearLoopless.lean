import OAI.Hierarchy.NonlinearExpanders
import OAI.ThreeFlat.ExpanderCloudIteration
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace OAI
/-! # Loop removal and connectedness for uniform nonlinear expanders

Two copies of the input graph are linked by a matching. Each diagonal arc
is moved to this matching. A cycle through the resulting vertices gives a
connected graph independent of the metric target. -/

namespace Hierarchy.NonlinearExpanders

open ThreeFlat.Expander Finset
open scoped BigOperators Classical

private def flip {V : Type*} : Equiv.Perm (Bool × V) where
  toFun a := (!a.1,a.2)
  invFun a := (!a.1,a.2)
  left_inv a := by cases a with | mk b v => cases b <;> rfl
  right_inv a := by cases a with | mk b v => cases b <;> rfl

private theorem flip_involutive {V : Type*} : Function.Involutive (flip (V := V)) := by
  intro ⟨b,v⟩
  cases b <;> rfl

private theorem flip_ne {V : Type*} (a : Bool × V) : flip a ≠ a := by
  rcases a with ⟨b,v⟩
  cases b <;> simp [flip]

private noncomputable def doubled {V : Type*} (c : V → V → ℕ) (h : ℕ)
    (a b : Bool × V) : ℕ :=
  if a = b then 0 else cloudArcs c h flip a b + (if flip a = b then c a.2 a.2 else 0)

private theorem doubled_symm {V : Type*} (c : V → V → ℕ) (h : ℕ)
    (hs : ∀ i j, c i j = c j i) (a b : Bool × V) :
    doubled c h a b = doubled c h b a := by
  have flip_iff : flip a = b ↔ flip b = a :=
    ⟨fun H => H ▸ flip_involutive a, fun H => H ▸ flip_involutive b⟩
  by_cases H : a = b
  · subst b; rfl
  · simp only [doubled,ite_eq_right H,ite_eq_right (Ne.symm H),cloudArcs_symm c h flip hs flip_involutive a b]
    by_cases E : flip a = b
    · have E' := flip_iff.mp E
      have same : a.2 = b.2 := by
        simpa [flip] using congrArg (fun v : Bool × V => v.2) E
      simp [E,E',same]
    · simp [E,mt flip_iff.mpr E]

private theorem doubled_degree {V : Type*} [Fintype V] (c : V → V → ℕ) (h : ℕ)
    (hr : ∀ i, ∑ j, c i j = h) (a : Bool × V) : ∑ b, doubled c h a b = 2*h := by
  have row (b : Bool × V) :
      doubled c h a b + (if a = b then c a.2 a.2 else 0) =
        cloudArcs c h flip a b + (if flip a = b then c a.2 a.2 else 0) := by
    by_cases H : a = b
    · subst b; simp [doubled,cloudArcs,flip_ne]
    · simp [doubled,H]
  have H := congrArg (fun f : Bool × V → ℕ => ∑ b, f b) (funext row)
  simpa [sum_add_distrib,cloudArcs_degree c h flip hr] using H

private theorem cloud_bound {V X : Type*} [Fintype V] [Nonempty V] [PseudoMetricSpace X]
    (c : V → V → ℕ) {h : ℕ} (hh : 0 < h) {γ : ℝ} (hγ : 0 ≤ γ)
    (bnd : Bound (transition c h) X γ) :
    Bound (transition (doubled c h) (2*h)) X (48*(γ+1)) := by
  intro x
  let inner := internalEnergy (transition c h) x
  let matchE := matchingEnergy flip x
  have HI : 0 ≤ inner := avg_nonneg fun b => energy_transition_nonneg c h (fun i => x (b,i))
  have HM : 0 ≤ matchE := avg_nonneg fun _ => sq_nonneg _
  have H := cloud_variance_le (transition c h) flip (γ := 1) zero_le_one bnd
    (fun y => by
      have S := sq_nonneg (dist (y false) (y true))
      have A : matchingEnergy (flip (V := V)) (fun i => y i.1) =
          dist (y false) (y true)^2 := by
        unfold matchingEnergy
        change (avg fun p : Bool × V => dist (y p.1) (y (!p.1))^2) = _
        rw [avg_prod (fun b (_ : V) => dist (y b) (y (!b))^2)]
        simp_rw [avg_const]
        simp [avg,dist_comm (y true) (y false)]

      rw [A]
      simp [variance,avg,dist_comm (y true) (y false)]) x
  change variance x ≤ (6 + 18 * 1) * γ * inner + 9 * 1 * matchE at H
  have he : energy (transition (cloudArcs c h flip) (2*h)) x ≤
      energy (transition (doubled c h) (2*h)) x := by
    apply avg_le; intro a
    apply sum_le_sum; intro b _
    by_cases E : a = b
    · subst b; simp
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (show cloudArcs c h flip a b ≤ doubled c h a b by simp [doubled,E])
  rw [energy_cloudArcs c hh] at he
  change (inner+matchE)/2 ≤ _ at he
  calc
    variance x ≤ (6 + 18 * 1) * γ * inner + 9 * 1 * matchE := H
    _ ≤ 48*(γ+1)*((inner+matchE)/2) := by nlinarith [mul_nonneg hγ HM]
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

private theorem cycle_degree {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    ∑ j, (if (SimpleGraph.cycleGraph N).Adj i j then 1 else 0 : ℕ) = 2 := by
  obtain ⟨k, hk⟩ : ∃ k, N = k + 3 := ⟨N-3,by omega⟩
  subst N
  rw [sum_boole]
  calc
    _ = ((SimpleGraph.cycleGraph (k+3)).neighborFinset i).card := by
      apply congrArg Finset.card
      ext j
      simp
    _ = 2 := SimpleGraph.cycleGraph_degree_three_le

/-- Removing loops and adding a spanning cycle preserves common nonlinear
Poincaré bounds on all targets and increases the order exponent by one. -/
theorem exists_loopless_double {n h : ℕ} (hh : 0 < h) (hn : 1 ≤ n) {γ : ℝ} (hγ : 0 ≤ γ)
    (c : Fin (2^n) → Fin (2^n) → ℕ) (hs : ∀ i j, c i j = c j i)
    (hr : ∀ i, ∑ j, c i j = h) :
    ∃ G : Graph (n+1) (4*h), ∀ (X : Type*) [PseudoMetricSpace X],
      Bound (transition c h) X γ → Bound (transition G.arcs (4*h)) X (96*(γ+1)) := by
  let N := 2^(n+1)
  let e : Fin N ≃ Bool × Fin (2^n) := Fintype.equivOfCardEq (by simp [N,pow_succ,mul_comm])
  let d := fun i j : Fin N => doubled c h (e i) (e j)
  let a := fun i j : Fin N => d i j + h * (if (SimpleGraph.cycleGraph N).Adj i j then 1 else 0)
  have hN : 3 ≤ N := by
    have P : 2^2 ≤ 2^(n+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact le_trans (by decide : 3 ≤ 2^2) P
  have degreeD (i : Fin N) : ∑ j, d i j = 2*h :=
    (e.sum_comp (doubled c h (e i))).trans (doubled_degree c h hr (e i))
  refine ⟨⟨a,fun i j => ?_,fun i => ?_,fun i => ?_,fun i j => ?_⟩,?_⟩
  · simp only [a,d,doubled_symm c h hs (e i) (e j),SimpleGraph.adj_comm (G := SimpleGraph.cycleGraph N) i j]
  · simp [a,d,doubled]
  · change ∑ j, (d i j + h * _) = _
    rw [sum_add_distrib,← mul_sum,cycle_degree hN,degreeD]; omega
  · have step (u v : Fin N) (H : (SimpleGraph.cycleGraph N).Adj u v) : 0 < a u v := by
      simp only [a,ite_eq_left H,mul_one]; omega
    exact Relation.ReflTransGen.mono step i j
      ((SimpleGraph.reachable_iff_reflTransGen i j).mp (SimpleGraph.cycleGraph_preconnected i j))
  · intro X inst bnd x
    have HD := Bound.transition_reindex e (doubled c h) (cloud_bound c hh hγ bnd) x
    change variance x ≤ 48*(γ+1)*energy (transition d (2*h)) x at HD
    have HE : energy (transition d (2*h)) x ≤ 2 * energy (transition a (4*h)) x := by
      unfold energy
      rw [← avg_mul]
      apply avg_le; intro i
      rw [mul_sum]
      apply sum_le_sum; intro j _
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have pos : (0:ℝ) < h := Nat.cast_pos.mpr hh
      have dom : (d i j : ℝ) ≤ a i j := by exact_mod_cast (Nat.le_add_right ..)
      simp only [transition,Nat.cast_mul,Nat.cast_ofNat]
      calc
        _ ≤ (a i j : ℝ) / (2 * (h:ℝ)) := div_le_div_of_nonneg_right dom (by positivity)
        _ = _ := by field_simp; ring
    change variance x ≤ 96*(γ+1)*energy (transition a (4*h)) x
    calc
      variance x ≤ _ := HD
      _ ≤ 48*(γ+1)*(2*energy (transition a (4*h)) x) :=
        mul_le_mul_of_nonneg_left HE (by positivity)
      _ = _ := by ring

end Hierarchy.NonlinearExpanders

end OAI
