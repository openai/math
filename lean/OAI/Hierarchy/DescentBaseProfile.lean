import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Finite smoothing of the dyadic base depths for a compiler reset

The initial depth is the least depth satisfying the load and group constraints.
A sweep sends each neighbor's depth, diminished by the propagation allowance.
A depth not already transmitted can gain at most the original ceiling minus
the number of sweeps. This yields stabilization after a bounded number of
sweeps and a sum bound on the actual numbers of bases. -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators
variable {V : Type*}

/-- The finite relaxation, including its initial data at every sweep. -/
def relax (near : V → Finset V) (seed : V → ℕ) (g : ℕ) : ℕ → V → ℕ
  | 0,v => seed v
  | n+1,v => max (seed v) ((near v).sup (fun w => relax near seed g n w-g))

theorem seed_le (near : V → Finset V) (seed : V → ℕ) (g n : ℕ) (v : V) :
    seed v≤relax near seed g n v := by
  cases n with
  | zero => exact le_rfl
  | succ i => exact le_max_left _ _

theorem relax_le (near : V → Finset V) {seed : V → ℕ} {M : ℕ} (cap : ∀v,seed v≤M)
    (g n : ℕ) (v : V) : relax near seed g n v≤M := by
  induction n generalizing v with
  | zero => exact cap v
  | succ n ih => exact max_le (cap v) (Finset.sup_le fun w _ => (Nat.sub_le _ _).trans (ih w))

private theorem sends (near : V → Finset V) (seed : V → ℕ) (g n : ℕ) {v w : V} (edge : w∈near v) :
    relax near seed g n w-g≤relax near seed g (n+1) v :=
  (Finset.le_sup (f:=fun z=>relax near seed g n z-g) edge).trans (le_max_right _ _)

private theorem new_depth (near : V → Finset V) {seed : V → ℕ} {M g : ℕ}
    (cap : ∀v,seed v≤M) (hg : 0<g) (n : ℕ) (v : V) :
    relax near seed g (n+1) v ≤ max (relax near seed g n v) (M-n) := by
  induction n generalizing v with
  | zero =>
    exact (relax_le near cap g _ v).trans (by simp)
  | succ n ih =>
    apply max_le
    · exact (seed_le near seed g (n+1) v).trans (le_max_left _ _)
    · apply Finset.sup_le
      intro w hw
      have p := ih w
      have q := sends near seed g n hw
      omega

/-- The smoothed profile after the largest possible initial depth plus one sweep. -/
def depth (near : V → Finset V) (seed : V → ℕ) (g M : ℕ) := relax near seed g M

theorem depth_fixed (near : V → Finset V) {seed : V → ℕ} {M g : ℕ}
    (cap : ∀v,seed v≤M) (hg : 0<g) (v : V) :
    max (seed v) ((near v).sup (fun w=>depth near seed g M w-g)) ≤depth near seed g M v := by
  change relax near seed g (M+1) v ≤ relax near seed g M v
  simpa only [Nat.sub_self, Nat.max_zero] using new_depth near cap hg M v

theorem depth_smooth (near : V → Finset V) {seed : V → ℕ} {g M : ℕ}
    (cap : ∀v,seed v≤M) (hg : 0<g) {v w : V} (edge : w∈near v) :
    depth near seed g M w ≤ depth near seed g M v+g := by
  have : depth near seed g M w-g≤depth near seed g M v :=
    (sends near seed g M edge).trans (depth_fixed near cap hg v)
  omega

private theorem relax_mono (near : V → Finset V) (seed : V → ℕ) (g n : ℕ) (v : V) :
    relax near seed g n v ≤ relax near seed g (n+1) v := by
  induction n generalizing v with
  | zero => exact le_max_left _ _
  | succ n ih =>
    exact max_le (le_max_left _ _) (Finset.sup_le fun w hw =>
      (Nat.sub_le_sub_right (ih w) g).trans (sends near seed g (n+1) hw))

private theorem local_count (near : V → Finset V) {seed : V → ℕ} (M g : ℕ) (v : V) :
    2^g*2^depth near seed g M v ≤ 2^g*2^seed v+∑w∈near v,2^depth near seed g M w := by
  classical
  let b := depth near seed g M
  change 2^g*2^b v ≤ 2^g*2^seed v+∑w∈near v,2^b w
  by_cases old : b v≤seed v
  · exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) old)).trans (Nat.le_add_right _ _)
  have gained : b v≤(near v).sup (fun w=>b w-g) := by
    have m := relax_mono near seed g M v
    change b v≤max (seed v) ((near v).sup (fun w=>b w-g)) at m
    omega
  have inhabited : (near v).Nonempty := by
    by_contra! empty
    simp [empty] at gained
    omega
  obtain ⟨w,hw,atW⟩ := Finset.exists_mem_eq_sup (near v) inhabited (fun z=>b z-g)
  rw [atW] at gained
  have exp : g+b v≤b w := by omega
  calc
    2^g*2^b v = 2^(g+b v) := (pow_add ..).symm
    _ ≤ 2^b w := Nat.pow_le_pow_right (by decide) exp
    _ ≤ ∑z∈near v,2^b z := Finset.single_le_sum (fun z _ => Nat.zero_le (2^b z)) hw
    _ ≤ _ := Nat.le_add_left _ _

private theorem sum_neighbors [Fintype V] (near : V → Finset V)
    (undirected : ∀v w,w∈near v ↔ v∈near w) (cost : V → ℕ) :
    (∑v,∑w∈near v,cost w)=∑w,(near w).card*cost w := by
  classical
  calc
    _ = ∑v,∑w,if v∈near w then cost w else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      simp_rw [←undirected v]
      rw [←Finset.sum_filter,Finset.filter_mem_eq_inter,Finset.univ_inter]
    _ = _ := by
      rw [Finset.sum_comm]
      simp []

/-- The high levels propagated through neighboring sites add at most the cost
of another copy of the raw seeds when the dyadic decay beats twice the degree. -/
theorem total_depth [Fintype V] (near : V → Finset V)
    (undirected : ∀v w,w∈near v ↔ v∈near w) {Δ : ℕ} (degree : ∀v,(near v).card≤Δ)
    (seed : V → ℕ) (g M : ℕ) (spread : 2*Δ≤2^g) :
    (∑v,2^depth near seed g M v)≤2*∑v,2^seed v := by
  let t := fun v=>2^depth near seed g M v
  have localBound := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => local_count near (seed:=seed) M g v)
  change (∑v,2^g*t v)≤∑v,(2^g*2^seed v+∑w∈near v,t w) at localBound
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,sum_neighbors near undirected] at localBound
  have sumDegree : (∑v,(near v).card*t v)≤Δ*∑v,t v := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => Nat.mul_le_mul_right (t v) (degree v)
  have bound := Nat.mul_le_mul_right (∑v,t v) spread
  change (∑v,t v)≤2*∑v,2^seed v
  apply Nat.le_of_mul_le_mul_left (c:=2^g) _ (Nat.two_pow_pos _)
  nlinarith only [localBound,sumDegree,bound]

end Hierarchy.DescentBaseProfile

end OAI
