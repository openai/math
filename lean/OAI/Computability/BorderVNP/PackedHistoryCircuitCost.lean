import OAI.Computability.BorderVNP.PackedResources

/-! # Gate and count-field budgets of the full public history tree

Proposition 7.2 traverses the selected history bottom up. Each of its `T` epochs
contains `b` shortening subrounds of fan-in `k`, so one output visits
`(k^b)^T` bottom bundles. The following counts allow different costs at the
bottom bundles and at the internal nodes. They apply to gate counts and to
public count fields, which are reserved once per internal node.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Filter TeamScales

/-- Cost of a full ordered history tree with the specified costs at leaves and internal nodes. -/
def historyTreeCost (k leaf node : ℕ) : ℕ → ℕ
  | 0 => leaf
  | d + 1 => k * historyTreeCost k leaf node d + node

/-- An upper bound on the local compilation recurrence bounds the whole tree,
including depth zero and a unary tree. -/
theorem le_historyTreeCost {k leaf node : ℕ} (cost : ℕ → ℕ) (d : ℕ)
    (base : cost 0 ≤ leaf) (step : ∀ j < d, cost (j+1) ≤ k * cost j + node) :
    cost d ≤ historyTreeCost k leaf node d := by
  induction d with
  | zero => exact base
  | succ d ih =>
    exact (step d (Nat.lt_succ_self d)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left k (ih (fun j hj => step j (by omega)))) node)

/-- There are `k^d` leaves and at most `d*k^d` internal nodes, including the root. -/
theorem historyTreeCost_le {k : ℕ} (hk : 0 < k) (leaf node d : ℕ) :
    historyTreeCost k leaf node d ≤ k^d * (leaf + d*node) := by
  induction d with
  | zero => simp [historyTreeCost]
  | succ d ih =>
    calc
      _ ≤ k * (k^d * (leaf + d*node)) + node :=
        Nat.add_le_add_right (Nat.mul_le_mul_left k ih) node
      _ ≤ k * (k^d * (leaf + d*node)) + k^(d+1)*node :=
        Nat.add_le_add_left (Nat.le_mul_of_pos_left node (pow_pos hk _)) _
      _ = _ := by rw [pow_succ]; ring

/-- Traversal of all subrounds uses exactly the epoch pack multiplicity in the leaf factor. -/
theorem historyTreeCost_epochs {k : ℕ} (hk : 0 < k) (b t leaf node : ℕ) :
    historyTreeCost k leaf node (b*t) ≤ (k^b)^t * (leaf + (b*t)*node) := by
  rw [← pow_mul]
  exact historyTreeCost_le hk leaf node (b*t)

/-- The count bits of one public profile are indexed by seed, term, and word position.
There are no count fields at the leaves. -/
theorem historyProfileBits_le {k : ℕ} (hk : 0 < k) (b t seeds terms word : ℕ) :
    historyTreeCost k 0 (Fintype.card (Fin seeds × Fin terms × Fin word)) (b*t) ≤
      (k^b)^t * (b*t) * (seeds*terms*word) := by
  simpa [mul_assoc] using historyTreeCost_epochs hk b t 0 (seeds*terms*word)

/-- The strict Section 7.3 budget for a complete public traversal. The assumptions
on `leaf` and `node` are the sparse per-pack costs: tile count times maximum
descriptor count times a fixed power of the address width. The threshold is
independent of `r` and of the costs within those caps. -/
theorem eventually_historyTreeCost_below {α τ growth : ℝ} {k : ℕ} (b D : ℕ)
    (hα : α < 1/1000) (hτ : 0 < τ) (hτ' : τ < α/100) (hk : 0 < k)
    (hteams : τ * Real.logb 2 (k^b : ℕ) ≤ α) (hg : 1 ≤ growth)
    (hgrowth : τ * Real.logb 2 growth ≤ α/10) (γ : ℝ)
    (hγ : 2*α + 9/10 + 1/100 + τ/2000 < γ) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      let T := epochs τ n
      let cap := A * (r * (n : ℝ)^(9/10 : ℝ)) * (growth^T * width n α) * (logWidth r n : ℝ)^D
      ∀ leaf node : ℕ, (leaf : ℝ) ≤ cap → (node : ℝ) ≤ cap →
        (historyTreeCost k leaf node (b*T) : ℝ) < r * (n : ℝ)^γ := by
  have hK : 1 ≤ k^b := pow_pos hk b
  obtain ⟨ω,hω,work⟩ := eventually_sparse_resources_below hα hτ hτ' hK hteams hg hgrowth D γ hγ
  refine ⟨ω,hω,fun A hA => ?_⟩
  have hT : ∀ᶠ n : ℕ in atTop, 1 ≤ epochs τ n :=
    (VPVNP.Compression.tendsto_blockCount hτ).eventually_ge_atTop 1
  filter_upwards [hT, eventually_ge_atTop 1, work 1 (by norm_num),
    work (((b:ℝ)+1)*A) (by positivity)] with n hTn hn hrow hcost
  intro r hr hmax T cap leaf node hleaf hnode
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have ht' : 1 ≤ (T : ℝ) := by exact_mod_cast hTn
  have hα' : 0 ≤ α := by linarith
  have hwidth : 1 ≤ width n α := Nat.le_floor (by simpa using Real.one_le_rpow hn' hα')
  have hteam : (k^b)^T ≤ teams α τ (k^b) n := Nat.le_mul_of_pos_left _ hwidth
  have htile : growth^T * (width n α : ℝ) ≤ (n : ℝ)^(1/100 : ℝ) :=
    (by simpa only [one_mul] using (hrow r hr hmax).2.1 :
      growth^T * (width n α : ℝ) ≤ width n (1/100)).trans
        (Nat.floor_le (Real.rpow_nonneg (by positivity) _))
  have ht := (hcost r hr hmax).2.2
  have hsum : (leaf : ℝ) + b*T*node ≤ (((b : ℝ)+1)*T)*cap := by
    calc
      _ ≤ cap + (b:ℝ)*T*cap := add_le_add hleaf (mul_le_mul_of_nonneg_left hnode (by positivity))
      _ ≤ T*cap + (b:ℝ)*T*cap := add_le_add_left
        (le_mul_of_one_le_left (hleaf.trans' (Nat.cast_nonneg leaf)) ht') _
      _ = _ := by ring
  have htree := historyTreeCost_epochs hk b T leaf node
  have htree' : (historyTreeCost k leaf node (b*T) : ℝ) ≤ ((k^b)^T : ℕ) *
      ((leaf : ℝ) + (b:ℝ)*T*node) := by exact_mod_cast htree
  calc
    _ ≤ _ := htree'
    _ ≤ (teams α τ (k^b) n : ℝ) * ((((b:ℝ)+1)*T)*cap) :=
      mul_le_mul (by exact_mod_cast hteam) hsum (by positivity) (by positivity)
    _ ≤ (teams α τ (k^b) n : ℝ) * ((((b:ℝ)+1)*T) *
          (A * (r * (n : ℝ)^(9/10 : ℝ)) * (n : ℝ)^(1/100 : ℝ) * (logWidth r n : ℝ)^D)) := by
      dsimp only [cap]
      gcongr
    _ = _ := by ring
    _ < _ := ht

/-- The manuscript's strict exponent for reconstructing all public histories. -/
theorem eventually_historyTreeCost {α τ growth : ℝ} {k : ℕ} (b D : ℕ)
    (hα : α < 1/1000) (hτ : 0 < τ) (hτ' : τ < α/100) (hk : 0 < k)
    (hteams : τ * Real.logb 2 (k^b : ℕ) ≤ α) (hg : 1 ≤ growth)
    (hgrowth : τ * Real.logb 2 growth ≤ α/10) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ A : ℝ, 0 ≤ A →
      ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ 2^((n : ℝ)^ω) →
      let T := epochs τ n
      let cap := A * (r * (n : ℝ)^(9/10 : ℝ)) * (growth^T * width n α) * (logWidth r n : ℝ)^D
      ∀ leaf node : ℕ, (leaf : ℝ) ≤ cap → (node : ℝ) ≤ cap →
        (historyTreeCost k leaf node (b*T) : ℝ) < r * (n : ℝ)^(93/100 : ℝ) :=
  eventually_historyTreeCost_below b D hα hτ hτ' hk hteams hg hgrowth (93/100) (by linarith)

end Packing

end BorderVNP
end Computability
end OAI
