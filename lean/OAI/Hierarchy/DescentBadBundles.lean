import OAI.Hierarchy.DescentBadVolume

namespace OAI
/-! # Charging every exceptional core bundle to an actual bad base endpoint -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] {k : ℕ}

private theorem bins_mass {I Q : Type*} [Fintype I] [DecidableEq Q] (f : I → Q) (w : I → ℝ)
    (bad : Finset Q) : (∑ j∈bad,load f w j) = ∑i, if f i∈bad then w i else 0 := by
  unfold load
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases present : f i ∈ bad
  · rw [Finset.sum_eq_single_of_mem (f i) present]
    · simp [present]
    · intro j _ different
      exact ite_eq_right different
  · rw [ite_eq_right present]
    apply Finset.sum_eq_zero
    intro j member
    have different : j ≠ f i := fun equal => present (equal ▸ member)
    exact ite_eq_right different

/-- A physical old bundle occurs in the fallback bank if either endpoint
belongs to the true bad set. Its width is charged only once even when both
ends are bad. The incidence test counts the actual two endpoint sockets. -/
theorem bad_bundle_sum {I Q : Type*} [Fintype I] [DecidableEq I] [DecidableEq Q]
    (base : I → Q) (left right : E → I) (width : E → ℝ) (loadBound : I → ℝ)
    (pos : ∀e,0≤width e)
    (inc : ∀i,load left width i+load right width i≤loadBound i)
    (bad : Finset Q) :
    (∑e,if base (left e)∈bad ∨ base (right e)∈bad then width e else 0)≤
      ∑ q∈bad,load base loadBound q := by
  let touched := Finset.univ.filter (fun i : I => base i∈bad)
  have members (i : I) : i∈touched ↔ base i∈bad := by simp [touched]
  have both : (∑e,if base (left e)∈bad ∨ base (right e)∈bad then width e else 0)≤
      (∑e,if left e∈touched then width e else 0)+(∑e,if right e∈touched then width e else 0) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro e _
    by_cases a : base (left e)∈bad <;> by_cases b : base (right e)∈bad <;> simp [members,a,b,pos e]
  rw [←bins_mass,←bins_mass,←Finset.sum_add_distrib] at both
  apply both.trans
  rw [bins_mass,←Finset.sum_filter]
  exact Finset.sum_le_sum fun i _ => inc i

def baseOf (b : V → ℕ) (hk : ∀v,b v≤k) (L : Layout k) (x : V×Block k) : BaseId b :=
  ⟨x.1,dyadicLayout (hk x.1) L x.2⟩

omit [DecidableEq V] in
theorem true_base_mass (b : V → ℕ) (hk : ∀v,b v≤k) (L : Layout k)
    (weight : V → Block k → ℝ) (p : BaseId b) :
    load (baseOf b hk L) (fun q => weight q.1 q.2) p=baseValue b hk weight L p := by
  rcases p with ⟨v,q⟩
  unfold load
  rw [Fintype.sum_prod_type,Finset.sum_eq_single_of_mem v (Finset.mem_univ _)]
  · simp [baseValue,load,baseOf]
  · intro w _ ne
    apply Finset.sum_eq_zero
    intro i _
    apply ite_eq_right
    intro eqn
    exact ne (congrArg Sigma.fst eqn).symm

theorem exceptional_core (b : V → ℕ) (hk : ∀v,b v≤k) (L : Layout k)
    (left right : E → V×Block k) (width : E → ℝ) (weight : V → Block k → ℝ)
    (pos : ∀e,0≤width e)
    (inc : ∀ p,load left width p+load right width p≤weight p.1 p.2)
    (keys : Finset (V×ℕ)) :
    (∑e,if label b (baseOf b hk L (left e))∈keys ∨ label b (baseOf b hk L (right e))∈keys
        then width e else 0)≤ ∑ p∈validBases b keys,baseValue b hk weight L p := by
  have h := bad_bundle_sum (baseOf b hk L) left right width (fun p => weight p.1 p.2) pos inc (validBases b keys)
  simpa only [validBases,Finset.mem_filter,Finset.mem_univ,true_and,true_base_mass] using h

end
end Hierarchy.DescentColonies

end OAI
