import OAI.Hierarchy.DescentBadBaseCost

namespace OAI
/-! # Pay the actual mass on the union of affected source and destination bases -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

abbrev BaseId (b : V → ℕ) := Σ v, Block (b v)
def label (b : V → ℕ) (p : BaseId b) : V × ℕ := (p.1,p.2.val)

omit [Fintype V] [DecidableEq V] in
private theorem label_injective (b : V → ℕ) : Function.Injective (label b) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  have eq : v=w := congrArg Prod.fst h
  subst w
  exact congrArg (Sigma.mk v) (Fin.ext (congrArg Prod.snd h))

def validBases (b : V → ℕ) (s : Finset (V×ℕ)) : Finset (BaseId b) :=
  Finset.univ.filter fun p => label b p∈s

theorem validBases_card (b : V → ℕ) (s : Finset (V×ℕ)) :
    (validBases b s).card≤ s.card := by
  rw [←Finset.card_image_of_injective _ (label_injective b)]
  apply Finset.card_le_card
  rintro z hz
  obtain ⟨p,h,rfl⟩ := Finset.mem_image.mp hz
  exact (Finset.mem_filter.mp h).2

def baseValue (b : V → ℕ) (hk : ∀ v,b v≤k)
    (x : V → Block k → ℝ) (L : Layout k) (p : BaseId b) : ℝ :=
  load (dyadicLayout (hk p.1) L) (x p.1) p.2

/-- Both endpoint and propagation keys can repeat in the list of causes. Only
distinct valid base IDs are charged. Heavy base loads, independently of the
selection, are paid by the level-zero actual bins. -/
theorem bad_volume (b : V → ℕ) (hk : ∀v,b v≤k) (x : V → Block k → ℝ) (L : Layout k)
    (F : ℝ) (pos : ∀v i,0≤x v i) (small : ∀v i,x v i≤1)
    (fits : ∀v,mean (x v) (Block (b v))≤1) (forcedKeys capacityKeys : Finset (V×ℕ)) :
    ∑ p∈validBases b (forcedKeys∪capacityKeys),baseValue b hk x L p ≤
      2*((forcedKeys.card:ℝ)+capacityKeys.card) +
      2*∑v,levelCharge 0 F (DescentLinearLayouts.layout (hk v) L) (x v ∘ address k) := by
  have full := mass_of_bad (validBases b (forcedKeys∪capacityKeys)) (baseValue b hk x L)
  have counts : ((validBases b (forcedKeys∪capacityKeys)).card:ℝ) ≤
      (forcedKeys.card:ℝ)+(capacityKeys.card:ℝ) := by
    exact_mod_cast (validBases_card b _).trans (Finset.card_union_le forcedKeys capacityKeys)
  have heavy : (∑p∈Finset.univ.filter (fun p => 2<baseValue b hk x L p),baseValue b hk x L p) ≤
      2*∑v,levelCharge 0 F (DescentLinearLayouts.layout (hk v) L) (x v ∘ address k) := by
    rw [Finset.sum_filter,Fintype.sum_sigma,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    rw [←address_levelCharge]
    have payment := (marked_bins 0 F (dyadicLayout (hk v) L) (x v) (pos v) (small v) (fits v)).2
    simp only [Finset.sum_filter] at payment
    refine le_trans ?_ payment
    apply Finset.sum_le_sum
    intro j _
    by_cases marked : 2 < load (dyadicLayout (hk v) L) (x v) j
    · simp [baseValue, marked]
    · simp [baseValue, marked]
  linarith

end
end Hierarchy.DescentColonies

end OAI
