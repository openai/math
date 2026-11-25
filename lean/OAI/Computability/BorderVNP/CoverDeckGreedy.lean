import OAI.Computability.BorderVNP.CoverDeckProductKey

/-!
# Completing a deterministic deck translation down the tower

At each level the procedure chooses the first child minimizing the exact
histogram score. At the final level conditioning on the chosen residue is
conditioning on the translation itself. The resulting translation therefore
has no larger squared-deviation increment than the initial conditional mean.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

private theorem product_reduce_self (q l : ℕ) (x : Fin q → Deck l) :
    productReduction q (le_rfl : l ≤ l) x = x := by
  funext i
  change deckReduction le_rfl (x i) = x i
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective _ (x i)
  rw [← hg]
  rfl

private theorem self_mean (q l : ℕ) (f : (Fin q → Deck l) → ℚ) (x : Fin q → Deck l) :
    CoverDeck.residueMean (productReduction q (le_rfl : l ≤ l)) f x = f x := by
  have he : CoverDeck.fiber (productReduction q (le_rfl : l ≤ l)) x = {x} := by
    ext y
    simp [CoverDeck.fiber,product_reduce_self]
  simp [CoverDeck.residueMean,CoverDeck.histogram,he]

/-- Ascending canonical quaternion-address order breaks ties at every level. -/
noncomputable def digitChildren (q d : ℕ) (v : Fin q → Deck d) : List (Fin q → Deck (d+1)) :=
  letI := LinearOrder.lift' (AddressCircuit.productKey q (d+1)) (AddressCircuit.productKey q (d+1)).injective
  (CoverDeck.fiber (productReduction q (Nat.le_succ d)) v).sort

/-- Resolve `k` successive translation digits, retaining the selected
parent residue between steps. -/
noncomputable def refineDigits {B : Type*} [Fintype B] (q d l : ℕ)
    (prior candidate : B → (Fin q → Deck l) → ℚ) (mean : B → ℚ) (start : Fin q → Deck d) :
    (k : ℕ) → d+k ≤ l → Option (Fin q → Deck (d+k))
  | 0, _ => some start
  | k+1, hk => (refineDigits q d l prior candidate mean start k (by omega)).bind fun v =>
    CoverDeck.chooseResidue (CoverDeck.conditionalScore (productReduction q hk) prior candidate mean)
      (digitChildren q (d+k) v)

private theorem resolve_mean {B : Type*} [Fintype B] (q d l : ℕ)
    (prior candidate : B → (Fin q → Deck l) → ℚ) (mean : B → ℚ) (start : Fin q → Deck d)
    (k : ℕ) (hk : d+k ≤ l) :
    ∃ v, refineDigits q d l prior candidate mean start k hk = some v ∧
      CoverDeck.residueMean (productReduction q hk) (CoverDeck.increment prior candidate mean) v ≤
      CoverDeck.residueMean (productReduction q (show d ≤ l by omega))
        (CoverDeck.increment prior candidate mean) start := by
  induction k with
  | zero => exact ⟨start,rfl,le_rfl⟩
  | succ k ih =>
    obtain ⟨v,hv,hprior⟩ := ih (by omega)
    have hlist (w) : w ∈ digitChildren q (d+k) v ↔
        productReduction q (Nat.le_succ (d+k)) w = v := by
      simp [digitChildren,CoverDeck.fiber]
    obtain ⟨u,hu,_,hule⟩ := choose_product_digit q (d+k) l hk prior candidate mean
      v (digitChildren q (d+k) v) hlist
    exact ⟨u, by rw [refineDigits,hv,Option.bind_some]; exact hu, hule.trans hprior⟩

/-- Resolving every remaining digit returns an actual translation whose
unconditional increment in the selected placement meets the original
conditional bound. -/
theorem refineDigits_complete {B : Type*} [Fintype B] (q d k : ℕ)
    (prior candidate : B → (Fin q → Deck (d+k)) → ℚ) (mean : B → ℚ)
    (start : Fin q → Deck d) :
    ∃ v, refineDigits q d (d+k) prior candidate mean start k le_rfl = some v ∧
      CoverDeck.increment prior candidate mean v ≤
      CoverDeck.residueMean (productReduction q (show d ≤ d+k by omega))
        (CoverDeck.increment prior candidate mean) start := by
  obtain ⟨v,hv,h⟩ := resolve_mean q d (d+k) prior candidate mean start k le_rfl
  exact ⟨v,hv,by rwa [self_mean] at h⟩

/-- The level-one starting residue is unique, so the fully resolved translation
meets the expectation over all product deck translations. -/
theorem refineDigits_uniform {B : Type*} [Fintype B] (q k : ℕ)
    (prior candidate : B → (Fin q → Deck (1+k)) → ℚ) (mean : B → ℚ) :
    ∃ v, refineDigits q 1 (1+k) prior candidate mean 1 k le_rfl = some v ∧
      CoverDeck.increment prior candidate mean v ≤
        (∑ h, CoverDeck.increment prior candidate mean h) / Fintype.card (Fin q → Deck (1+k)) := by
  have hroot (v : Deck 1) : v = 1 := by
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective _ v
    exact (QuotientGroup.eq_one_iff _).mpr g.property
  have hπ (h : Fin q → Deck (1+k)) : productReduction q (show 1 ≤ 1+k by omega) h = 1 :=
    funext fun i => hroot _
  obtain ⟨v,hv,h⟩ := refineDigits_complete q 1 k prior candidate mean 1
  exact ⟨v,hv,by simpa [CoverDeck.residueMean,CoverDeck.histogram,CoverDeck.fiber,hπ] using h⟩

end Cover

end BorderVNP
end Computability
end OAI
