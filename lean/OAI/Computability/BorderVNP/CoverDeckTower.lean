import OAI.Computability.BorderVNP.CoverDeckAddress
import OAI.Computability.BorderVNP.CoverDeckSelection

/-!
# Deck residues in the product cover

This specializes the finite-group histogram and deterministic-choice
calculation to the actual quaternion congruence quotients. In the stable
range, one product-tile residue has exactly `7^(3*q)` children.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

/-- The deck group is finite by its faithful four-coordinate representation. -/
noncomputable instance deckFintype (l : ℕ) : Fintype (Deck l) := by
  let e := QuaternionAlgebra.equivProd (2 : ZMod (7^l)) 0 3
  let f (x : Deck l) := e (deckAddress l x).val
  have hi : Function.Injective f :=
    e.injective.comp (Units.val_injective.comp (deckAddress_injective l))
  let := Finite.of_injective f hi
  exact Fintype.ofFinite _

/-- Equality of product residue labels is decidable. -/
noncomputable instance deckDecidableEq (l : ℕ) : DecidableEq (Deck l) := Classical.decEq _

private theorem gamma_antitone {d l : ℕ} (h : d ≤ l) : gamma l ≤ gamma d := by
  induction l, h using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih => exact (gamma_next l).trans ih

/-- Reduction of a tile address to a shallower congruence cover. -/
def deckReduction {d l : ℕ} (h : d ≤ l) : Deck l →* Deck d :=
  QuotientGroup.map _ _ (MonoidHom.id _) (fun _ hx => gamma_antitone h hx)

/-- Every shallower tile has a lift to the deeper cover. -/
theorem deckReduction_surjective {d l : ℕ} (h : d ≤ l) :
    Function.Surjective (deckReduction h) :=
  QuotientGroup.map_surjective_of_surjective _ _ _ QuotientGroup.mk_surjective _

/-- Simultaneous reduction in all surface factors of the product host. -/
def productReduction (q : ℕ) {d l : ℕ} (h : d ≤ l) :
    (Fin q → Deck l) →* (Fin q → Deck d) :=
  MonoidHom.piMap (fun _ => deckReduction h)

/-- All product-tile residues lift independently in every factor. -/
theorem productReduction_surjective (q : ℕ) {d l : ℕ} (h : d ≤ l) :
    Function.Surjective (productReduction q h) :=
  Function.Surjective.piMap (fun _ => deckReduction_surjective h)

/-- The manuscript's conditional deck-translation identity for its actual
product cover, including its kernel-order denominator. -/
theorem deck_residue_correlation (q : ℕ) {d l : ℕ} (h : d ≤ l)
    (a b : (Fin q → Deck l) → ℚ) (c : Fin q → Deck d) :
    let π := productReduction q h
    CoverDeck.residueMean π (fun t => ∑ x, a (t*x)*b x) c =
      (∑ v, CoverDeck.histogram π a (c*v)*CoverDeck.histogram π b v) /
        (CoverDeck.fiber π 1).card :=
  CoverDeck.residueMean_correlation _ (productReduction_surjective q h) a b c

private theorem reduction_comp (q : ℕ) {e d l : ℕ} (he : e ≤ d) (hd : d ≤ l) :
    (productReduction q he) ∘ (productReduction q hd) = productReduction q (he.trans hd) := by
  funext x i
  change deckReduction he (deckReduction hd (x i)) = deckReduction (he.trans hd) (x i)
  obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective ((gamma l).subgroupOf (gamma 1)) (x i)
  rw [← ha]
  rfl

/-- The deterministic digit decision on p. 21 for the product tower: choosing
the first minimizing child in a supplied address ordering keeps the parent's
conditional expectation bound. -/
theorem choose_product_digit {B : Type*} [Fintype B] (q d l : ℕ) (hd : d+1 ≤ l)
    (prior candidate : B → (Fin q → Deck l) → ℚ) (mean : B → ℚ)
    (c : Fin q → Deck d) (children : List (Fin q → Deck (d+1)))
    (hchildren : ∀ v, v ∈ children ↔ productReduction q (Nat.le_succ d) v = c) :
    let π := productReduction q hd
    ∃ v, CoverDeck.chooseResidue (CoverDeck.conditionalScore π prior candidate mean) children =
        some v ∧ productReduction q (Nat.le_succ d) v = c ∧
      CoverDeck.residueMean π (CoverDeck.increment prior candidate mean) v ≤
        CoverDeck.residueMean (productReduction q ((Nat.le_succ d).trans hd))
          (CoverDeck.increment prior candidate mean) c := by
  have h := CoverDeck.chooseResidue_le_parent (productReduction q hd)
    (productReduction_surjective q hd) (productReduction q (Nat.le_succ d))
    (productReduction_surjective q (Nat.le_succ d)) prior candidate mean c children hchildren
  rwa [reduction_comp] at h

/-- From depth two onwards, every product residue has exactly the fixed
number of children stated in Lemma 5.3. -/
theorem product_children_card (q d : ℕ) (c : Fin q → Deck (d+2)) :
    (CoverDeck.fiber (productReduction q (show d+2 ≤ d+3 by omega)) c).card = 7^(3*q) := by
  let π := productReduction q (show d+2 ≤ d+3 by omega)
  have hs := productReduction_surjective q (show d+2 ≤ d+3 by omega)
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := π) (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  change Finset.univ.card = ∑ v, (CoverDeck.fiber π v).card at hsum
  simp_rw [CoverDeck.fiber_card_eq_kernel π hs] at hsum
  simp only [Finset.card_univ,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Fintype.card_fun,
    Fintype.card_fin,← Nat.card_eq_fintype_card (α := Deck _),deck_card] at hsum
  have hg : tileCount (d+3) = (7^3)*tileCount (d+2) := by
    rw [tileCount_eq (d+1),tileCount_eq d,pow_succ]; ring
  rw [hg,mul_pow,← pow_mul] at hsum
  rw [CoverDeck.fiber_card_eq_kernel π hs c]
  have hp : 0 < tileCount (d+2)^q := by
    rw [tileCount_eq]; exact pow_pos (Nat.mul_pos (by positivity) tileCount_two_bounds.1) _
  exact Nat.mul_right_cancel hp ((mul_comm _ _).trans hsum.symm)

end Cover

end BorderVNP
end Computability
end OAI
