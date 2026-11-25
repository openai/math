import OAI.Computability.BorderVNP.ShortenAddressCost

/-!
# Combining seeds in the quotient host

The old sites live in the quotient. For each seed we lift its endpoint slots
in a common neighborhood of the canonical crossing. Separate slots at a single
old site may use different lifts. Projecting the inserted profile back to the
quotient does not increase any interior or hook distance.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch
open scoped BigOperators Classical

variable {I : Type*} [Fintype I] {Q : Type*} [PseudoMetricSpace Q]
variable {D : ℕ} {P : Type*} {bits : P → ℕ}

/-- A nonexpanding projection does not increase interior wire lengths. -/
theorem placedCost_project (G : Network D P bits) (sites : G.Site → HyperbolicHost I)
    (π : HyperbolicHost I → Q) (hπ : ∀ x y, dist (π x) (π y) ≤ dist x y) :
    placedCost G (π ∘ sites) ≤ placedCost G sites :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (hπ _ _) (Nat.cast_nonneg _)

/-- A separate lift of every old endpoint bounds the corresponding hook. -/
theorem hookCost_project [Fintype P] (G : Network D P bits) (sites : G.Site → HyperbolicHost I)
    (π : HyperbolicHost I → Q) (hπ : ∀ x y, dist (π x) (π y) ≤ dist x y)
    (old : P → Q) (lifts : P → HyperbolicHost I) (hl : ∀ i, π (lifts i) = old i) :
    hookCost G (π ∘ sites) old ≤ hookCost G sites lifts := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [← hl i]
  exact hπ _ _

variable {m : ℕ} {K : Type*} [Field K] {A : Type} [Fintype A]

/-- Actual charged length after projecting each seed's inserted sites into the quotient. -/
noncomputable def combinedQuotientLength (e : PaidIdentity K D m) (j : A → ℕ)
    (p : Pack D P bits K) (t : AddressPartition p.layout A)
    (b : ∀ a, Bundle p.layout (t.part a) (j a * m))
    (old : p.layout.Site → Q) (charged : p.layout.Edge → Bool)
    (π : A → HyperbolicHost I → Q) (charts : A → SeedChart I D) (q : ProfileCounts e j) : ℝ :=
  let nets := seedNetwork e j t b q
  let atSeed := fun a v => π a ((charts a).atSite ((nets a).position v))
  chargedLength ((p.layout.cut t.selected).sew (t.parallel nets))
    (Sum.elim old (t.parallelSites nets atSeed)) (profileCharges p.layout t.selected _ charged)

/-- All profiles save the same fraction of the matched length in the quotient.
The original segment lengths are measured there. The only lifts needed are
the individual hook endpoints for each seed. -/
theorem quotient_combining_saving (e : PaidIdentity K D m) (hD : 0 < D) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ {Q : Type*} [PseudoMetricSpace Q] {P : Type*} {bits : P → ℕ}
      (p : Pack D P bits K) {A : Type} [Fintype A] (t : AddressPartition p.layout A)
      (j : A → ℕ) (b : ∀ a, Bundle p.layout (t.part a) (j a*m))
      (old : p.layout.Site → Q) (charged : p.layout.Edge → Bool)
      (π : A → HyperbolicHost I → Q) (charts : A → SeedChart I D)
      (lifts : ∀ a, p.layout.CutPorts (t.part a) → HyperbolicHost I),
      (∀ a x y, dist (π a x) (π a y) ≤ dist x y) →
      (∀ a u, π a (lifts a u) = oldEndpoint p.layout (t.part a) old u) →
      (∀ a, (charts a).radius ∈ Set.Icc (0 : ℝ) h) →
      (∀ a c, c ∈ t.part a → charged c = true) →
      (∀ a (c : ↥(t.part a)), dist (old (p.layout.src c.val)) (old (p.layout.dst c.val)) =
        2*(charts a).radius) →
      (∀ a u, dist (lifts a u) ((charts a).atTerminal ((b a).terminal u)) ≤ ν/4*(charts a).radius) →
      ∀ q : ProfileCounts e j, combinedQuotientLength e j p t b old charged π charts q ≤
        chargedLength p.layout old charged - (ν/2) * ∑ a, selectedLength p.layout old (t.part a) := by
  obtain ⟨ν,hν,budget⟩ := e.profile_uniform_saving hD hm
  obtain ⟨h,hh,placeBound⟩ := place_profile_saving (I := I) hν
  refine ⟨ν,hν,h,hh,?_⟩
  intro Q _ P bits p A _ t j b old charged π charts lifts hπ hlift hr hc hlen hnear q
  let nets := seedNetwork e j t b q
  let up := fun a v => (charts a).atSite ((nets a).position v)
  let down := fun a => π a ∘ up a
  have hlocal (a : A) :
      placedCost (nets a) (down a) + hookCost (nets a) (down a) (oldEndpoint p.layout (t.part a) old) ≤
        (1-ν/2) * selectedLength p.layout old (t.part a) := by
    refine (add_le_add (placedCost_project _ _ (π a) (hπ a))
      (hookCost_project _ _ (π a) (hπ a) _ _ (hlift a))).trans ?_
    have hcost : (nets a).cost ≤ (1-ν) * ∑ u : p.layout.CutPorts (t.part a),
        (p.layout.cutWidths (t.part a) u : ℝ) := by
      rw [(b a).hookWidth, Nat.cast_mul]
      change (e.profile (j a) (q a).val).cost ≤ _
      convert budget (j a) (q a).val (profileCounts_total e j q a) using 1
      ring
    have hnear' (u : p.layout.CutPorts (t.part a)) : dist (lifts a u)
        (shiftTo (charts a).center (productLine ((charts a).axes ((nets a).position ((nets a).attach u)))
          (charts a).radius)) ≤ ν/4*(charts a).radius := by
      have hpos : (nets a).position ((nets a).attach u) = antipodalPosition ((b a).terminal u) :=
        e.profile_placedAt (j a) (q a).val ((b a).terminal u)
      rw [hpos]
      exact hnear a u
    have hx := placeBound (charts a).radius (hr a) (nets a) (charts a).axes (charts a).center
      (lifts a) hcost hnear'
    let V := ∑ u : p.layout.CutPorts (t.part a), (p.layout.cutWidths (t.part a) u : ℝ)
    have hraw : placedCost (nets a) (up a) + hookCost (nets a) (up a) (lifts a) ≤
        (1-ν/2) * (charts a).radius * V := hx
    rw [(b a).selectedLength_eq old (charts a).radius (hlen a)]
    exact hraw.trans_eq (mul_assoc _ _ _)
  change chargedLength ((p.layout.cut t.selected).sew (t.parallel nets))
    (Sum.elim old (t.parallelSites nets down)) (profileCharges p.layout t.selected _ charged) ≤ _
  apply (t.chargedLength_parallel old nets down charged hc).le.trans
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun a _ => hlocal a
  rw [← Finset.mul_sum] at hsum
  linarith only [hsum]

end Shortening

end BorderVNP
end Computability
end OAI
