import OAI.Computability.BorderVNP.ShortenBundleCost
import OAI.Computability.BorderVNP.ShortenAddressReplacement

/-!
# Charged length of a simultaneous profile replacement

The joint profile retains the unselected part of the exterior once. Its
other cables partition into hooks and internal profile cables at the
individual seed addresses, including their selector wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Epoch
open scoped BigOperators Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
variable {A : Type} [Fintype A] {H : Type*} [PseudoMetricSpace H] (t : AddressPartition N A)
variable (place : N.Site → H)
variable (G : ∀ a, Network D (N.CutPorts (t.part a)) (N.cutWidths (t.part a)))
variable (sites : ∀ a, (G a).Site → H)

/-- Independent seed networks keep their own site placements. -/
def AddressPartition.parallelSites : (t.parallel G).Site → H :=
  fun v => sites v.1 v.2

/-- The selected old length is the sum over seeds. -/
theorem AddressPartition.selectedLength_sum :
    selectedLength N place t.selected = ∑ a, selectedLength N place (t.part a) := by
  let f := fun c : ↥t.selected => (N.width c.val : ℝ) * dist (place (N.src c.val)) (place (N.dst c.val))
  exact (t.edgeIndex.sum_comp f).symm.trans (Fintype.sum_sigma _)

/-- Internal charged cost of the joint profile is the sum over seed gadgets. -/
theorem AddressPartition.placedCost_parallel :
    placedCost (t.parallel G) (t.parallelSites G sites) = ∑ a, placedCost (G a) (sites a) :=
  Fintype.sum_sigma _

/-- Each endpoint hook belongs to the unique seed that selected its interval. -/
theorem AddressPartition.hookCost_parallel :
    hookCost (t.parallel G) (t.parallelSites G sites) (oldEndpoint N t.selected place) =
      ∑ a, hookCost (G a) (sites a) (oldEndpoint N (t.part a) place) := by
  let f := fun q : N.CutPorts t.selected => (N.cutWidths t.selected q : ℝ) *
    dist (oldEndpoint N t.selected place q) (t.parallelSites G sites ((t.parallel G).attach q))
  refine (t.portIndex.sum_comp f).symm.trans ((Fintype.sum_sigma _).trans ?_)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro q _
  change f (t.includePort a q) = _
  dsimp only [f]
  rw [t.attach_include G a q]
  cases q <;> rfl

/-- One profile's actual charged output: it loses all matched old wires and
pays for all hooks and profile interiors. -/
theorem AddressPartition.chargedLength_parallel (charged : N.Edge → Bool)
    (hc : ∀ a c, c ∈ t.part a → charged c = true) :
    chargedLength ((N.cut t.selected).sew (t.parallel G))
        (Sum.elim place (t.parallelSites G sites)) (profileCharges N t.selected _ charged) =
      chargedLength N place charged - (∑ a, selectedLength N place (t.part a)) +
        ∑ a, (placedCost (G a) (sites a) + hookCost (G a) (sites a) (oldEndpoint N (t.part a) place)) := by
  have hall (c : N.Edge) (hc' : c ∈ t.selected) : charged c = true := by
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hc'
    exact hc a c ha
  rw [chargedLength_replace N place charged t.selected hall, t.selectedLength_sum place,
    t.placedCost_parallel, t.hookCost_parallel, Finset.sum_add_distrib]

/-- Geometric data selected by the motion and bin at a single seed. -/
structure SeedChart (I : Type*) [Fintype I] (D : ℕ) where
  /-- Half the common length of matched segments. -/
  radius : ℝ
  /-- Directions of the representative orthogonal crossing. -/
  axes : EuclideanSpace ℝ (Fin D) →ₗᵢ[ℝ] PiLp 2 (fun _ : I => ℂ)
  /-- Representative center in the lifted host. -/
  center : HyperbolicHost I

variable {I : Type*} [Fintype I]

/-- Actual host position of an inserted site. -/
noncomputable def SeedChart.atSite (c : SeedChart I D) (z : EuclideanSpace ℝ (Fin D)) :=
  shiftTo c.center (productChart (c.radius • c.axes z))

/-- Canonical endpoint toward which an old slot is hooked. -/
noncomputable def SeedChart.atTerminal (c : SeedChart I D) (q : Fin D × Bool) :=
  shiftTo c.center (productLine (c.axes (antipodalPosition q)) c.radius)

variable {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m) (j : A → ℕ)
variable (p : Pack D P bits K) (u : AddressPartition p.layout A)
variable (b : ∀ a, Bundle p.layout (u.part a) (j a * m))

/-- Total charged length of the actual network for a joint histogram tuple. -/
noncomputable def combinedLength (oldSites : p.layout.Site → HyperbolicHost I)
    (charged : p.layout.Edge → Bool) (charts : A → SeedChart I D) (q : ProfileCounts e j) : ℝ :=
  let nets := seedNetwork e j u b q
  let host := fun a v => (charts a).atSite ((nets a).position v)
  chargedLength ((p.layout.cut u.selected).sew (u.parallel nets))
    (Sum.elim oldSites (u.parallelSites nets host)) (profileCharges p.layout u.selected _ charged)

/-- For every simultaneous profile, the sewn pack saves a fixed fraction
of the sum of the actually matched old lengths. The constants precede
the pack, seed addresses, subdivisions, and public counts. -/
theorem combinedLength_saving (hD : 0 < D) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ {P : Type*} {bits : P → ℕ}
      (p : Pack D P bits K) {A : Type} [Fintype A] (u : AddressPartition p.layout A)
      (j : A → ℕ) (b : ∀ a, Bundle p.layout (u.part a) (j a * m))
      (oldSites : p.layout.Site → HyperbolicHost I) (charged : p.layout.Edge → Bool)
      (charts : A → SeedChart I D),
      (∀ a, (charts a).radius ∈ Set.Icc (0 : ℝ) h) →
      (∀ a c, c ∈ u.part a → charged c = true) →
      (∀ a (c : ↥(u.part a)), dist (oldSites (p.layout.src c.val)) (oldSites (p.layout.dst c.val)) =
        2*(charts a).radius) →
      (∀ a (q : p.layout.CutPorts (u.part a)), dist (oldEndpoint p.layout (u.part a) oldSites q)
        ((charts a).atTerminal ((b a).terminal q)) ≤ ν/4*(charts a).radius) →
      ∀ q : ProfileCounts e j, combinedLength e j p u b oldSites charged charts q ≤
        chargedLength p.layout oldSites charged - (ν/2) * ∑ a, selectedLength p.layout oldSites (u.part a) := by
  obtain ⟨ν, hν, h, hh, save⟩ := Bundle.paid_host_saving (I := I) e hD hm
  refine ⟨ν,hν,h,hh,?_⟩
  intro P bits p A _ u j b oldSites charged charts hr hc hl hn q
  let nets := seedNetwork e j u b q
  let sites := fun a v => (charts a).atSite ((nets a).position v)
  have hlocal (a : A) : placedCost (nets a) (sites a) +
      hookCost (nets a) (sites a) (oldEndpoint p.layout (u.part a) oldSites) ≤
      selectedLength p.layout oldSites (u.part a) - ν/2 * selectedLength p.layout oldSites (u.part a) := by
    have h' := save (charts a).radius (hr a) p.layout oldSites charged (u.part a) (hc a)
      (j a) (b a) (q a).val (profileCounts_total e j q a) (charts a).axes (charts a).center (hl a) (hn a)
    have hx := chargedLength_replace p.layout oldSites charged (u.part a) (hc a) (nets a) (sites a)
    change chargedLength ((p.layout.cut (u.part a)).sew (nets a)) (Sum.elim oldSites (sites a))
      (profileCharges p.layout (u.part a) (nets a) charged) ≤ _ at h'
    linarith only [hx, h']
  unfold combinedLength
  rw [u.chargedLength_parallel oldSites nets sites charged hc]
  have ht := Finset.sum_le_sum (s := Finset.univ) fun a _ => hlocal a
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at ht
  linarith only [ht]

end Shortening

end BorderVNP
end Computability
end OAI
