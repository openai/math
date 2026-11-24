import OAI.Computability.VPVNP.SpectralRelabel
import OAI.Computability.VPVNP.SubpartyNormalization
import OAI.Computability.VPVNP.SpectralRealizable
import OAI.Computability.VPVNP.ConfigurationLimits
import Mathlib.Logic.Equiv.Set

/-! # Closure of finite wire configurations under coordinatewise limits

Any assignment of the finite label set to ambient parties factors through a
surjection onto a numbered set of used parties. Their numbering may vary, but
there are only finitely many possible numbers and maps. Separating the used
parties from their complement allows the spectrum to be normalized on them.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

open Filter Set
open scoped Topology

private abbrev PartyPattern (ι : Type*) [Fintype ι] :=
  (n : Fin (Fintype.card ι + 1)) × {f : ι → Fin n.val // Function.Surjective f}

private theorem exists_party_pattern {ι J : Type*} [Fintype ι] (f : ι → J) :
    ∃ p : PartyPattern ι, ∃ e : (Fin p.1.val ⊕ ((Set.range f)ᶜ : Set J)) ≃ J,
      ∀ i, e (.inl (p.2.1 i)) = f i := by
  classical
  let used := Set.range f
  let : Fintype used := Fintype.ofFinite used
  let e := Fintype.equivFin used
  let g := e ∘ Set.rangeFactorization f
  have hg : Function.Surjective g := e.surjective.comp Set.rangeFactorization_surjective
  have hcard : Fintype.card used ≤ Fintype.card ι :=
    Fintype.card_le_of_surjective (Set.rangeFactorization f) Set.rangeFactorization_surjective
  refine ⟨⟨⟨Fintype.card used, by omega⟩, g, hg⟩,
    (Equiv.sumCongr e.symm (Equiv.refl _)).trans (Equiv.Set.sumCompl used), ?_⟩
  intro i
  simp [g, used]

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι]

private theorem normalize_realization {d : ι → ι → ℝ} (w : WireRealization k d)
    {a b : ι} (hab : d a b ≠ 0) :
    ∃ p : PartyPattern ι, SpectralPoint.Realizes k p.2.1 (fun i ↦ d i.1 i.2) := by
  classical
  obtain ⟨p, e, he⟩ := exists_party_pattern w.label
  have : Nonempty (Fin p.1.val) := ⟨p.2.1 a⟩
  let : Fintype ((range w.label)ᶜ : Set w.Parties) := Fintype.ofFinite _
  let H := w.spectrum.relabel e
  have hwire (i j : ι) : H.wireDistance (.inl (p.2.1 i)) (.inl (p.2.1 j)) =
      w.spectrum.wireDistance (w.label i) (w.label j) := by
    rw [show H = w.spectrum.relabel e from rfl, w.spectrum.wireDistance_relabel, he, he]
  have hpos : 0 < H.subpartyExponent := by
    have hw : 0 < w.spectrum.wireDistance (w.label a) (w.label b) := by
      refine lt_of_le_of_ne (w.spectrum.wireDistance_nonneg _ _) ?_
      intro hz
      exact hab (by rw [w.distances, ← hz, mul_zero])
    rw [← hwire] at hw
    exact hw.trans_le (H.wireDistance_le_subpartyExponent _ _)
  refine ⟨p, H.subpartyNormalization hpos, w.scale * H.subpartyExponent,
    mul_pos w.scale_pos hpos, ?_⟩
  rintro ⟨i, j⟩
  dsimp only
  rw [H.subpartyNormalization_wireDistance hpos, hwire, w.distances]
  field_simp [hpos.ne']

omit [Fintype ι] in
/-- Lemma 2.3. A coordinatewise limit of realizable wire configurations on a
fixed finite label set is realizable at a common positive scale. -/
theorem RealizableUpToScale.limit [Finite ι] {d : ι → ι → ℝ} (seq : ℕ → ι → ι → ℝ)
    (hseq : ∀ m, RealizableUpToScale k (seq m))
    (hlim : ∀ i j, Tendsto (fun m ↦ seq m i j) atTop (𝓝 (d i j))) : RealizableUpToScale k d := by
  classical
  let := Fintype.ofFinite ι
  by_cases hzero : ∀ i j, d i j = 0
  · obtain ⟨w⟩ := hseq 0
    let center : w.Parties := Classical.ofNonempty
    exact ⟨{
      Parties := w.Parties
      spectrum := w.spectrum
      label := fun _ ↦ center
      scale := 1
      scale_pos := zero_lt_one
      distances := fun i j ↦ by rw [hzero, w.spectrum.wireDistance_self, mul_zero] }⟩
  obtain ⟨a, ha⟩ := not_forall.mp hzero
  obtain ⟨b, hab⟩ := not_forall.mp ha
  have : Nonempty ι := ⟨a⟩
  have hd : (fun i : ι × ι ↦ d i.1 i.2) ≠ 0 := fun h ↦ hab (congrFun h (a, b))
  have hpatterns : ∃ᶠ m in atTop, ∃ p : PartyPattern ι,
      SpectralPoint.Realizes k p.2.1 (fun i ↦ seq m i.1 i.2) := by
    apply ((hlim a b).eventually_ne hab).frequently.mono
    intro m hm
    obtain ⟨w⟩ := hseq m
    exact normalize_realization w hm
  obtain ⟨p, G, t, ht, heq⟩ := SpectralPoint.realizes_limit_of_finite_patterns
    (fun p : PartyPattern ι ↦ Fin p.1.val) (fun p ↦ p.2.1) (fun p ↦ p.2.2)
    hd (fun m i ↦ seq m i.1 i.2) hpatterns (fun i ↦ hlim i.1 i.2)
  have : Nonempty (Fin p.1.val) := ⟨p.2.1 a⟩
  have : Nontrivial (Fin p.1.val) := G.nontrivial_parties
  exact ⟨{
    Parties := Fin p.1.val
    spectrum := G
    label := p.2.1
    scale := t
    scale_pos := ht
    distances := fun i j ↦ (heq (i, j)).symm }⟩

end WireTensor

end VPVNP
end Computability
end OAI
