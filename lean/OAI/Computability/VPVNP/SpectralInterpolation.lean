import OAI.Computability.VPVNP.SplitWireExtension
import OAI.Computability.VPVNP.PlacedTensorComposition
import OAI.Computability.VPVNP.CubeStar

/-!
# Adjoining finitely many interpolated parties to a spectral point

A finite interpolation tree describes a point in every CAT(0) realization
of a configuration. Each internal node can be adjoined by the fractional
extension of Theorem 2.4(1). Subsequent extensions preserve all old tensor
values and hence the already realized wire distances. This places the
centroids used for the balanced cuts in Section 4.3 simultaneously.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u
namespace WireTensor
open VPVNP.SpectralGeometry

variable {k : Type u} [Field k] {J : Type} [Fintype J]

/-- An enlarged finite spectral configuration with its old parties marked.
All placed old tensors keep their values. -/
structure ExtendedSpectrum (F : SpectralPoint k J) where
  /-- Finite party set of the enlarged spectral configuration. -/
  Parties : Type
  finiteParties : Fintype Parties
  /-- Spectral point on the enlarged party set whose values extend those of the original point. -/
  point : @SpectralPoint k Parties _ finiteParties
  /-- Embedding that marks the original parties inside the enlarged configuration. -/
  old : J ↪ Parties
  values : ∀ T : Tensor.{u,0,0} k J, point.value (placeTensor old T) = F.value T
  distances : ∀ a b, point.wireDistance (old a) (old b) = F.wireDistance a b

attribute [instance] ExtendedSpectrum.finiteParties

namespace ExtendedSpectrum

variable {F : SpectralPoint k J}

/-- Regard a spectral point as an extension of itself using the identity embedding on parties. -/
noncomputable def refl (F : SpectralPoint k J) : ExtendedSpectrum F where
  Parties := J
  finiteParties := inferInstance
  point := F
  old := Function.Embedding.refl _
  values T := (F.value_eq_of_mutual (placeTensor_id_mutual T)).symm
  distances _ _ := rfl

/-- Compose two successive extensions of a spectral point by composing the embeddings of their
marked parties. -/
noncomputable def trans (S : ExtendedSpectrum F) (U : ExtendedSpectrum S.point) :
    ExtendedSpectrum F where
  Parties := U.Parties
  finiteParties := U.finiteParties
  point := U.point
  old := S.old.trans U.old
  values T := ((U.point.value_eq_of_mutual (placeTensor_comp_mutual S.old U.old T)).symm.trans
    (U.values _)).trans (S.values _)
  distances a b := (U.distances _ _).trans (S.distances a b)

private noncomputable def addParty (H : SpectralPoint k (Option J))
    (extendsOld : ∀ T, H.value (embedOld T) = F.value T) : ExtendedSpectrum F where
  Parties := Option J
  finiteParties := inferInstance
  point := H
  old := Function.Embedding.some
  values T := (H.value_eq_of_mutual (placeTensor_some_mutual T)).symm.trans (extendsOld _)
  distances := F.wireDistance_extension H extendsOld

/-- The marked party realizes the prescribed tree in every CAT(0) metric
embedding of this finite configuration. -/
def RealizesTree {V : Type*} (S : ExtendedSpectrum F) (labels : V → J)
    (t : InterpolationTree V) (c : S.Parties) : Prop :=
  ∀ (X : Type) [MetricSpace X] (hc : HasCATZeroSegments X) (e : S.Parties → X),
    (∀ a b, dist (e a) (e b) = S.point.wireDistance a b) →
      e c = t.eval hc (e ∘ S.old ∘ labels)

/-- Once a tree is realized, it remains realized in each further extension. -/
theorem RealizesTree.trans {V : Type*} {S : ExtendedSpectrum F} {labels : V → J}
    {t : InterpolationTree V} {c : S.Parties} (h : S.RealizesTree labels t c)
    (U : ExtendedSpectrum S.point) : (S.trans U).RealizesTree labels t (U.old c) := by
  intro X _ hc e he
  exact h X hc (e ∘ U.old) (fun a b ↦ (he _ _).trans (U.distances a b))

end ExtendedSpectrum

namespace SpectralPoint

variable {V : Type*}

/-- A single finite interpolation prescription can be realized while preserving
every old tensor value. -/
theorem exists_tree_extension (F : SpectralPoint k J) (labels : V → J)
    (t : InterpolationTree V) :
    ∃ (S : ExtendedSpectrum F) (c : S.Parties), S.RealizesTree labels t c := by
  induction t generalizing J with
  | vertex v =>
    exact ⟨.refl F, labels v, fun _ _ _ _ _ ↦ rfl⟩
  | segment l r frac ihl ihr =>
    obtain ⟨S, a, ha⟩ := ihl F labels
    obtain ⟨U, b, hb⟩ := ihr S.point (S.old ∘ labels)
    obtain ⟨H, hH, hfrac⟩ := U.point.exists_fraction_extension (U.old a) b frac.property.1 frac.property.2
    let Z := ExtendedSpectrum.addParty H hH
    refine ⟨(S.trans U).trans Z, none, ?_⟩
    intro X _ hc e he
    have heH (i j : Option U.Parties) : dist (e i) (e j) = H.wireDistance i j := he i j
    have he' (i j : U.Parties) : dist (e (some i)) (e (some j)) = U.point.wireDistance i j :=
      (he _ _).trans (U.point.wireDistance_extension H hH i j)
    have hleft := (ha.trans U) X hc (e ∘ some) he'
    have hright := hb X hc (e ∘ some) he'
    let g (v : V) := e (some (U.old (S.old (labels v))))
    change e none = catPoint hc (l.eval hc g) (r.eval hc g) frac
    change e (some (U.old a)) = l.eval hc g at hleft
    change e (some b) = r.eval hc g at hright
    rw [← hleft, ← hright]
    apply catPoint_unique
    · rw [dist_comm, heH, heH]
      exact hfrac.1
    · rw [heH, heH]
      exact hfrac.2

/-- Realize all trees in a finite indexed family in one enlarged spectrum. -/
theorem exists_treeFamily_extension (F : SpectralPoint k J) (labels : V → J)
    {I : Type} [Fintype I] (trees : I → InterpolationTree V) :
    ∃ (S : ExtendedSpectrum F) (c : I → S.Parties), ∀ i, S.RealizesTree labels (trees i) (c i) := by
  have byFin : ∀ n : ℕ, ∀ {K : Type} [Fintype K] (G : SpectralPoint k K) (v : V → K)
      (ts : Fin n → InterpolationTree V), ∃ (S : ExtendedSpectrum G) (c : Fin n → S.Parties),
      ∀ i, S.RealizesTree v (ts i) (c i) := by
    intro n
    induction n with
    | zero =>
      intro K _ G _ _
      exact ⟨.refl G, Fin.elim0, fun i ↦ Fin.elim0 i⟩
    | succ n ih =>
      intro K _ G v ts
      obtain ⟨S, a, ha⟩ := G.exists_tree_extension v (ts 0)
      obtain ⟨U, c, hc⟩ := ih S.point (S.old ∘ v) (fun i ↦ ts i.succ)
      exact ⟨S.trans U, Fin.cases (U.old a) c, Fin.cases (ha.trans U) hc⟩
  let e := Fintype.equivFin I
  obtain ⟨S, c, hc⟩ := byFin (Fintype.card I) F labels (trees ∘ e.symm)
  exact ⟨S, c ∘ e, fun i ↦ by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hc (e i)⟩

/-- The centroids of all subsets of the marked basis corners are parties of
a single extension. Every isometric CAT(0) embedding locates those parties
at the prescribed points of the filled cube. -/
theorem exists_cubeCentroid_extension (F : SpectralPoint k J) {n : ℕ} (corner : Finset (Fin n) → J) :
    ∃ (S : ExtendedSpectrum F) (c : Finset (Fin n) → S.Parties),
      ∀ (X : Type) [MetricSpace X] (hc : HasCATZeroSegments X) (e : S.Parties → X),
        (∀ a b, dist (e a) (e b) = S.point.wireDistance a b) → ∀ s,
          e (c s) = filledSubsetCentroid hc (e ∘ S.old ∘ corner) s := by
  obtain ⟨S, c, hs⟩ := F.exists_treeFamily_extension corner
    (fun s ↦ cubeInterpolation (cubeCentroidCoordinates s))
  exact ⟨S, c, fun X _ hc e he s ↦ (hs s X hc e he).trans (cubeInterpolation_eval _ _ _)⟩

end SpectralPoint
end WireTensor

end VPVNP
end Computability
end OAI
