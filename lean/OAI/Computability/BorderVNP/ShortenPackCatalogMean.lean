import OAI.Computability.BorderVNP.ShortenPackHeckeLaw

/-!
# Half-mean coverage from a finite catalog of segment types

The type tag records the length and ordered speed tuple; direction bins may
have different cardinalities for different types. The averaging length is
chosen for the whole finite catalog before the cover level, the input
networks, their widths and all carried deck addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PackMotions

open Crossing Epoch Cover Cover.Frame Hecke MeasureTheory Set Filter Packing
open scoped Classical BigOperators Topology

universe u v

variable {D : ℕ} [NeZero D] {I T : Type} [Fintype I] [Fintype T]
variable {B : T → Type} [∀ t, Fintype (B t)]
variable (speed : T → I → ℝ) (radiusLength : T → ℝ)
variable (code : ∀ t, HyperbolicHost I × PiLp 2 (fun _ : I => ℂ) → B t)
variable (perm : ∀ t, Fin D → Equiv.Perm (B t))

/-- Public relative address includes the old segment's geometric type. -/
def catalogCode (t : T) (x : HyperbolicHost I × PiLp 2 (fun _ : I => ℂ)) : Σ t, B t :=
  ⟨t, code t x⟩

/-- The crossing-direction permutation retains both the destination tile and the length tag. -/
def catalogPerm (depth : ℕ) (j : Fin D) : Equiv.Perm ((I → Deck depth) × (Σ t, B t)) :=
  (Equiv.refl _).prodCongr (Equiv.sigmaCongrRight fun t => perm t j)

/-- Length field in the tagged public address. -/
def catalogLength (depth : ℕ) (a : (I → Deck depth) × (Σ t, B t)) : ℝ := radiusLength a.2.1

omit [Fintype I] [Fintype T] [∀ t, Fintype (B t)] in
private theorem tagged_preimage (t : T) (b : B t) :
    catalogCode code t ⁻¹' {⟨t,b⟩} = code t ⁻¹' {b} := by
  ext x
  simp [catalogCode]

omit [Fintype I] [Fintype T] [∀ t, Fintype (B t)] in
private theorem tagged_empty {t t' : T} (h : t ≠ t') (b : B t') :
    catalogCode code t ⁻¹' {⟨t',b⟩} = ∅ := by
  ext x
  simp [catalogCode, Sigma.ext_iff, h]

/-- For every sufficiently long common Hecke averaging table, at every output depth and for
every finite collection of physically placed packs, the actual bin mean matches at least half
the normalized charged length. This uses the geometric finite-motion estimate itself, with
no aggregate mean or single-wire variation assumption on the input packs. -/
theorem eventually_catalog_half
    (hB : ∀ t b, MeasurableSet (code t ⁻¹' {b}))
    (hn : ∀ t b, ((productPositions I).prod (idealDirectionLaw (speed t)))
      (frontier (code t ⁻¹' {b})) = 0)
    (hperm : ∀ t j b, ((productPositions I).prod (idealDirectionLaw (speed t)))
      (code t ⁻¹' {perm t j b}) = ((productPositions I).prod (idealDirectionLaw (speed t))) (code t ⁻¹' {b}))
    (hpos : ∀ t, 0 ≤ radiusLength t) :
    ∀ᶠ n in atTop, ∀ {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type u}
      (input : Fin copies → Pack D P bits K) (charged : ∀ i, (input i).layout.Edge → Bool)
      (kind : Active input charged → T) (depth : ℕ)
      (frame : Active input charged → Equiv.Perm I → I → SL)
      (carry : Active input charged → Equiv.Perm I → ProductSample (lattice 1) elliptic I n → I → Deck depth)
      {Q : Type v} [PseudoMetricSpace Q]
      (place : ∀ i, PackSample (lattice 1) elliptic I depth n → (input i).layout.Site → Q)
      (ω : Fin copies → PackSample (lattice 1) elliptic I depth n),
      (∀ (w : Active input charged) s,
        dist (place w.1 s ((input w.1).layout.src w.2.val)) (place w.1 s ((input w.1).layout.dst w.2.val)) =
          radiusLength (kind w)) →
      let mb := sampledBin input charged (speed ∘ kind) (catalogCode code ∘ kind) frame carry
      (chargedLength (parallelPacks input).layout (fun v => place v.1 (ω v.1) v.2)
        (fun c => (jointBin input mb ω c).isSome) / copies) / 2 ≤
        matchedLength (catalogPerm (I := I) perm depth) (catalogLength radiusLength depth)
          (binMean input mb (sampleProb depth n)) := by
  let μ (t : T) := (productPositions I).prod (idealDirectionLaw (speed t))
  have hmeas (t : T) (b : Σ t, B t) : MeasurableSet (catalogCode code t ⁻¹' {b}) := by
    rcases b with ⟨u,b⟩
    by_cases h : t = u
    · subst u; rw [tagged_preimage]; exact hB t b
    · rw [tagged_empty code h b]; exact MeasurableSet.empty
  have hnull (t : T) (b : Σ t, B t) : μ t (frontier (catalogCode code t ⁻¹' {b})) = 0 := by
    rcases b with ⟨u,b⟩
    by_cases h : t = u
    · subst u; rw [tagged_preimage]; exact hn t b
    · rw [tagged_empty code h b, frontier_empty, measure_empty]
  have h := pack_bin_variation D (NeZero.pos D) speed (catalogCode code) hmeas hnull
  filter_upwards [h] with n hmix copies P bits K input charged kind depth frame carry Q inst place ω hmove
  let mb := sampledBin input charged (speed ∘ kind) (catalogCode code ∘ kind) frame carry
  let : ∀ w : Active input charged, IsProbabilityMeasure ((μ ∘ kind) w) := fun _ => by
    dsimp [μ]; infer_instance
  apply half_binMean_of_measure input charged mb (sampleProb depth n) place ω (catalogPerm perm depth)
    (catalogLength radiusLength depth) (radiusLength ∘ kind) (μ ∘ kind) (catalogCode code ∘ kind)
    (sampledBin_mask _ _ _ _ _ _) hmove (fun a => hpos a.2.1) (fun _ _ => rfl) _
    (fun w b => hmeas (kind w) b) (fun _ _ _ => rfl) _ _
  · intro w s a ha
    have he : sampleAddress input charged (speed ∘ kind) (catalogCode code ∘ kind) frame carry w s = a := by
      simpa [mb,sampledBin,w.2.property] using ha
    subst a
    rfl
  · rintro w j ⟨tile, u, b⟩
    change μ (kind w) (catalogCode code (kind w) ⁻¹' {⟨u,perm u j b⟩}) =
      μ (kind w) (catalogCode code (kind w) ⁻¹' {⟨u,b⟩})
    by_cases he : kind w = u
    · subst u; rw [tagged_preimage, tagged_preimage]; exact hperm _ j b
    · rw [tagged_empty code he, tagged_empty code he]
  · intro w
    dsimp only [mb]
    simp_rw [finiteWireLaw_eq_actualBinMass]
    exact hmix (kind w) depth (frame w) (carry w)

end Shortening.PackMotions

end BorderVNP
end Computability
end OAI
