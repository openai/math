import OAI.Computability.BorderVNP.CoverDeckPackConcentration
import OAI.Computability.BorderVNP.ShortenCubeEnumeration
import OAI.Computability.BorderVNP.ShortenPreparedDeckTransport

/-! # Equation (6.2) for the compiled choices of actual geometric pack samples -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Cover Cover.Frame Cover.AddressCircuit Hecke Crossing Epoch Packing PackMotions PackedDeckEnergy
open scoped Classical BorderVNP.Epoch.Cube

variable {D q n m : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    (index : Fin m ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)

private theorem named_energy {l : ℕ} (F : (Cube D → Deck l) × B.Bin → ℝ) :
    binEnergy (fun a : (Fin q → Deck l) × B.Bin => F (a.1 ∘ enum.symm,a.2)) = binEnergy F :=
  Equiv.sum_comp ((enum.arrowCongr (Equiv.refl (Deck l))).prodCongr (Equiv.refl B.Bin)) (fun a => (F a)^2)

include enum in
private theorem card_names (l : ℕ) :
    Fintype.card (Fin q → Deck l) = Fintype.card (Cube D → Deck l) :=
  Fintype.card_congr (enum.arrowCongr (Equiv.refl (Deck l)))

/-- The finite candidate probabilities of the actual uniform speed permutation
and independent Hecke words, in the order of the physical count banks. -/
noncomputable def indexedProbability (j : Fin m) : ℚ :=
  PackedDeckMean.motionProbability (lattice 1) elliptic (index j)

/-- Normalized deviation at the physical names equals the deviation at the
canonical bit-key names, for the same choices and the true pack sample law. -/
theorem sampled_deviation_eq {copies l : ℕ} {P : Type} {bits : P → ℕ} {K : Type*}
    (input : Fin copies → Pack D P bits K) (active : ∀ i, (input i).layout.Edge → Bool)
    (kind : Active input active → B.types) (lift : Active input active → Cube D → gamma 1)
    (choice : Fin copies → Fin m) (deck : Fin copies → Fin q → Deck l) :
    let C := B.deckCounts input active kind lift enum index
    let tags := B.tag (d := l) (n := n) input active kind lift
    let ω := fun i => deckSample enum index (choice i,deck i)
    binEnergy (fun a => SeedIntervals.count (parallelPacks input).layout (jointBin input tags ω) a / copies -
      binMean input tags (sampleProb l n) a) =
    binEnergy (fun a : (Fin q → Deck l) × B.Bin => (∑ i, moved C i (choice i,deck i) a)/copies -
      (∑ i, motionMean (motionWeight (fun _ => indexedProbability index)) (moved C) i a)/copies) := by
  dsimp only
  rw [← named_energy B enum]
  apply congrArg binEnergy
  funext a
  rw [B.joint_deck_count input active kind lift enum index choice deck a.1 a.2,
    B.deck_binMean input active kind lift enum index a.1 a.2,Nat.cast_sum]
  rfl

/-- A fixed circuit family reads the actual unshifted candidate histograms
and selects forward geometric samples. Its choices achieve (6.2) for the
joint physical bins, at the same level-independent gate constants as the
deck computation. -/
theorem compiledSample_frames :
    ∃ P Dg p : ℕ, 0 < P ∧ ∀ copies l w : ℕ, 0 < copies → 1 ≤ l → P < 2^w →
      ∃ f : VPVNP.VerifierNetwork.Frame (PackTables B.Bin q l m w copies) (PackTracePins B.Bin q l m w copies),
        f.size ≤ 1+copies*(Fintype.card (Cube D → Deck l)*Dg*(l+w+1)^p) ∧
        ∀ {Port : Type} {bits : Port → ℕ} {K : Type*} (input : Fin copies → Pack D Port bits K)
          (active : ∀ i, (input i).layout.Edge → Bool) (kind : Active input active → B.types)
          (lift : Active input active → Cube D → gamma 1) (z : PackTables B.Bin q l m w copies → Bool)
          (H : ℕ), tableCount z = B.deckCounts input active kind lift enum index →
          (∀ i j b g, B.deckCounts (d := l) input active kind lift enum index i j b g ≤ H) →
          packRunWidth (Fintype.card (Cube D → Deck l)) P copies H ≤ w →
          ∃ (choice : Fin copies → Fin m) (deck : Fin copies → Fin q → Deck l),
            let tags := B.tag (d := l) (n := n) input active kind lift
            let ω := fun i => deckSample enum index (choice i,deck i)
            (∀ i j, f.eval z (.inr (i,.inl j)) = true ↔ j = choice i) ∧
            (∀ i b, f.eval z (.inr (i,.inr b)) = keyWord q l (deck i) b) ∧
            (∀ b g, ParseBatchSort.value (fun s => f.eval z (.inl (.inl (b,g,s)))) =
              SeedIntervals.count (parallelPacks input).layout (jointBin input tags ω) (g ∘ enum.symm,b)) ∧
            ∀ R : ℝ, 0 ≤ R →
              (∀ i j, (Fintype.card (Cube D → Deck l) : ℝ) * binEnergy (fun a =>
                (SeedIntervals.count (input i).layout (tags i ((index j).1,(index j).2,1)) a : ℝ)) ≤ R^2) →
              Real.sqrt (Fintype.card (Cube D → Deck l)) * Real.sqrt (binEnergy fun a =>
                SeedIntervals.count (parallelPacks input).layout (jointBin input tags ω) a / copies -
                binMean input tags (sampleProb l n) a) ≤ R / Real.sqrt copies := by
  let prob := indexedProbability index
  have hp (j) : 0 ≤ prob j := (PackedDeckMean.motionProbability_pos _ _ (index j)).le
  have hs : ∑ j, prob j = 1 := by
    obtain ⟨den,weights,hd,hs,_,he,_⟩ := PackedDeckMean.quaternion_candidate_numerators index
    have each (j : Fin m) : prob j = (weights j : ℚ)/den := he j
    simp_rw [each]
    rw [← Finset.sum_div,← Nat.cast_sum,hs,div_self (Nat.cast_ne_zero.mpr hd.ne')]
  obtain ⟨P,Dg,p,hP,make⟩ := packConcentration_frames B.Bin q m prob hp hs
  refine ⟨P,Dg,p,hP,?_⟩
  intro copies l w hk hl hw
  obtain ⟨f,hf,hout⟩ := make copies l w hk hl hw
  have hcard := card_names enum l
  refine ⟨f,by rwa [← hcard],?_⟩
  intro Port bits K input active kind lift z H hz hcounts hwidth
  obtain ⟨choice,deck,flags,keys,counts,_,bound⟩ := hout z H (by rwa [hz]) (by rwa [hcard])
  refine ⟨choice,deck,flags,keys,?_,?_⟩
  · intro b g
    rw [B.joint_deck_count input active kind lift enum index choice deck]
    simpa [hz] using counts b g
  · intro R hr hR
    have cap (i : Fin copies) (j : Fin m) : (Fintype.card (Fin q → Deck l) : ℝ) *
        binEnergy (fun a : (Fin q → Deck l) × B.Bin => (tableCount z i j a.2 a.1 : ℝ)) ≤ R^2 := by
      rw [hz,hcard]
      have hh := hR i j
      rw [← named_energy B enum] at hh
      exact hh
    have hbound := bound R hr cap
    rw [hz,hcard] at hbound
    rw [B.sampled_deviation_eq enum index input active kind lift choice deck]
    exact hbound

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
