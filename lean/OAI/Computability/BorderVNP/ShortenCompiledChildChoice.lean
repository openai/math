import OAI.Computability.BorderVNP.ShortenCompiledSampleChoice
import OAI.Computability.BorderVNP.ShortenEpochChoosePlaced
import OAI.Computability.BorderVNP.ShortenPlacedMeasurements

/-! # The compiled samples at the measured child midpoint radius -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PreparedBins

open Cover Cover.Frame Cover.AddressCircuit Hecke Crossing Epoch Packing PackMotions Framed
open scoped Classical BorderVNP.Epoch.Cube

variable {D q n m : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    (index : Fin m ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)

set_option maxHeartbeats 1400000 in
/-- The physical samples chosen on the trace wires satisfy the exact
deviation hypothesis of the measured shortening step. Their radius constant
is chosen before the depth, fan-in, count width, and children. -/
theorem compiledChildSample_frames :
    ∃ N P C e : ℕ, 0 < P ∧ ∀ d k w : ℕ, 0 < d → ∀ hk : 0 < k, P < 2^w →
      ∃ f : VPVNP.VerifierNetwork.Frame (PackTables B.Bin q (d+1) m w k) (PackTracePins B.Bin q (d+1) m w k),
        f.size ≤ 1+k*(Fintype.card (Cube D → Deck (d+1))*C*(d+1+w+1)^e) ∧
        ∀ {Port : Type} {bits : Port → ℕ} {K : Type*} (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n)),
          let input := fun i => (child i).pack
          let active := fun i => (child i).active
          ∀ (L : Labels B input active (childSites (d := d) (n := n) child)),
            (∀ i c, (child i).active c = true → dist ((child i).midpoint c) ((child i).site ((child i).pack.layout.src c)) ≤
              dist ((child i).site ((child i).pack.layout.src c)) ((child i).site ((child i).pack.layout.dst c))/2) →
            ∀ (z : PackTables B.Bin q (d+1) m w k → Bool) (H : ℕ),
              tableCount z = B.deckCounts input active L.kind L.lift enum index →
              (∀ i j b g, B.deckCounts (d := d+1) input active L.kind L.lift enum index i j b g ≤ H) →
              packRunWidth (Fintype.card (Cube D → Deck (d+1))) P k H ≤ w →
              ∃ (choice : Fin k → Fin m) (deck : Fin k → Fin q → Deck (d+1)),
                let tags := B.tag (d := d+1) (n := n) input active L.kind L.lift
                let ω := fun i => deckSample enum index (choice i,deck i)
                (∀ i j, f.eval z (.inr (i,.inl j)) = true ↔ j = choice i) ∧
                (∀ i b, f.eval z (.inr (i,.inr b)) = keyWord q (d+1) (deck i) b) ∧
                (∀ b g, ParseBatchSort.value (fun s => f.eval z (.inl (.inl (b,g,s)))) =
                  SeedIntervals.count (parallelPacks input).layout (jointBin input tags ω) (g ∘ enum.symm,b)) ∧
                Real.sqrt (Fintype.card (Cube D → Deck (d+1))) * Real.sqrt (binEnergy fun a =>
                  SeedIntervals.count (parallelPacks input).layout (jointBin input tags ω) a / k -
                  binMean input tags (sampleProb (d+1) n) a) ≤
                  (N : ℝ)*PlacedStep.childMaximum child hk / Real.sqrt k := by
  obtain ⟨N,energy⟩ := B.child_sample_energy n
  obtain ⟨P,C,e,hP,make⟩ := B.compiledSample_frames enum index
  refine ⟨N,P,C,e,hP,?_⟩
  intro d k w hd hk hw
  cases d with
  | zero => omega
  | succ d =>
    obtain ⟨f,hf,choose⟩ := make k (d+2) w hk (by omega) hw
    refine ⟨f,hf,?_⟩
    intro Port bits K child input active L hm z H hz hcounts hwidth
    obtain ⟨j,deck,flags,keys,counts,dev⟩ := choose input active L.kind L.lift z H hz hcounts hwidth
    let X := PlacedStep.childMaximum child hk
    have hX (i : Fin k) : (child i).concentration ≤ X := Finset.le_sup'
      (s := (Finset.univ : Finset (Fin k))) (fun i => (child i).concentration) (Finset.mem_univ i)
    have hX₀ : 0 ≤ X := ((child ⟨0,hk⟩).nonneg.2).trans (hX ⟨0,hk⟩)
    refine ⟨j,deck,flags,keys,counts,dev ((N : ℝ)*X) (mul_nonneg (Nat.cast_nonneg _) hX₀) ?_⟩
    intro i a
    exact (energy d child L hm i ((index a).1,(index a).2,1)).trans (pow_le_pow_left₀
      (mul_nonneg (Nat.cast_nonneg N) (child i).nonneg.2) (mul_le_mul_of_nonneg_left (hX i) (Nat.cast_nonneg N)) 2)

end Shortening.PreparedBins

end BorderVNP
end Computability
end OAI
