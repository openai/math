import OAI.Computability.BorderVNP.ShortenPublicPopulationCandidates
import OAI.Computability.BorderVNP.CoverDeckPackSequence

/-! # Compiling all input packs' candidate population tables

Each candidate histogram uses the cable names reserved for its own pack.
The physical input wires are common, so every pack can read the retained
output of the same endpoint join. The total work sums the actual numbers
of reserved rows and charges one tile table per pack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PackMotions Hecke ParseBatchSort
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q n m : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    (perm : Fin m → Equiv.Perm (Cube D)) (word : Fin m → ProductSample (lattice 1) elliptic (Cube D) n)

private theorem sum_batch_budget {K : ℕ} (r : Fin K → ℕ) (V A W : ℕ) :
    ∑ i, (r i+V+1)*A*W = ((∑ i, r i)+K*(V+1))*A*W := by
  simp only [←Finset.sum_mul,Nat.add_assoc,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_add]

set_option maxHeartbeats 1000000 in
/-- Literal candidate populations in the input bank of the full deck selection sequence. -/
theorem packTables_frames :
    ∃ A p : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (w copies : ℕ)
      {U : Fin copies → Type*} [∀ i, Fintype (U i)] {σ : Type*} [Fintype σ]
      (a : ∀ i, CandidatePins (↥B.types) (U i) σ q (d+2*n+2*n) w),
      ∃ f : Frame σ (PackTables B.Bin q (d+2*n) m w copies),
        (∀ T : ℕ, (∀ i, Fintype.card (U i) ≤ T) → w ≤ Nat.clog 2 (T+1) →
          let V := Fintype.card (Cube D → Deck (d+2*n))
          f.size ≤ 1 + ((∑ i, Fintype.card (U i))+copies*(V+1))*A*(Nat.clog 2 (T+V+2)+1)^p) ∧
        ∀ {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (slot : ∀ i, (input i).layout.Edge ↪ U i) (x : σ → Bool),
          (∀ i, CandidateReads B enum (a i) input active sites L i (slot i) x hd) →
          let bin := fun i j => candidateTag B input active sites L i (perm j) (word j)
          (∀ i j b, SeedIntervals.count (input i).layout (bin i j) b < 2^w) →
          ∀ i j b (g : Fin q → Deck (d+2*n)),
            value (fun k => f.eval x (i,j,b,g,k)) =
              SeedIntervals.count (input i).layout (bin i j) (g ∘ enum.symm,b) := by
  obtain ⟨A,p,one⟩ := candidate_frames B enum perm word
  refine ⟨A,p,?_⟩
  intro d hd w copies U instU σ instσ a
  choose frame size he using fun i => one d hd w (a i)
  obtain ⟨all,hall,run⟩ := exists_parallelFrames frame
  refine ⟨all.select (fun z => ⟨z.1,z.2⟩), ?_, ?_⟩
  · intro T hT hw V
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => size i T (hT i) hw)
    rw [sum_batch_budget] at sum
    exact hall.trans (Nat.add_le_add_left sum 1)
  · intro P bits K input active sites L slot x reads bin fits i j b g
    simp only [Frame.select_eval,run]
    exact he i input active sites L i (slot i) x (reads i) (fits i) j b g

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
