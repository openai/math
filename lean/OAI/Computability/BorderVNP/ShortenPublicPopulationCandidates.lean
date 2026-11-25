import OAI.Computability.BorderVNP.ShortenPublicPopulationCandidateRows
import OAI.Computability.BorderVNP.ShortenPublicPopulationBudget

/-! # Finite bank of candidate histograms for one pack

The complete finite motion catalog is evaluated on the same reserved rows.
Candidate planes are wired into the factor order used by the deck selector.
Their total size is linear in rows and actual tiles times a polylogarithmic
factor, with the catalog held fixed before any input dimensions are chosen.
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

set_option maxHeartbeats 1500000 in
/-- All finite candidate arrays for one pack before posttranslation. The histogram at the
deck selector's product address is the actual count at the corresponding geometric seed. -/
theorem candidate_frames :
    ∃ A p : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (w : ℕ) {U σ : Type*} [Fintype U] [Fintype σ]
      (a : CandidatePins (↥B.types) U σ q (d+2*n+2*n) w),
      ∃ f : Frame σ (Fin m × B.Bin × (Fin q → Deck (d+2*n)) × Fin w),
        (∀ T : ℕ, Fintype.card U ≤ T → w ≤ Nat.clog 2 (T+1) →
          let V := Fintype.card (Cube D → Deck (d+2*n))
          f.size ≤ (Fintype.card U+V+1)*A*(Nat.clog 2 (T+V+2)+1)^p) ∧
        ∀ {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (i : Fin copies)
          (slot : (input i).layout.Edge ↪ U) (x : σ → Bool),
          CandidateReads B enum a input active sites L i slot x hd →
          let bin := fun j => candidateTag B input active sites L i (perm j) (word j)
          (∀ j b, SeedIntervals.count (input i).layout (bin j) b < 2^w) →
          ∀ j b (g : Fin q → Deck (d+2*n)),
            value (fun k => f.eval x (j,b,g,k)) =
              SeedIntervals.count (input i).layout (bin j) (g ∘ enum.symm,b) := by
  choose C e all using fun j => candidateRow_frames B enum (perm j) (word j)
  let c := Finset.univ.sup C
  let k := Finset.univ.sup e
  obtain ⟨A,p,hpoly⟩ := jointCost_polylog (Cube D) q (Fintype.card B.Bin) c k
  refine ⟨m*A+1,p,?_⟩
  intro d hd w U σ instU instσ a
  choose f size he using fun j => all j d hd w a
  obtain ⟨batch,hbatch,eval⟩ := exists_parallelFrames f
  let output (j : Fin m × B.Bin × (Fin q → Deck (d+2*n)) × Fin w) :
      Σ _ : Fin m, ((Cube D → Deck (d+2*n)) × B.Bin) × Fin w :=
    Sigma.mk j.1 ((j.2.2.1 ∘ enum.symm,j.2.1),j.2.2.2)
  refine ⟨batch.select output, ?_, ?_⟩
  · intro T hT hw V
    let R := Fintype.card U+V+1
    let W := (Nat.clog 2 (T+V+2)+1)^p
    have each (j : Fin m) : (f j).size ≤ R*A*W := by
      have row := size j
      have factor : C j*(d+1)^(e j) ≤ c*(d+1)^k :=
        Nat.mul_le_mul (Finset.le_sup (Finset.mem_univ j))
          (Nat.pow_le_pow_right (by omega) (Finset.le_sup (Finset.mem_univ j)))
      apply row.trans
      apply le_trans (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ factor) 1) _)
      exact hpoly d (d+2*n) w (Fintype.card U) T (by omega) hT hw
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => each j)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
    have hR : 1 ≤ R := Nat.le_add_left _ _
    have hW : 1 ≤ W := Nat.one_le_pow _ _ (Nat.le_add_left _ _)
    change batch.size ≤ R*(m*A+1)*W
    calc
      _ ≤ 1 + m*(R*A*W) := hbatch.trans (Nat.add_le_add_left sum 1)
      _ ≤ R*W + m*(R*A*W) := Nat.add_le_add_right (by simpa only [one_mul] using Nat.mul_le_mul hR hW) _
      _ = _ := by ring
  · intro copies P bits K input active sites L i slot x reads bin fits j b g
    simp only [Frame.select_eval,output,eval]
    exact he j input active sites L i slot x reads (fits j) (g ∘ enum.symm,b)

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
