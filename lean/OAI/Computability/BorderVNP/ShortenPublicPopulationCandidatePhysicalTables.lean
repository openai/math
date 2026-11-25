import OAI.Computability.BorderVNP.ShortenPublicPopulationCandidatePhysical
import OAI.Computability.BorderVNP.ShortenCompiledCandidateTables

/-! # The deck selector's candidate tables on actual joined cables

All packs share one endpoint join. Partitioning stable row names by their
original owner counts every reserved row exactly once in the gate bound.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PreparedBins PackMotions
open PublicPopulation ParseBatchSort Hecke
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q n m : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    (perm : Fin m → Equiv.Perm (Cube D)) (word : Fin m → ProductSample (lattice 1) elliptic (Cube D) n)

/-- The disjoint row fibers account for exactly the reserved cable names. -/
theorem candidateRows_card {E copies : ℕ} (home : Fin E → Fin copies) :
    ∑ i, Fintype.card {u // home u=i} = E := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr (Equiv.sigmaFiberEquiv home)

set_option maxHeartbeats 1000000 in
/-- Every candidate in the selection table has the true width sum of its original pack.
The complete circuit precedes the physical labels and every execution of the selector. -/
theorem physicalPackTables_frames :
    ∃ A p : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) {Data : Type*} [Fintype Data]
      (V E k w copies : ℕ) (home : Fin E → Fin copies)
      (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data),
      ∃ f : Frame (Classified Data (↥B.types) V E k w) (PackTables B.Bin q (d+2*n) m w copies),
        (∀ T : ℕ, E ≤ T → w ≤ Nat.clog 2 (T+1) →
          let vol := Fintype.card (Cube D → Deck (d+2*n))
          f.size ≤ 1 + (E+copies*(vol+1))*A*(Nat.clog 2 (T+vol+2)+1)^p) ∧
        ∀ {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : Labels B input active sites) (rows : (parallelPacks input).layout.Edge ↪ Fin E)
          (_ : ∀ e, home (rows e) = e.1) (x : Classified Data (↥B.types) V E k w → Bool),
          PhysicalReads B enum (by omega) field input active sites L rows x →
          let bin := fun i j => candidateTag B input active sites L i (perm j) (word j)
          (∀ i j b, SeedIntervals.count (input i).layout (bin i j) b < 2^w) →
          ∀ i j b (g : Fin q → Deck (d+2*n)),
            value (fun s => f.eval x (i,j,b,g,s)) =
              SeedIntervals.count (input i).layout (bin i j) (g ∘ enum.symm,b) := by
  obtain ⟨A,p,frames⟩ := packTables_frames B enum perm word
  refine ⟨A,p,?_⟩
  intro d hd Data instData V E k w copies home field
  let pins := fun i => candidatePins B enum (V := V) (k := k) (w := w) home i field
  obtain ⟨f,size,sem⟩ := frames d hd w copies pins
  refine ⟨f,?_,?_⟩
  · intro T hT hw vol
    have hr (i : Fin copies) : Fintype.card {u // home u=i} ≤ T := by
      exact (Fintype.card_subtype_le _).trans (by simpa only [Fintype.card_fin] using hT)
    simpa only [candidateRows_card] using size T hr hw
  · intro P bits K input active sites L rows owner x physical bin fits
    exact sem input active sites L (fun i => candidateSlot home i input rows owner) x
      (fun i => candidateReads_of_physical B enum home i field input rows owner active sites L x hd physical) fits

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
