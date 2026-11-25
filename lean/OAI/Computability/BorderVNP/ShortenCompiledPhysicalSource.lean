import OAI.Computability.BorderVNP.ShortenCompiledSampleChoice
import OAI.Computability.BorderVNP.CoverDeckPackWidth
import OAI.Computability.BorderVNP.ShortenPublicPopulationCandidatePhysicalTables

/-! # Calibrated-width candidate tables from classified physical cable records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PreparedBins PackMotions PublicPopulation Hecke
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

private noncomputable def nativeVolume (D l : ℕ) := Fintype.card (Cube D → Deck l)
private theorem nativeVolume_nat (D l : ℕ) : nativeVolume D l = Nat.card (Cube D → Deck l) :=
  Nat.card_eq_fintype_card.symm

open scoped BorderVNP.Epoch.Cube

private theorem nativeVolume_eq (D l : ℕ) : nativeVolume D l = Fintype.card (Cube D → Deck l) :=
  (nativeVolume_nat D l).trans Nat.card_eq_fintype_card

private theorem count_le_total {D : ℕ} {Port : Type*} {bits : Port → ℕ} (N : Network D Port bits)
    {Bin : Type} (tag : N.Edge → Option Bin) (b : Bin) : SeedIntervals.count N tag b ≤ ∑ e, N.width e := by
  rw [SeedIntervals.count_eq_sum]
  exact Finset.sum_le_sum fun _ _ => by split <;> omega

variable {D q n m : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    (index : Fin m ≃ PackedDeckMean.MotionCandidate (lattice 1) elliptic (Cube D) n)

/-- The same physical candidate table works at every sufficiently wide word size. -/
theorem classifiedTablesAtWidth :
    ∃ A p : ℕ, ∀ (r l : ℕ) (hr : 1 ≤ r) (_ : l = r+2*n) (w copies : ℕ)
      {Data : Type*} [Fintype Data] (sites rows nameWidth : ℕ) (home : Fin rows → Fin copies)
      (field : FieldBit (↥S) (Cube D) (l+2*n) → Data),
      let vol := Fintype.card (Cube D → Deck l)
      ∃ f : Frame (Classified Data (↥B.types) sites rows nameWidth w) (PackTables B.Bin q l m w copies),
        (∀ T, rows ≤ T → w ≤ Nat.clog 2 (T+1) →
          f.size ≤ 1+(rows+copies*(vol+1))*A*(Nat.clog 2 (T+vol+2)+1)^p) ∧
        ∀ {Port : Type} {bits : Port → ℕ} {K : Type*} (input : Fin copies → Pack D Port bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (points : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (l+2*n))
          (L : Labels B input active points) (slot : (parallelPacks input).layout.Edge ↪ Fin rows)
          (_ : ∀ a, home (slot a) = a.1) (x : Classified Data (↥B.types) sites rows nameWidth w → Bool),
          PhysicalReads B enum (by omega) field input active points L slot x →
          ∀ H : ℕ, H < 2^w → (∀ i, (∑ a, (input i).layout.width a) ≤ H) →
          tableCount (f.eval x) = B.deckCounts input active L.kind L.lift enum index ∧
            ∀ i j b g, B.deckCounts (d := l) input active L.kind L.lift enum index i j b g ≤ H := by
  obtain ⟨A,p,tables⟩ := physicalPackTables_frames B enum (fun i => (index i).1) (fun i => (index i).2)
  refine ⟨A,p,?_⟩
  intro r l hr hl w copies Data instData sites rows nameWidth home field
  subst l
  intro vol
  obtain ⟨table,hs,he⟩ := tables r hr sites rows nameWidth w copies home field
  refine ⟨table,?_,?_⟩
  · intro T hrows hbits
    have h₁ : table.size ≤ 1+(rows+copies*(nativeVolume D (r+2*n)+1))*A*
        (Nat.clog 2 (T+nativeVolume D (r+2*n)+2)+1)^p := hs T hrows hbits
    rwa [nativeVolume_eq] at h₁
  · intro Port bits K input active points L slot own x reads H hH htotal
    have cap i j b : SeedIntervals.count (input i).layout
        (candidateTag B input active points L i (index j).1 (index j).2) b ≤ H :=
      (count_le_total (input i).layout _ _).trans (htotal i)
    constructor
    · funext i j b g
      exact he input active points L slot own x reads (fun i j b => (cap i j b).trans_lt hH) i j b g
    · intro i j b g
      exact cap i j (g ∘ enum.symm,b)

/-- Compute all candidate populations at the public score width. The physical
level is named separately from the depth used by the cleared motion program,
so the result also splices into a selector calibrated at a fixed depth offset. -/
theorem classifiedTablesAt :
    ∃ A p : ℕ, ∀ (r l : ℕ) (hr : 1 ≤ r) (_ : l = r+2*n) (P H copies : ℕ)
      {Data : Type*} [Fintype Data] (sites rows nameWidth : ℕ) (home : Fin rows → Fin copies)
      (field : FieldBit (↥S) (Cube D) (l+2*n) → Data),
      let vol := Fintype.card (Cube D → Deck l)
      let w := AddressCircuit.packWidth vol P copies H
      ∃ f : Frame (Classified Data (↥B.types) sites rows nameWidth w) (PackTables B.Bin q l m w copies),
        f.size ≤ 1+(rows+copies*(vol+1))*A*(Nat.clog 2 (packPadding rows vol P copies H+vol+2)+1)^p ∧
        ∀ {Port : Type} {bits : Port → ℕ} {K : Type*} (input : Fin copies → Pack D Port bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (points : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (l+2*n))
          (L : Labels B input active points) (slot : (parallelPacks input).layout.Edge ↪ Fin rows)
          (_ : ∀ a, home (slot a) = a.1) (x : Classified Data (↥B.types) sites rows nameWidth w → Bool),
          PhysicalReads B enum (by omega) field input active points L slot x →
          (∀ i, (∑ a, (input i).layout.width a) ≤ H) →
          tableCount (f.eval x) = B.deckCounts input active L.kind L.lift enum index ∧
            ∀ i j b g, B.deckCounts (d := l) input active L.kind L.lift enum index i j b g ≤ H := by
  obtain ⟨A,p,tables⟩ := classifiedTablesAtWidth B enum index
  refine ⟨A,p,?_⟩
  intro r l hr hl P H copies Data instData sites rows nameWidth home field vol w
  obtain ⟨table,hs,he⟩ := tables r l hr hl w copies sites rows nameWidth home field
  obtain ⟨hrows,hbits⟩ := packPadding_fits rows vol P copies H
  exact ⟨table,hs _ hrows hbits,fun input active points L slot own x reads htotal =>
    he input active points L slot own x reads H (packWidth_fits vol P copies H).2.1 htotal⟩

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
