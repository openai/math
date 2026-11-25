import OAI.Computability.BorderVNP.ShortenPublicPackFrontWires
import OAI.Computability.BorderVNP.ShortenCompiledAt

/-! # Reading the calibrated child geometry from its merged public cable records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicRelative

open PublicSegments PublicParallel Cover Cover.AddressCircuit Epoch PreparedBins Crossing Packing
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube

universe u
variable {D n d k V E w : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) {Data : Type*} [Fintype Data] {Port : Type} {bits : Port → ℕ} {K : Type u}
    (child : Fin k → PlacedPack D Port bits K (Cube D) (d+2*n))

/-- A segment reader applied to the saved parallel layout produces a single
set of labels for the actual positive child cables at the motion domain.
Transporting the level changes neither cable charge nor measured distance. -/
theorem frontChildRead (sites : ∀ i, (child i).pack.layout.Site ↪ Fin V)
    (rows : ∀ i, (child i).pack.layout.Edge ↪ Fin E)
    (dummy : ∀ i, Fin E → (child i).pack.layout.Site)
    (field : FieldBit (↥S) (Cube D) (d+2*n+1) → Data)
    (raw : Raw Data (k*V) (k*E) w w → Bool)
    (ready : SegmentReady S (parallelPacks fun i => (child i).pack).layout (parallelName sites)
      (parallelName rows) (parallelDummy dummy) (fun v => (child v.1).site v.2) field
      (fun a => (child a.1).charged a.2) raw)
    (short : ∀ i a, (child i).charged a = true →
      dist ((child i).site ((child i).pack.layout.src a)) ((child i).site ((child i).pack.layout.dst a)) ≤ 2*h)
    (reader : Frame (Raw Data (k*V) (k*E) w w) (Classified Data (↥B.types) (k*V) (k*E) w w))
    (recovers : Reconstructs.{_,u} B (factorEnum D) (by omega)
      (fieldAtLevel (Nat.add_right_comm d (2*n) 1) field) reader) :
    ∃ L : Labels B (fun i => (child i).pack) (fun i => (child i).active) (childSites child),
      PhysicalReads B (factorEnum D) (by omega) (fieldAtLevel (Nat.add_right_comm d (2*n) 1) field)
        (fun i => (child i).pack) (fun i => (child i).active) (childSites child) L (parallelName rows) (reader.eval raw) := by
  let level := Nat.add_right_comm d (2*n) 1
  obtain ⟨valid,fieldRead⟩ := ready.fields_atLevel level
  have hdist (i a) (ha : (child i).charged a = true) :
      dist (childSites child i ((child i).pack.layout.src a)) (childSites child i ((child i).pack.layout.dst a)) ≤ 2*h := by
    rw [childSites,childSites,levelCast_dist]
    exact short i a ha
  have out := recovers (fun i => (child i).pack) (childSites child) (fun i v => valid ⟨i,v⟩)
    (fun i => (child i).charged) (parallelName sites) (parallelName rows) (parallelDummy dummy)
    raw ready.names fieldRead ready.charge hdist
  rw [positiveMask_childSites child] at out
  exact out

end Shortening.PublicRelative

end BorderVNP
end Computability
end OAI
