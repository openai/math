import OAI.Computability.BorderVNP.ShortenPublicPopulationCandidateRows
import OAI.Computability.BorderVNP.ShortenPublicSegmentPhysical

/-! # Reading a single pack's candidate input from the physical cable table

The shared endpoint join runs once on all packs. For each pack its reserved
row names form the fiber of the static owner map. The candidate histogram
needs exactly this fiber and reads the joined fields through unchanged wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicSegments

open Cover Cover.AddressCircuit Epoch Catalog Crossing Packing PreparedBins PackMotions PublicPopulation
open scoped Classical

variable {D q V E k w copies n d : ℕ} {Data : Type*}
    {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ} (B : PreparedBins D S h η)
    (enum : Fin q ≃ Cube D) (home : Fin E → Fin copies) (i : Fin copies)
    (field : FieldBit (↥S) (Cube D) (d+2*n+2*n) → Data)

/-- Restrict the joined cable table to the stable names owned by one pack. -/
def candidatePins :
    CandidatePins (↥B.types) {u // home u=i} (Classified Data (↥B.types) V E k w) q (d+2*n+2*n) w where
  live u := .inr (u.val,.inl ())
  width u := widthPin u.val
  kind u t := .inr (u.val,.inr t)
  source u := sourcePin enum field u.val

variable {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
    (rows : (parallelPacks input).layout.Edge ↪ Fin E) (owner : ∀ e, home (rows e) = e.1)

/-- Original edge names in the reserved row fiber of their pack. -/
def candidateSlot : (input i).layout.Edge ↪ {u // home u=i} where
  toFun e := ⟨rows ⟨i,e⟩,owner ⟨i,e⟩⟩
  inj' := by
    intro e f hef
    have h := rows.injective (congrArg Subtype.val hef)
    exact eq_of_heq (Sigma.mk.inj h).2

/-- Every unused name in a pack's row fiber is also unused in the full physical table. -/
theorem candidateSlot_absent (u : {v // home v=i}) (hu : u ∉ Set.range (candidateSlot home i input rows owner)) :
    u.val ∉ Set.range rows := by
  rintro ⟨⟨j,e⟩,eq⟩
  have hi : j=i := (owner ⟨j,e⟩).symm.trans ((congrArg home eq).trans u.property)
  subst j
  exact hu ⟨e,Subtype.ext eq⟩

variable (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
    (L : Labels B input active sites)

/-- The actual classifier and endpoint join feed every candidate of a pack
before the motion selection stage has produced any outputs. -/
theorem candidateReads_of_physical (y : Classified Data (↥B.types) V E k w → Bool) (hd : 1 ≤ d)
    (physical : PhysicalReads B enum (by omega) field input active sites L rows y) :
    CandidateReads B enum (candidatePins B enum home i field) input active sites L i
      (candidateSlot home i input rows owner) y hd :=
  ⟨fun e => physical.live ⟨i,e⟩, fun u hu => physical.empty u.val (candidateSlot_absent home i input rows owner u hu),
   fun e he => physical.widths ⟨i,e,he⟩, fun e he => physical.kinds ⟨i,e,he⟩,
   fun e he => physical.sources ⟨i,e,he⟩⟩

end Shortening.PublicSegments

end BorderVNP
end Computability
end OAI
