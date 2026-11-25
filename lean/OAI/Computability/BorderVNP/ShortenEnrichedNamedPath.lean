import OAI.Computability.BorderVNP.ShortenEnrichedNode
import OAI.Computability.BorderVNP.ShortenEnrichedRecordClosure

/-!
# The assigned state and physical kernel family of a finite prepared path

Every level stores its actual occupied table, sparse directory and local
geometric invariant. The histogram pins of the normalized history are
identified with the concrete seed, term and bit triple of each physical node.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath

open Crossing Cover Cover.Frame Epoch Epoch.Round Shortening Shortening.Adaptive Packing Physical
open Shortening.PublicRelative Shortening.PreparedBins NamedKernel
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u v
variable {D m b k : ℕ} [NeZero D] {K : Type u} [Field K] {P : Type} {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} (p : SourcePath b e h H ν) (last high : ℕ) (V E : ℕ → ℕ) (w : ℕ)

/-- Actual occupied public rows at each path level, with one shared word width. -/
noncomputable abbrev StatePins (j : ℕ) := Pins (p.catalog j) (p.asPath.depth last high j+1) (V j) (E j) w

/-- A named physical pack carrying its whole assigned state and any retained local payload. -/
noncomputable abbrev NamedAt (P : Type) (bits : P → ℕ) (k : ℕ) (Extra : ℕ → Type v) (j : ℕ) :=
  NamedState.At (D := D) (K := K) (lev := p.asPath.depth last high) (V := V) (E := E)
    (W := p.StatePins last high V E w) (Extra := Extra) (k := k) (bits := bits) j

variable [Fintype P] {Extra : ℕ → Type v} (cap : ℕ → ℕ)

/-- Admissibility of the literal named input, with expanded records for the
next count bound. The parameter allows further invariants on the actual
payload and full assigned pin vector. -/
structure NamedGood
    (keep : ∀ j, p.NamedAt last high V E w P bits k Extra j → Prop)
    (j : ℕ) (x : p.NamedAt last high V E w P bits k Extra j) : Prop where
  /-- The selected physical node's sites, charged segments and true midpoints. -/
  placed : Catalog.PlacedAt (p.catalog j) h x.placed
  /-- The stored bits encode the named directory, including cable occupancy. -/
  reads : x.names.Reads (p.catalog j) (segmentField (factorEnum D) (p.catalog j) rfl) x.words
  /-- The current layer's per-tile bound pays for all cable widths. -/
  expanded : ∃ r, RecordsWithin x.placed r true (cap j)
  /-- Further facts retained about this particular assigned state. -/
  retained : keep j x

/-- A native frame using ordinary seed/term/bit triples before reindexing
to the normalized program's histogram pins. -/
noncomputable abbrev Node (k : ℕ) (i : Fin b) :=
  Frame ((Fin k × p.StatePins last high V E w i.val) ⊕
    Shortening.PublicDenseReceipt.Words (Shortening.PublicDenseReceipt.Seed (p.pattern i).bins (p.asPath.depth last high (i.val+1))) e.count w)
    (p.StatePins last high V E w (i.val+1) ⊕ Unit)

/-- The single physical node family assembled using the canonical history pins. -/
noncomputable def namedKernels (nodes : ∀ i : Fin b, p.Node last high V E w k i) :
    Steps k b (p.StatePins last high V E w)
      (Pin (Cube D) (fun i => (p.pattern i).bins.Bin) (p.asPath.depth last high) e.count (fun _ => w)) :=
  fun j hj => scheduled (nodes ⟨j,hj⟩) (pinEquiv (I := Cube D) (B := fun i => (p.pattern i).bins.Bin) (depth := p.asPath.depth last high) (e := e) (fun _ => w) ⟨j,hj⟩) id

omit [Fintype P] in
/-- Reindexing a physical node to the public history preserves its entire gate count. -/
theorem namedKernels_size (nodes : ∀ i : Fin b, p.Node last high V E w k i) (i : Fin b) :
    (p.namedKernels last high V E w nodes i.val i.isLt).size = (nodes i).size := scheduled_size ..

end PackedHistoryCircuit.Normalized.SourcePath

end BorderVNP
end Computability
end OAI
