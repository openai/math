import OAI.Computability.BorderVNP.PackedFrozenPrepRoom
import OAI.Computability.BorderVNP.PackedFrozenPrepHeader
import OAI.Computability.BorderVNP.PackedFrozenSelectedPreRead
import OAI.Computability.BorderVNP.PackedSelectedPrivateFieldRows

/-! # The complete prepared history on the machine's original grouped port numbering

The outer port capacity is recursively flattened in the named run and written
as a power in the frozen schema. The resulting equality of capacities changes
the type of the public header while preserving its numerical coordinates and
the genuine private site programs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.PhysicalEpochs Inherited WorkWords FrozenTape EnrichedOuter ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1600000
set_option maxRecDepth 3500

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {start T w : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
    (C : Compiled bits deep budget cap w) (base : FrozenTape.Format) (t : ℕ) (ht : t<T)

variable (p : WorkWords.Ports (CoverScale.sites (Cube D) start))
    (leaf : P ↪ Fin (CoverScale.sites (Cube D) start))
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (fit : (before S start t 0).sites ≤ 2^w)
    (c : Fin (fan S) → Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout)
    (x : Fin (fan S) × ProgramSchemas.outerPins S start w base t → Bool)

local notation3 "comp" => C.atLevel t ht
local notation3 "Fmt" => ProgramSchemas.epoch S start w base t
local notation3 "nextFmt" => ProgramSchemas.stage S start w base t 0

private theorem installed_port_cast {n n' : ℕ} (port : Port (fan S) P t ↪ Fin n) (hn : n=n') (i : Fin (fan S)) :
    (comp).epoch.installedPrivatePrograms ((comp).program.privateSiteRows (port.trans (finCongr hn).toEmbedding) (seeds t)) c old i =
      (comp).epoch.installedPrivatePrograms ((comp).program.privateSiteRows port (seeds t)) c old i := by
  subst n'
  have same : (port.trans (finCongr (rfl : n=n)).toEmbedding) = port := DFunLike.ext _ _ fun _ => rfl
  rw [same]

/-- The complete prepared tape, on exactly the `Compiled.privateSiteRows` consumed by the
native history replay. All address guards follow from the actual child capacity and word fit. -/
theorem tapePre_native_image (i : Fin (fan S))
    (read : ∀ j, Boundary.WidthReads (c j).val (old j) (fun z => x (j,.inl z)))
    (previous : (Fmt).schema.Image (fun z => x (i,.inr z)) ((c i).val.rows.site.trans Fin.valEmbedding)
      (fun v => (old i v).program))
    (portOK : (p.outer S start t).Reads (c i).val.pack.layout (c i).val.rows.site (privatePorts S leaf t))
    (portWidth : (PortTable.mk _ leaf p).Widths bits w)
    {B : ℕ} (childCap : ∀ j, SiteCap (c j).val.route (Subdivision.publicProgramData (old j)) true B)
    (leafFit : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
      Fin (hopCount S.budget S.radius)))*B < 2^w) (one : 1 < 2^w) :
    (nextFmt).schema.Image (fun z => (tapePre C base t ht (prepHeader (S := S) t p) fit).eval x (i,.inr z))
      ((((comp).epoch.run c).flat i).val.names.sites.trans Fin.valEmbedding)
      (fun v => ((comp).epoch.installedPrivatePrograms (C.privateSiteRows leaf seeds t ht) c old i v).program) := by
  let eqn := input_port_count (S := S) (start := start) t
  let port := privatePorts S leaf t
  let header := prepHeader (S := S) t p
  have portRead := castHeader_reads (c i).val.pack.layout (c i).val.rows.site port eqn (p.outer S start t) portOK
  have width := p.outer_widths leaf S start portWidth t
  have headFit (j) : header.width j < 2^w := width.fit (Fin.cast eqn.symm j)
  have cells := (comp).prep_room (C.privateSiteRows leaf seeds t ht) c old childCap leafFit i
  have both (v b) : value (fun j => x (i,.inl (.inr ((c i).val.rows.site v,b,j)))) =
      if b then (old i v).program.size else (old i v).program.work := by
    simpa only [assignedColumn,Frame.initial_eval] using ((read i).covers b).live v
  have image := tapePre_image C base t ht header fit c old x (port.trans (finCongr eqn).toEmbedding) (seeds t)
    i (fun j => (read j).geometry) both previous portRead headFit one cells.1 cells.2.1 cells.2.2
  rw [installed_port_cast C t ht seeds c old port eqn i] at image
  exact image

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
