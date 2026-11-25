import OAI.Computability.BorderVNP.PackedFrozenPreparedLeaf
import OAI.Computability.BorderVNP.PackedFrozenNativeFrames
import OAI.Computability.BorderVNP.PackedFrozenNamedOutput

/-! # Complete readback on the physical selected inner tree -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.PhysicalEpochs Inherited WorkWords FrozenTape EnrichedOuter SourcePath.NamedRun InheritedBank VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {start T w : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
    (C : Compiled bits deep budget cap w) (base : Format) (t : ℕ) (ht : t<T)
variable (header : WorkWords.Ports (CoverScale.sites (Cube D) start))
    (leaf : P ↪ Fin (CoverScale.sites (Cube D) start)) (wr : WidthRanges S start T w)
    (seeds : ∀ t, ∀ i : Fin S.rounds,
      ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
    (c : Fin (fan S) → Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout)
    (x : Fin (fan S) × ProgramSchemas.outerPins S start w base t → Bool)
    (B : ℕ)

local notation3 (prettyPrint := false) "A" => C.atLevel t ht
local notation3 (prettyPrint := false) "port" => privatePorts S leaf t
local notation3 (prettyPrint := false) "p" => header.outer S start t
local notation3 (prettyPrint := false) "rows" => C.privateSiteRows leaf seeds t ht
local notation3 (prettyPrint := false) "fit" => wr.initial t ht
local notation3 (prettyPrint := false) "pre" => C.tapePre base t ht (prepHeader t header) fit
local notation3 (prettyPrint := false) "flat" => ((A).epoch.run c).flat
local notation3 (prettyPrint := false) "pr" => (A).epoch.installedPrivatePrograms rows c old

variable (hm : 0 < m) (number : e.Entry → ℕ)
local notation3 (prettyPrint := false) "initialFmt" => ProgramSchemas.installed S start w t (ProgramSchemas.epoch S start w base t)
local notation3 (prettyPrint := false) "fmt(" n "," j ")" => ProgramSchemas.inner S.source S.last (S.high (offset S start t))
  S.fanIn (fun a => (before S start t a).edges) n w initialFmt j
local notation3 (prettyPrint := false) "geo" j => S.source.StatePins S.last (S.high (offset S start t))
  (fun a => (before S start t a).sites) (fun a => (before S start t a).edges) w j
local notation3 (prettyPrint := false) "pins(" n "," j ")" => (fmt(n,j)).Output (geo j) (before S start t j).sites w w
local notation3 (prettyPrint := false) "native" => NativeTape.steps (A).program initialFmt p port
  (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht) (wr.successor t ht) hm
local notation3 (prettyPrint := false) "selected" => C.stageSteps base header leaf wr hm t ht

/-- Subdivision and every combining node of the selected epoch read the
actual attained flat histogram. Its root programs, width words and marked
tape are all indexed by the native saved row names. -/
theorem stage_root_read
    (child : ∀ i, Boundary.WidthReads (c i).val (old i) (fun j => x (i,.inl j)))
    (previous : ∀ i, (ProgramSchemas.epoch S start w base t).schema.Image (fun z => x (i,.inr z))
      ((c i).val.rows.site.trans Fin.valEmbedding) (fun v => (old i v).program))
    (portOK : ∀ i, (p).Reads (c i).val.pack.layout (c i).val.rows.site port)
    (small : (PortTable.mk _ leaf header).Widths bits w)
    (childCap : ∀ i, SiteCap (c i).val.route (old i).bankFields true B) (hB : 0 < B)
    (leafFit : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
      Fin (hopCount S.budget S.radius)))*B < 2^w) (one : 1 < 2^w)
    (word : ∀ i : Fin S.rounds, 2*widthBudget S B (i.val+1) < 2^w)
    (hookRoom : ∀ i : Fin S.rounds, HookTape.sourceRoom e (0,false)
      (loadMultiplier e*(S.source.pattern i).record*S.fanIn*widthBudget S B i.val)
      ((measured_population_cap (I := Cube D) (B := (S.source.pattern i).bins.Bin) e S.saving).choose*
        ((S.source.pattern i).record*S.fanIn*widthBudget S B i.val)) < 2^w)
    (q : (A).epoch.F.Hist flat) :
    let guess := ((A).epoch.run c).word (A).epoch.room q
    let root := fun j => (flatEpoch selected).eval (Sum.elim ((pre).eval x) guess) (.inl j)
    NativeTape.Read p port (widthBudget S B) S.rounds (ProgramSchemas.stage S start w base t S.rounds)
      (((A).returned c).run.root q) ((A).rootPrivate rows c old number q) root := by
  intro guess root
  let cap₀ := portCapacity S (CoverScale.sites (Cube D) start) t
  let cap₁ := portSlots S start t 0
  have eqn : cap₀ = cap₁ := input_port_count t
  let schema := fun n => fmt(n,S.rounds)
  let F := fmt(cap₀,S.rounds)
  let G := fmt(cap₁,S.rounds)
  have same : F = G := congrArg schema eqn
  let back := cast (congrArg (fun X : Format => X.Output (geo S.rounds) (before S start t S.rounds).sites w w) same)
  have rootWire (j : pins(cap₀,S.rounds)) :
      root (back j) = (flatEpoch native).eval (Sum.elim ((pre).eval x) guess) (.inl j) :=
    resizeSteps_flat_read eqn (fun n j => pins(n,j)) (Count S start t (fun _ => w)) native
      (fun i z => (pre).eval x (i,z)) guess (.inl j)
  have atLeaf := C.tapePre_leafRead base t ht header leaf wr seeds c old x B child previous portOK small childCap leafFit one
  have read := NativeTape.flat_read (A).program initialFmt p port (width_rectangle S deep ht) (tapeEdgeRectangle S deep ht)
    (wr.successor t ht) hm (seeds t) number (widthBudget S B) (header.outer_widths leaf S start small t)
    (fun i => widthBudget_pos S hB i.val) (widthBudget_step S B) word hookRoom flat pr ((pre).eval x) atLeaf q
  apply NativeTape.Read.of_reindex p port (widthBudget S B) S.rounds (((A).returned c).run.root q)
    ((A).rootPrivate rows c old number q) same root
  change NativeTape.Read p port (widthBudget S B) S.rounds F (((A).returned c).run.root q)
    ((A).rootPrivate rows c old number q) (fun z => root (back z))
  simp_rw [rootWire]
  exact read

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
