import OAI.Computability.BorderVNP.PackedFrozenNativePreRead
import OAI.Computability.BorderVNP.PackedFrozenNamedRead
import OAI.Computability.BorderVNP.PackedInheritedWorkHorizon

/-! # Complete named read at every actually subdivided leaf

The public geometry and two width columns come from the selected width
preparation. The chronological tape is read at the very same installed
program. The named run uses the original port capacity throughout.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.PhysicalEpochs Inherited WorkWords FrozenTape EnrichedOuter SourcePath.NamedRun VPVNP.VerifierNetwork
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
local notation3 (prettyPrint := false) "oldY" => fun i j => x (i,Sum.inl j)
local notation3 (prettyPrint := false) "flat" => ((A).epoch.run c).flat
local notation3 (prettyPrint := false) "pr" => (A).epoch.installedPrivatePrograms rows c old

private theorem pre_header_cast {np nq : ℕ} (eqn : np=nq) (a : WorkWords.Ports np) :
    (A).widthPre rfl (castHeader eqn a) fit = (A).widthPre rfl a fit := by
  subst nq
  rfl

/-- At inner depth zero both width columns, all physical geometry and the
full frozen tape are evaluated at each real selected child. -/
theorem tapePre_leafRead
    (child : ∀ i, Boundary.WidthReads (c i).val (old i) (fun j => x (i,.inl j)))
    (previous : ∀ i, (ProgramSchemas.epoch S start w base t).schema.Image (fun z => x (i,.inr z))
      ((c i).val.rows.site.trans Fin.valEmbedding) (fun v => (old i v).program))
    (portOK : ∀ i, (p).Reads (c i).val.pack.layout (c i).val.rows.site port)
    (small : (PortTable.mk _ leaf header).Widths bits w)
    (childCap : ∀ i, SiteCap (c i).val.route (old i).bankFields true B)
    (leafFit : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
      Fin (hopCount S.budget S.radius)))*B < 2^w) (one : 1 < 2^w) (i : Fin (fan S)) :
    NativeTape.Read p port (widthBudget S B) 0 (ProgramSchemas.stage S start w base t 0)
      (flat i) (pr i) (fun j => (pre).eval x (i,j)) := by
  let initial := (A).widthPre rfl p fit
  have same : (A).widthPre rfl (prepHeader t header) fit = initial :=
    pre_header_cast C t ht wr (input_port_count t) p
  have word : (fun j => (pre).eval x (i,.inl j)) = fun j => initial.eval (Function.uncurry oldY) (i,j) := by
    funext j
    exact (C.tapePre_width base t ht (prepHeader t header) fit x i j).trans
      (congrArg (fun f => Frame.eval f (Function.uncurry oldY) (i,j)) same)
  refine ⟨?_,C.tapePre_native_image base t ht header leaf seeds fit c old x i child (previous i) (portOK i)
    small childCap leafFit one⟩
  change WidthRead p port (widthBudget S B) 0 (flat i) (pr i) (fun j => (pre).eval x (i,.inl j))
  rw [word]
  refine ⟨(A).widthPre_assigned rfl p fit oldY c (fun j => (child j).geometry) i,?_,?_,?_⟩
  · exact fun b => (A).widthPre_covers rfl fit oldY rows c old p (fun j => (child j).geometry)
      (fun j => (child j).covers true) portOK (header.outer_widths leaf S start small t).fit
      ((A).widthPre_room rows c old childCap leafFit) i b
  · exact (A).widthPre_ports rows c p portOK i
  · have capacity := (A).epoch.installedPrivatePrograms_bank_within rows c old true B childCap i
    exact fun tile => (capacity tile).trans (by simp only [widthBudget,pow_zero,one_mul]; rfl)

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
