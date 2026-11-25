import OAI.Computability.BorderVNP.PackedFrozenNamedHistory
import OAI.Computability.BorderVNP.PackedInheritedWorkFlat
import OAI.Computability.BorderVNP.PackedFrozenNativeRead

/-! # Full tape readback on the actual named inner histogram -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.StaticRows
open Packing Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords InheritedBank NamedKernel Physical
open VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m b k np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
variable {e : PaidIdentity K D m} {h H ν : ℝ} {src : SourcePath b e h H ν} {last high : ℕ}
variable {V E : ℕ → ℕ} {w : ℕ} {cap : ℕ → ℕ} {Extra : ℕ → Type u}
variable {keep : ∀ j, src.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
variable {nodes : ∀ i : Fin b, src.Node last high V E w k i}
variable (r : src.NamedRun last high V E w cap keep hk nodes) (base : Format)
variable (header : WorkWords.Ports np) (leaf : P ↪ Fin np)
variable (rect : ∀ i : Fin b, V (i.val+1) = siteCapacity e (k*V i.val) (Fintype.card
    (ProgramSchemas.Seeds src last high i)))
variable (edgeRect : ∀ i : Fin b, E (i.val+1) = edgeCapacity e (k*E i.val) (Fintype.card
    (ProgramSchemas.Seeds src last high i)))
variable (fits : ∀ i : Fin b, V (i.val+1) ≤ 2^w) (hm : 0 < m)
local notation3 (prettyPrint := false) "fmt" j => ProgramSchemas.inner src last high k E np w base j
local notation3 (prettyPrint := false) "geo" j => src.StatePins last high V E w j
local notation3 (prettyPrint := false) "pins" j => Format.Output (fmt j) (geo j) (V j) w w
variable (seeds : ∀ i : Fin b, ProgramSchemas.Seeds src last high i → ℕ) (number : e.Entry → ℕ)
    (bound : ℕ → ℕ) (widths : (PortTable.mk np leaf header).Widths bits w)
    (positive : ∀ i : Fin b, 0 < bound i.val)
    (growth : ∀ i : Fin b, loadMultiplier e*(src.pattern i).record*k*bound i.val ≤ bound (i.val+1))
    (word : ∀ i : Fin b, 2*bound (i.val+1) < 2^w)
    (hookRoom : ∀ i : Fin b, HookTape.sourceRoom e (0,false)
      (loadMultiplier e*(src.pattern i).record*k*bound i.val)
      ((measured_population_cap (I := Cube D) (B := (src.pattern i).bins.Bin) e H).choose*
        ((src.pattern i).record*k*bound i.val)) < 2^w)
local notation3 (prettyPrint := false) "at₀" => NamedState.Admissible (src.NamedGood last high V E w cap keep) 0
local notation3 (prettyPrint := false) "frames" => steps r base header leaf rect edgeRect fits hm

include widths positive growth word hookRoom in
set_option maxHeartbeats 1800000 in
set_option maxRecDepth 4500 in
/-- Executing the fixed flat inner circuit on the genuine histogram returns
the complete geometry, widths and frozen chronology of the original replay. -/
theorem flat_read (flat : Fin (k^b) → at₀) (prior : ∀ i, Site.Programs (flat i).val.placed.pack.layout)
    (x : Fin (k^b) × (pins 0) → Bool)
    (start : ∀ i, Read header leaf bound 0 (fmt 0) (flat i) (prior i) (fun z => x (i,z)))
    (q : r.program.Hist flat) :
    let codec := r.program.codec r.fits
    let nested := nestedPrivatePrograms (fun z : at₀ => z.val.placed.pack) b flat prior
    let state := (flatChoice r.program.system flat).term q
    let replay := r.program.replayPrivatePrograms r.saveNames (r.privateSiteRows leaf seeds) number
      b le_rfl (leavesEquiv k _ b flat) nested q
    Read header leaf bound b (fmt b) state replay
      (fun z => (flatEpoch frames).eval (Sum.elim x (flatWord codec flat q)) (.inl z)) := by
  let read j := Read (path := src) (keep := keep) (last := last) (high := high) (cap := cap)
    (V := V) (E := E) (w := w) (Extra := Extra) header leaf bound j (fmt j)
  apply r.program.private_flat_output r.saveNames (r.privateSiteRows leaf seeds) number
    (r.program.codec r.fits) frames read _ flat prior x start q
  intro i c q prior y previous
  apply steps_read_of_node r base header leaf rect edgeRect fits hm seeds number bound i c q prior y
  exact node_read r i (fmt i.val) header leaf rect edgeRect fits hm c q prior y seeds number bound previous
    widths positive growth word (hookRoom i)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
