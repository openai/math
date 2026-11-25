import OAI.Computability.BorderVNP.PackedFrozenNamedKernel

/-! # Scheduling the complete native tape on the named inner history

The native node takes the current cumulative format and the actual histogram
digits. Reindexing its outputs to the successor format and its guess pins to
the named codec adds no gates. All inner children use their own history bits.
-/

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
local notation3 (prettyPrint := false) "guesses" => Pin (Cube D) (fun i => (src.pattern i).bins.Bin)
  (src.asPath.depth last high) e.count (fun _ => w)
local notation3 (prettyPrint := false) "native" i => node r i (fmt (Fin.val i)) header leaf rect edgeRect fits hm

/-- Reuse the node's gates on the named codec's count pins and the recursively
specified successor format. -/
noncomputable def steps : Steps k b (fun j => pins j) guesses := fun j hj =>
  let i : Fin b := ⟨j,hj⟩
  let same := ProgramSchemas.inner_next src last high k E np w base i
  let back := cast (congrArg (fun F : Format => F.Output (geo (j+1)) (V (j+1)) w w) same)
  scheduled (native i) (pinEquiv (I := Cube D) (B := fun t => (src.pattern t).bins.Bin)
    (depth := src.asPath.depth last high) (e := e) (fun _ => w) i) back

/-- Neither change of names adds a gate to the actual full node. -/
theorem steps_size (i : Fin b) :
    (steps r base header leaf rect edgeRect fits hm i.val i.isLt).size = (native i).size :=
  scheduled_size ..

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
