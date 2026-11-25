import OAI.Computability.BorderVNP.PackedFrozenNamedEmit
import OAI.Computability.BorderVNP.PackedInheritedWorkNamedKernel

/-! # Installing the actual native geometry and work pass into the full named tape node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.PublicDenseReceipt
open Shortening.StaticRows Epoch Epoch.Round Packing Packing.DirectoryCircuit Packing.CellAddressCircuit
open Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2200000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

variable {D m b k last high w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (S : Format) (header : WorkWords.Ports np) (leaf : P ↪ Fin np)

local notation3 (prettyPrint := false) "A" i => Shortening.PublicDenseReceipt.Seed (path.pattern i).bins
  (path.asPath.depth last high (Fin.val i+1))
local notation3 (prettyPrint := false) "geo" j => path.StatePins last high V E w j
local notation3 (prettyPrint := false) "ww" j => WithWidths (geo j) (V j) w
local notation3 (prettyPrint := false) "child" => S.Output (geo i.val) (V i.val) w w
local notation3 (prettyPrint := false) "input" => ((Fin k × child) ⊕ Words (A i) e.count w)
local notation3 (prettyPrint := false) "O" => r.operands i
local notation3 (prettyPrint := false) "ctx" => Shared.Context input (O).Pin (ww (i.val+1)) (k*E i.val) w
local notation3 (prettyPrint := false) "ports" => (header.nested k V i.val).parallel k (V i.val)

variable (rect : ∀ j : Fin b,V (j.val+1)=siteCapacity e (k*V j.val) (Fintype.card (ProgramSchemas.Seeds path last high j)))
variable (edgeRect : ∀ j : Fin b,E (j.val+1)=edgeCapacity e (k*E j.val) (Fintype.card (ProgramSchemas.Seeds path last high j)))
variable (fits : ∀ j : Fin b,V (j.val+1) ≤ 2^w) (hm : 0 < m)

/-- The actual width-augmented geometric step on the old geometry, work and guessed digits. -/
noncomputable def widthStep : Frame input ((ww (i.val+1)) ⊕ Unit) :=
  (r.widthNode header rect fits i).subst (Frame.initial (Sum.map (fun z => (z.1,Sum.inl z.2)) id))

/-- Prepared measured words, successor geometry and earlier work/tape on their physical pins. -/
noncomputable def source : Frame input ctx := sourceWith r i S (widthStep r i S header rect fits)

/-- The complete selected geometry, work, record tape and bank flag on the genuine step. -/
noncomputable def node : Frame input
    ((ProgramSchemas.innerRound path last high k E np w i S).Output (geo (i.val+1)) (V (i.val+1)) w w ⊕ Unit) :=
  nodeWith r i S header leaf rect edgeRect fits hm (widthStep r i S header rect fits)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
