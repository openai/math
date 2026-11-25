import OAI.Computability.BorderVNP.PackedFrozenNativeImage
import OAI.Computability.BorderVNP.PackedFrozenNamedKernel
import OAI.Computability.BorderVNP.PackedInheritedWorkNamed

/-! # The complete saved state of the native geometry, work and record-tape node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.PublicDenseReceipt
open Shortening.StaticRows Epoch Epoch.Round Packing Packing.DirectoryCircuit Packing.CellAddressCircuit
open Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1600000

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
local notation3 (prettyPrint := false) "oldHeader" => header.nested k V i.val
local notation3 (prettyPrint := false) "nextHeader" => (oldHeader).parallel k (V i.val)
variable (rect : ∀ j : Fin b,V (j.val+1)=siteCapacity e (k*V j.val) (Fintype.card (ProgramSchemas.Seeds path last high j)))
variable (edgeRect : ∀ j : Fin b,E (j.val+1)=edgeCapacity e (k*E j.val) (Fintype.card (ProgramSchemas.Seeds path last high j)))
variable (fits : ∀ j : Fin b,V (j.val+1) ≤ 2^w) (hm : 0 < m)
variable (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e) (old : ∀ j,Site.Programs (c j).val.placed.pack.layout)
    (y : Fin k → S.Output (path.StatePins last high V E w i.val) (V i.val) w w → Bool)
    (names : ∀ j : Fin b, ProgramSchemas.Seeds path last high j → ℕ) (position : e.Entry → ℕ)
    (bound : ℕ → ℕ) (previous : ∀ j, Read header leaf bound i.val S (c j) (old j) (y j))
local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "p" => raw (fun j => (c j).val.placed)
local notation3 (prettyPrint := false) "site" => parallelName (fun j => (c j).val.names.sites)
local notation3 (prettyPrint := false) "slot" => (st).slot.trans (finCongr (r.installed i c).capacity).toEmbedding
local notation3 (prettyPrint := false) "port" => Parallel.nestedPorts k leaf (i.val+1)
local notation3 (prettyPrint := false) "words" => (fun z : Fin k × geo i.val => (c z.1).val.words z.2)
local notation3 (prettyPrint := false) "basePin" => geoPin (path := path) (last := last) (high := high)
  (V := V) (E := E) (w := w) (k := k) i S

local notation3 (prettyPrint := false) "a₀" => assignment r i S c q y
local notation3 (prettyPrint := false) "current" => r.program.advance i c q
local notation3 (prettyPrint := false) "pr" => r.program.savePrivatePrograms r.saveNames (r.privateSiteRows leaf names)
  position i c q old
local notation3 (prettyPrint := false) "result" => node r i S header leaf rect edgeRect fits hm
local notation3 (prettyPrint := false) "format₁" => ProgramSchemas.innerRound path last high k E np w i S
local notation3 (prettyPrint := false) "sID" => siteRows e (st).input site (r.directorySeed i).toEmbedding
local notation3 (prettyPrint := false) "geom" => (nodes i).eval (Sum.elim words (NamedReceipt.word (st) (r.fits i c) q)) ∘ Sum.inl
local notation3 (prettyPrint := false) "factor" => (path.pattern i).record
local notation3 (prettyPrint := false) "T" => bound i.val
local notation3 (prettyPrint := false) "M" => InheritedBank.loadMultiplier e*factor*k*T
local notation3 (prettyPrint := false) "U" => (measured_population_cap (I := Cube D) (B := (path.pattern i).bins.Bin) e H).choose*(factor*k*T)

include previous in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
/-- Every attained histogram receives the actual geometry, both physical width
columns, and every ordered row of each true saved private program. -/
theorem node_read (base : (PortTable.mk np leaf header).Widths bits w)
    (positive : ∀ j : Fin b,0<bound j.val)
    (growth : ∀ j : Fin b, InheritedBank.loadMultiplier e*(path.pattern j).record*k*bound j.val ≤ bound (j.val+1))
    (word : ∀ j : Fin b,2*bound (j.val+1)<2^w)
    (room : HookTape.sourceRoom e (0,false) M U < 2^w) :
    Read header leaf bound (i.val+1) format₁ current pr ((result).eval a₀ ∘ Sum.inl) := by
  let prior := fun j : Fin k => y j ∘ Sum.inl
  have hw := r.widthNode_read header leaf rect fits names position bound base positive growth word i c q old prior
    (fun j => (previous j).widths)
  let select : ((Fin k × ww i.val) ⊕ Words (A i) e.count w) → input :=
    Sum.map (fun z => (z.1,Sum.inl z.2)) id
  let oldWords := Sum.elim (fun z : Fin k × ww i.val => prior z.1 z.2) (NamedReceipt.word (st) (r.fits i c) q)
  have assigned : (Frame.initial select).eval a₀ = oldWords := by
    funext z
    cases z <;> exact Frame.initial_eval select a₀ _
  have equal : (widthStep r i S header rect fits).eval a₀ ∘ Sum.inl = (r.widthNode header rect fits i).eval oldWords ∘ Sum.inl := by
    funext z
    exact (Frame.subst_eval _ _ _ _).trans (congrArg (fun y => (r.widthNode header rect fits i).eval y (.inl z)) assigned)
  apply readWith r i S header leaf rect edgeRect fits hm c q old y (widthStep r i S header rect fits)
    names position bound previous base (positive i) room
  rw [equal]
  exact hw

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
