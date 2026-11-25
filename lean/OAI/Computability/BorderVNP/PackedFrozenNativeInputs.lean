import OAI.Computability.BorderVNP.PackedFrozenNamedEmit
import OAI.Computability.BorderVNP.PackedFrozenNamedReady
import OAI.Computability.BorderVNP.PackedFrozenNamedRead
import OAI.Computability.BorderVNP.PackedFrozenOldPorts
import OAI.Computability.BorderVNP.PackedFrozenNamedWidths

/-! # Actual child wires, clipping operands and normalized old incidence fields of the joint native node -/

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
variable (fits : ∀ j : Fin b,V (j.val+1) ≤ 2^w) (hm : 0 < m)
variable (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e) (old : ∀ j,Site.Programs (c j).val.placed.pack.layout)
    (y : Fin k → S.Output (path.StatePins last high V E w i.val) (V i.val) w w → Bool) (next : Frame
      ((Fin k × S.Output (path.StatePins last high V E w i.val) (V i.val) w w) ⊕
        Words (ProgramSchemas.Seeds path last high i) e.count w)
      (WithWidths (path.StatePins last high V E w (i.val+1)) (V (i.val+1)) w ⊕ Unit))
    (bound : ℕ → ℕ) (previous : ∀ j, Read header leaf bound i.val S (c j) (old j) (y j))
local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "p" => raw (fun j => (c j).val.placed)
local notation3 (prettyPrint := false) "site" => parallelName (fun j => (c j).val.names.sites)
local notation3 (prettyPrint := false) "slot" => (st).slot.trans (finCongr (r.installed i c).capacity).toEmbedding
local notation3 (prettyPrint := false) "port" => Parallel.nestedPorts k leaf (i.val+1)
local notation3 (prettyPrint := false) "words" => (fun z : Fin k × geo i.val => (c z.1).val.words z.2)
local notation3 (prettyPrint := false) "basePin" => geoPin (path := path) (last := last) (high := high)
  (V := V) (E := E) (w := w) (k := k) i S

/-- Canonical old child arrays and actual histogram words used in the physical node. -/
noncomputable def assignment : input → Bool :=
  Sum.elim (fun z => y z.1 z.2) (NamedReceipt.word (st) (r.fits i c) q)

local notation3 (prettyPrint := false) "a₀" => assignment r i S c q y
local notation3 (prettyPrint := false) "x" => (sourceWith r i S next).eval a₀
local notation3 (prettyPrint := false) "x₀" => (Shared.front (O) basePin next).eval a₀

include previous in
/-- The projection used by the selected front reads exactly the child's certified geometric output. -/
theorem input_geometry : a₀ ∘ basePin = words := funext fun z => congrFun (previous z.1).widths.geometry z.2

include previous in
/-- The complete shared input contains the very selected population frame for these true children. -/
theorem selected_image : x ∘ Shared.selected = (O).frame.eval words := by
  have hg := input_geometry r i S header leaf c q old y bound previous
  funext z
  exact (Shared.source_selected (O) basePin next a₀ z).trans (congrArg (fun u => (O).frame.eval u z) hg)

include previous in
/-- The native pre-stage has one represented old endpoint directory. All old
holes now read as zero-width rows, including those with an arbitrary unused
population width in the measured frame. -/
theorem old_endpoints (base : (PortTable.mk np leaf header).Widths bits w) :
    Views.EndpointData (p).layout (oldFields r i S header rect fits) site slot port x := by
  have hg := input_geometry r i S header leaf c q old y bound previous
  have read : x₀ ∘ Shared.operand = (O).frame.eval words := by
    funext z
    change (Shared.front (O) basePin next).eval a₀ (.inr (.inl z)) = _
    simp only [Shared.front,Frame.withInput_eval_inr,parallelFrame_eval_inl,Frame.subst_eval]
    have h := funext fun u => Frame.initial_eval basePin a₀ u
    rw [show (Frame.initial basePin).eval a₀ = a₀ ∘ basePin from h,hg]
  obtain ⟨_,dummy,ready⟩ := r.frozen_ready i c Shared.operand x₀ read
  let oldPorts := Parallel.nestedPorts k leaf i.val
  have widths₀ := header.nested_widths leaf k V base i.val
  have before := Ports.raw_parallel (fun j => (c j).val.placed) (fun j => (c j).val.names.sites) oldPorts oldHeader
    (fun j => (previous j).widths.ports) widths₀
  have got := OldFields.represented (mapPins Shared.operand (O).pop) (mapColumns Shared.operand (O).col)
    (rawFit e (rect i) (fits i))
    (nextHeader).host (nextHeader).width e p (st).bin (st).positive (O).code (r.directorySeed i) site slot port
    dummy x₀ ready before.attach before.size (widths₀.parallel k (V i.val)).fit before.hole
  have mask : x = (OldFields.frame (mapPins Shared.operand (O).pop) (mapColumns Shared.operand (O).col)).eval x₀ := by
    funext z; exact Frame.subst_eval _ _ _ _
  rw [mask]
  exact got

include previous in
/-- On these actual inputs the selected counts give both the measured block
number and the separate multiplicity of each entry of the true histogram. -/
theorem count_words (a : A i) (u : Option (Fin e.count)) :
    value (fun j => (operands r i S hm).counts.eval x (a,u,j)) = u.elim ((st).matched a) (q a).val := by
  have read := selected_image r i S header leaf c q old y next bound previous
  obtain ⟨perm,_,ready⟩ := r.frozen_ready i c Shared.selected x read
  have mul : 0 < widthMultiplier e := by unfold widthMultiplier; omega
  have hits := (operands r i S hm).histogram (p).layout (st).bin slot x ready.population
    (fun b => (Nat.le_mul_of_pos_left _ mul).trans_lt (ready.room b))
  cases u with
  | none => simpa only [Option.elim_none,Stage.matched_eq,perm] using hits.1 a
  | some u =>
    have eqn : (fun j => (operands r i S hm).counts.eval x (a,some u,j)) =
        fun j => NamedReceipt.word (st) (r.fits i c) q (a,u,j) := by
      funext j
      exact (hits.2 a u j).trans (Shared.source_input (O) basePin next a₀ (.inr (a,u,j)))
    rw [eqn]
    exact (NamedReceipt.word_value (st) (r.fits i c) q a u).symm

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
