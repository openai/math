import OAI.Computability.BorderVNP.PackedFrozenNodeEnumeration
import OAI.Computability.BorderVNP.PackedFrozenNativeReturn
import OAI.Computability.BorderVNP.PackedFrozenNamedEmitReadback
import OAI.Computability.BorderVNP.PackedFrozenMeasuredFixed
import OAI.Computability.BorderVNP.PackedFrozenFixedInstall
import OAI.Computability.BorderVNP.PackedNamedResultPresence
import OAI.Computability.BorderVNP.PackedInheritedWorkReceipt

/-! # Complete record readback on the genuine selected, measured inner node -/

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

private theorem keepPins_image {I R B V : Type} {fi : Fintype I} {w : ℕ} {f₁ f₂ : Fintype (Pins R B w)}
    {raw : @Frame I (Pins R B w) fi f₁} {schema : Schema R B} {x : I → Bool} {key : V ↪ ℕ} {program : V → Site}
    (image : schema.Image (@Frame.eval I _ fi f₁ raw x) key program) :
    schema.Image (@Frame.eval I _ fi f₂ (keepPins raw (fun z => z)) x) key program := by
  rw [keepPins_eval]
  exact image

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
    (y : Fin k → S.Output (path.StatePins last high V E w i.val) (V i.val) w w → Bool) (next : Frame
      ((Fin k × S.Output (path.StatePins last high V E w i.val) (V i.val) w w) ⊕
        Words (ProgramSchemas.Seeds path last high i) e.count w)
      (WithWidths (path.StatePins last high V E w (i.val+1)) (V (i.val+1)) w ⊕ Unit))
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
local notation3 (prettyPrint := false) "x" => (sourceWith r i S next).eval a₀
local notation3 (prettyPrint := false) "current" => r.program.advance i c q
local notation3 (prettyPrint := false) "pr" => r.program.savePrivatePrograms r.saveNames (r.privateSiteRows leaf names)
  position i c q old
local notation3 (prettyPrint := false) "result" => nodeWith r i S header leaf rect edgeRect fits hm next
local notation3 (prettyPrint := false) "format₁" => ProgramSchemas.innerRound path last high k E np w i S
local notation3 (prettyPrint := false) "sID" => siteRows e (st).input site (r.directorySeed i).toEmbedding
local notation3 (prettyPrint := false) "geom" => (nodes i).eval (Sum.elim words (NamedReceipt.word (st) (r.fits i c) q)) ∘ Sum.inl
local notation3 (prettyPrint := false) "factor" => (path.pattern i).record
local notation3 (prettyPrint := false) "T" => bound i.val
local notation3 (prettyPrint := false) "M" => InheritedBank.loadMultiplier e*factor*k*T
local notation3 (prettyPrint := false) "U" => (measured_population_cap (I := Cube D) (B := (path.pattern i).bins.Bin) e H).choose*(factor*k*T)

attribute [local irreducible] FrozenTape.Node.frame FrozenTape.Node.schema keepPins selectedPass carryFrame
  VPVNP.VerifierNetwork.Frame.eval roundSites siteRows

include previous in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 900000 in
/-- The returned program's full sparse tape is installed on its physical site
names, together with the checked geometry, private widths and exact child bank
histories. The shared masked source and the emitted records are actual gates. -/
theorem readWith (base : (PortTable.mk np leaf header).Widths bits w) (positive : 0<T)
    (room : HookTape.sourceRoom e (0,false) M U < 2^w)
    (returned : WidthRead header leaf bound (i.val+1) current pr (next.eval a₀ ∘ Sum.inl)) :
    Read header leaf bound (i.val+1) format₁ current pr ((result).eval a₀ ∘ Sum.inl) := by
  have projections : ((result).eval a₀ ∘ Sum.inl) ∘ Sum.inl = next.eval a₀ ∘ Sum.inl :=
    funext (Shared.install_widths (O) basePin next (emit r i S header leaf rect edgeRect fits hm) a₀)
  constructor
  · rw [projections]
    exact returned
  have read := selected_image r i S header leaf c q old y next bound previous
  obtain ⟨perm,dummy,ready⟩ := r.frozen_ready i c Shared.selected x read
  have incoming := old_endpoints r i S header leaf rect fits c q old y next bound previous base
  have gotCounts := count_words r i S header leaf hm c q old y next bound previous
  have childPin (j : Fin k) (z : ww i.val) : x (Shared.input (.inl (j,.inl z))) = y j (.inl z) :=
    Shared.source_input (O) basePin next a₀ (.inl (j,.inl z))
  have childProof (j : Fin k) : WidthRead header leaf bound i.val (c j) (old j)
      (x ∘ (fun z : ww i.val => Shared.input (.inl (j,.inl z)))) := by
    rw [show (x ∘ (fun z : ww i.val => Shared.input (.inl (j,.inl z)))) = y j ∘ Sum.inl from funext (childPin j)]
    exact (previous j).widths
  obtain ⟨_,hw,he,hi⟩ := frozen_node_widths i c old header leaf bound x
    (fun j z => Shared.input (.inl (j,.inl z))) childProof
  have ends := new_endpoints r i S header leaf rect edgeRect fits c q old y next names position bound previous base returned
  have used := new_occupied r i S header leaf edgeRect c q old y next names position bound returned
  let fit₁ : siteCapacity e (k*V i.val) (Fintype.card (A i)) ≤ 2^w := (rect i).symm.le.trans (fits i)
  let fit₀ : V i.val ≤ 2^w := (Nat.le_mul_of_pos_left _ hk).trans
    (rawFit e (rect i) (fits i))
  let tapePin := fun z : Fin k × FrozenTape.Pins S.Rows S.Payload w => (Shared.input (.inl (z.1,.inr z.2)) : ctx)
  have childTape (j : Fin k) : S.schema.Image (fun z => x (tapePin (j,z))) ((c j).val.names.sites.trans Fin.valEmbedding)
      (fun v => (old j v).program) := by
    rw [show (fun z => x (tapePin (j,z))) = y j ∘ Sum.inr from funext fun z =>
      Shared.source_input (O) basePin next a₀ (.inl (j,.inr z))]
    exact (previous j).tape
  have carryOk := r.carried_tape i c q S.schema fit₀ fit₁ tapePin x old childTape
  have keys := site_keys r i S header rect edgeRect fits c
  have oldKeys : (sID).trans ((Fin.castLEEmb fit₁).trans Fin.valEmbedding) = (sID).trans Fin.valEmbedding :=
    DFunLike.ext _ _ fun _ => rfl
  rw [oldKeys,← keys] at carryOk
  let pass := operands r i S hm
  have clip : InheritedHook.ComputesCuts (m := m) (mapPins Shared.selected (O).pop) (O).code (st).perm pass.cut :=
    perm.symm ▸ pass.clips
  have hp (u) : portUsed (k := k) i leaf u = true ↔ u ∈ Set.range port := decide_eq_true_iff
  let selectedStage : Stage m (path.pattern i).bins.Bin (path.asPath.depth last high (i.val+1))
      (fun j => (c j).val.placed) := st
  have image := selectedStage.frozen_node_fixed (rows := k*E i.val) (sites := k*V i.val) (n := Fintype.card (A i))
    (np := Parallel.nestedCapacity k np (i.val+1)) e q (fun j => (old j).bankFields) (S.schema.parallel k) (r.installed i c).capacity
    (mapPins Shared.selected (O).pop) (mapColumns Shared.selected (O).col) (O).code (r.directorySeed i)
    site port dummy (oldFields r i S header rect fits) (newFields r i S header rect edgeRect fits)
    Shared.literal pass.counts pass.cut (carry r i S rect fits) (oldWord r i S false) (oldWord r i S true)
    (portUsed (k := k) i leaf) (newOccupied r i S edgeRect) (fun z => (old z.1 z.2).program) (names i) position
    hm H hk (r.installed i c).measure.some x (Shared.source_literal (O) basePin next a₀) ready clip incoming ends
    used gotCounts carryOk hw he hi (fun _ => Nat.le_add_right _ _) hp (r.installed i c).records positive
    (fun j => (previous j).widths.capacity) le_rfl le_rfl room
  dsimp only [selectedStage] at image
  rw [keys] at image
  dsimp only [pass,mapColumns] at image
  have final := r.fixed_installed_tape i c q leaf names position old (format₁).schema ((emit r i S header leaf rect edgeRect fits hm).eval x)
    (rect i) (edgeRect i) (by
      unfold emit
      apply keepPins_image
      have schemaEq : (format₁).schema = FrozenTape.Node.schema e (0,false) («A» := A i)
          (S.schema.parallel k) (k*E i.val) (Parallel.nestedCapacity k np (i.val+1)) w := by
        dsimp only [ProgramSchemas.innerRound,Format.round,Format.ofSchema,ProgramSchemas.Seeds]
        exact congrArg (fun ft : Fintype (A i) => @FrozenTape.Node.schema D m K _ e (0,false) (A i) ft _ _
          (S.schema.parallel k) (k*E i.val) (Parallel.nestedCapacity k np (i.val+1)) w) (Subsingleton.elim _ _)
      rw [schemaEq]
      dsimp only [SourcePath.namedView,SourcePath.NamedRun.resultCableRows]
      exact FrozenTape.Node.image_enumeration (l := (operands r i S hm).counts) (r := (operands r i S hm).counts) HEq.rfl image)
  have out : ((result).eval a₀ ∘ Sum.inl) ∘ Sum.inr = (emit r i S header leaf rect edgeRect fits hm).eval x :=
    funext (Shared.install_tape (O) basePin next (emit r i S header leaf rect edgeRect fits hm) a₀)
  rw [out]
  exact final

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
