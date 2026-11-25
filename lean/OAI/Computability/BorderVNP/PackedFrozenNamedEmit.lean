import OAI.Computability.BorderVNP.PackedFrozenSharedNode
import OAI.Computability.BorderVNP.PackedInheritedWorkReturn
import OAI.Computability.BorderVNP.PackedNamedPortHeaders
import OAI.Computability.BorderVNP.PackedFrozenProgramSchemas
import OAI.Computability.BorderVNP.PackedNamedResultFields

/-! # The complete native record kernel for an inner shortening node

All pins, clipping and count circuits, shared endpoint fields, old record
rekeying and fresh row writers are fixed by the schedule and node before
the selected children or histogram are known.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.PublicDenseReceipt
open Shortening.StaticRows Epoch Epoch.Round Packing Packing.DirectoryCircuit Packing.CellAddressCircuit
open Packing.Inherited Packing.Inherited.FrozenTape Packing.Inherited.WorkWords VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 600000
set_option maxRecDepth 4000

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

/-- Projection of the true old child geometry, before any histogram. -/
def geoPin (z : Fin k × geo i.val) : input := .inl (z.1,.inl (.inl z.2))

/-- The complete shared prepared context used by the record emitters. -/
noncomputable def sourceWith (next : Frame
      ((Fin k × S.Output (path.StatePins last high V E w i.val) (V i.val) w w) ⊕
        Words (ProgramSchemas.Seeds path last high i) e.count w)
      (WithWidths (path.StatePins last high V E w (i.val+1)) (V (i.val+1)) w ⊕ Unit)) : Frame input ctx :=
  Shared.source (O) (geoPin (path := path) (last := last) (high := high) (V := V) (E := E) (w := w) (k := k) i S)
    next

/-- The merged old site rectangle is a literal initial interval of the current physical sites. -/
theorem rawFit {D m old seeds output w : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
    (rect : output = siteCapacity e old seeds) (fit : output ≤ 2^w) : old ≤ 2^w :=
  (Nat.le_add_right old (seeds*Fintype.card (TemplateSite e))).trans (rect.symm.le.trans fit)

/-- The true old work width or complete staged extent at the flattened child row. -/
noncomputable def oldWord (extent : Bool) : Fin (k*V i.val) → Fin w → ctx :=
  fun row j =>
    let a := finProdFinEquiv.symm row
    Shared.input (.inl (a.1,.inl (.inr (a.2,extent,j))))

/-- The exposed selected populations and the checked histogram digits drive the one fixed pass. -/
noncomputable def operands := selectedPass e (O) (Shared.selected (X := input) (Z := ww (i.val+1)) (rows := k*E i.val) (w := w))
  (fun a u j => Shared.input (.inr (a,u,j))) hm

/-- Every old local record is routed from its genuine child tape and old physical owner key. -/
noncomputable def carry : Frame ctx (FrozenTape.Pins (Fin k × S.Rows) (Fin k × S.Payload) w) :=
  let fit := rawFit e (rect i) (fits i)
  carryFrame ((Nat.le_mul_of_pos_left _ hk).trans fit) fit (fun z => Shared.input (.inl (z.1,.inr z.2)))

/-- The old widths are masked by measured occupancy and the fixed ports use their true grouped headers. -/
noncomputable def oldFields : Fields (k*V i.val) (k*E i.val) (Parallel.nestedCapacity k np (i.val+1)) 1 w 0 w ctx := OldFields.fields
  (mapColumns (Shared.operand (X := input) (Z := ww (i.val+1))) (O).col)
  (rawFit e (rect i) (fits i)) (ports).host (ports).width

/-- Select the actually returned geometry or the shared constant bit. -/
def resultPin : ((geo (i.val+1)) ⊕ Bool) → ctx := Sum.elim (Shared.widths ∘ Sum.inl) Shared.literal

/-- Successor incidence fields in the exact fixed site/cable rectangles. -/
noncomputable def newFields : Fields (siteCapacity e (k*V i.val) (Fintype.card (A i)))
    (edgeCapacity e (k*E i.val) (Fintype.card (A i))) (Parallel.nestedCapacity k np (i.val+1)) 1 w 0 w ctx :=
  let pin := fun z : Shortening.PublicEndpoints.Inputs
    (Cover.AddressCircuit.ProductSlots (Fintype.card (Cube D)) (path.asPath.depth last high (i.val+1)+1) ⊕ ↥(path.catalog (i.val+1)))
    (V (i.val+1)) (E (i.val+1)) w w => (Sum.inr (Sum.inr z) : geo (i.val+1))
  @Ports.sharedResultFields (Parallel.nestedCapacity k np (i.val+1)) (V (i.val+1)) (E (i.val+1))
    (siteCapacity e (k*V i.val) (Fintype.card (A i))) (edgeCapacity e (k*E i.val) (Fintype.card (A i))) w
    (Cover.AddressCircuit.ProductSlots (Fintype.card (Cube D)) (path.asPath.depth last high (i.val+1)+1) ⊕ ↥(path.catalog (i.val+1)))
    (geo (i.val+1)) ctx ports (fits i) pin (rect i) (edgeRect i) (resultPin r i S)

/-- Actual output-present wire for each slot of the static sewn cable rectangle. -/
noncomputable def newOccupied (a : Fin (edgeCapacity e (k*E i.val) (Fintype.card (A i)))) : ctx :=
  let row : Fin (E (i.val+1)) := Fin.cast (edgeRect i).symm a
  let pin : geo (i.val+1) := Sum.inl row
  let get : ((geo (i.val+1)) ⊕ Bool) → ctx := resultPin r i S
  get (Sum.inl pin)

/-- Static membership of a grouped exterior port in the occupied physical directory. -/
noncomputable def portUsed (u : Fin (Parallel.nestedCapacity k np (i.val+1))) :=
  decide (u ∈ Set.range (Parallel.nestedPorts k leaf (i.val+1)))

/-- Select the scheduled output coordinates using the native frame's existing finite enumeration. -/
noncomputable def keepPins {I Old New : Type} {fi : Fintype I} {fo : Fintype Old} [fn : Fintype New]
    (f : @Frame I Old fi fo) (wire : New → Old) : @Frame I New fi fn := @Frame.select I Old New fi fo fn f wire

/-- The four actual chronological record writers operating on one prepared assignment. -/
noncomputable def emit : Frame ctx (FrozenTape.Pins
    (ProgramSchemas.innerRound path last high k E np w i S).Rows (ProgramSchemas.innerRound path last high k E np w i S).Payload w) :=
  let raw := FrozenTape.Node.frame (D := D) (m := m) (s := k*V i.val) (old := k*E i.val) (n := Fintype.card (A i))
    (np := Parallel.nestedCapacity k np (i.val+1)) (C := 1) (C' := siteCapacity e (k*V i.val) (Fintype.card (A i)))
    (d := w) (d' := w) (k := 0) (k' := w) (w := w) («A» := A i) (σ := ctx)
    (R := Fin k × S.Rows) (B := Fin k × S.Payload) e (0,false) hm (r.directorySeed i).toEmbedding (carry r i S rect fits)
    (oldFields r i S header rect fits) (Views.literalFields (newFields r i S header rect edgeRect fits) Shared.literal)
    (operands r i S hm).cut (operands r i S hm).counts (oldWord r i S false) (oldWord r i S true)
    (Shared.selected ∘ (O).col.occupied) (portUsed (k := k) i leaf) (newOccupied r i S edgeRect)
  keepPins raw (fun z => z)


/-- Full checked inner step, including every saved public geometry/work bit, all frozen
record bits and the very same bank acceptance flag. -/
noncomputable def nodeWith (next : Frame
      ((Fin k × S.Output (path.StatePins last high V E w i.val) (V i.val) w w) ⊕
        Words (ProgramSchemas.Seeds path last high i) e.count w)
      (WithWidths (path.StatePins last high V E w (i.val+1)) (V (i.val+1)) w ⊕ Unit)) : Frame input
    ((ProgramSchemas.innerRound path last high k E np w i S).Output (geo (i.val+1)) (V (i.val+1)) w w ⊕ Unit) :=
  Shared.install (O) (geoPin (path := path) (last := last) (high := high) (V := V) (E := E) (w := w) (k := k) i S)
    next (emit r i S header leaf rect edgeRect fits hm)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun.NativeTape

end BorderVNP
end Computability
end OAI
