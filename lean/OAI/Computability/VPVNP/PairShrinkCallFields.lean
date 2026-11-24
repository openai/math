import OAI.Computability.VPVNP.PairSimulationMapCallArg
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.CompressorShrinkTermSelection

/-!
# The descriptor words of a resident six-party map

The selected term supplies its copy count and the eight payload widths.
The dense two-column demand array supplies AB and CD. Each absorbed role
reads its single shared private slot. The surviving roles read the buffers
assembled from subdivision frames. The CD endpoints read the stored old
half-wire directly, and AB reads its assembled bundle slice.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallFields

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe
open Compression Compression.PackingData Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion
open scoped Fin.CommRing

/-- One descriptor slot of the map evaluator, indexed by a demand edge or one of the eight
supply roles where needed. -/
abbrev Arg := MapCallSetup.Arg Bool (Bool × Fin 4)
/-- A source or target half of a demand edge or supply role whose field buffer the six-party
map can read. -/
abbrev Endpoint := MapLookup.LabelField Bool (Bool × Fin 4)

/-- The eight surviving endpoint staging intervals follow the single AB interval.
Every absolute absorbed role has its own earlier interval, shared by its ends. -/
structure Scratch where
  /-- First private word reserved for absorbed supply labels shared by their two endpoints. -/
  hidden : ℕ
  /-- Number of private words reserved for each shared or staged field. -/
  stride : ℕ
  /-- Number of motifs for which the hidden pass reserves four shared field intervals apiece. -/
  motifs : ℕ
  /-- Private base address of the label histogram updated by the map evaluator. -/
  hist : ℕ

/-- Base of the AB buffer, immediately after the four shared intervals for each motif. -/
def Scratch.staging (s : Scratch) := s.hidden + 4 * s.motifs * s.stride

/-- Base of absorbed role `t`'s shared label in the four-field block for motif `ordinal`. -/
def Scratch.shared (s : Scratch) (ordinal : ℕ) (t : Fin 4) :=
  s.hidden + (ordinal * 4 + t.val) * s.stride

/-- Base of role `t`'s staged surviving field at the chosen source or target end. -/
def Scratch.surviving (s : Scratch) (dir : Bool) (t : Fin 4) :=
  s.staging + (1 + dir.toNat * 4 + t.val) * s.stride

/-- Base of the lookup directory after the AB interval and the eight surviving endpoint
intervals. -/
def Scratch.directory (s : Scratch) := s.staging + 9 * s.stride
/-- Base of the map descriptor following the sixteen directory words. -/
def Scratch.descriptor (s : Scratch) := s.directory + 16
/-- Start of the source-copy indices immediately after the complete descriptor. -/
def Scratch.source (s : Scratch) := s.descriptor + Fintype.card Arg
/-- Start of the target-copy indices after all source-copy indices. -/
def Scratch.target (s : Scratch) (copies : ℕ) := s.source + copies

/-- The source party of a demand edge for an outgoing field and its target party for an
incoming field. -/
def demandParty (dir e : Bool) := if dir then demandTarget e else demandSource e

/-- The party incident to the specified supply role at its outgoing or incoming end. -/
def supplyParty (dir : Bool) (e : Bool × Fin 4) := if dir then supply.dst e else supply.src e

/-- Locate the endpoint at party `j` in its old CD, staged AB, surviving, or shared buffer. An
absent endpoint uses address zero. -/
def Scratch.fieldBase (s : Scratch) (ordinal : ℕ) (j : Fin 6) (layout : Bool)
    (cd : Bool → ℕ) : Endpoint → ℕ
  | .inl (dir, e) => if j = demandParty dir e then (if e then cd dir else s.staging) else 0
  | .inr (dir, e) => if j = supplyParty dir e then
      (if e.1 = layout then s.surviving dir e.2 else s.shared ordinal e.2) else 0

/-- Live operands: the canonical level header, the dense motif ordinal, the
private arena and the old CD source or target computed from its physical row. -/
structure Inputs where
  /-- Register expression for the producing level header from which the map loads its published
  addresses. -/
  level : Expr
  /-- Register expression for the selected motif number in the dense ordering. -/
  ordinal : Expr
  /-- Expression for the base of the shared absorbed-role buffers. -/
  hidden : Expr
  /-- Expression for the allocated width of each shared or staged buffer. -/
  stride : Expr
  /-- Expression for the number of motifs represented in the shared buffers. -/
  motifs : Expr
  /-- Expression for the private histogram base used to count selected map labels. -/
  hist : Expr
  /-- Expressions for the old CD half-wire buffers at the source and target of the demand edge. -/
  cd : Bool → Expr

namespace Inputs

/-- Load the word at a fixed offset from the producing level header. -/
def loadHead (I : Inputs) (offset : ℕ) : Expr := .load (I.level.add (.lit offset))

/-- Compute this motif’s term-row address using the published term base, row stride and dense
ordinal. -/
def term (I : Inputs) := (I.loadHead 36).add (I.ordinal.mul (I.loadHead 37))
/-- Read the copy count from the second word of the selected term row. -/
def copies (I : Inputs) := Expr.load ((I.term).add (.lit 1))
/-- Read the selected shrinking layout bit from offset 38 of the level header. -/
def layout (I : Inputs) := I.loadHead 38
/-- Load the AB or CD demand width in the two-word row for this motif. -/
def demand (I : Inputs) (e : Bool) :=
  Expr.load (((I.loadHead 47).add ((Expr.lit 2).mul I.ordinal)).add (.lit e.toNat))

/-- Load the selected payload width at the recorded role index after the two leading term
words. -/
def payload (I : Inputs) (e : Bool × Fin 4) :=
  Expr.load (((I.term).add (.lit 2)).add (.lit (ShrinkSliceArrays.supplyRoles.symm e).val))

/-- Compute the start of the AB staging interval beyond the four shared buffers for every
motif. -/
def staging (I : Inputs) := I.hidden.add (((Expr.lit 4).mul I.motifs).mul I.stride)
/-- Compute the shared buffer address for absorbed role `t` of the current motif. -/
def shared (I : Inputs) (t : Fin 4) :=
  I.hidden.add (((I.ordinal.mul (.lit 4)).add (.lit t.val)).mul I.stride)
/-- Compute the staged buffer address for one of four surviving roles at the selected source or
target end. -/
def surviving (I : Inputs) (dir : Bool) (t : Fin 4) :=
  I.staging.add ((Expr.lit (1 + dir.toNat * 4 + t.val)).mul I.stride)
/-- Compute the lookup directory address after the nine staging intervals. -/
def directory (I : Inputs) := I.staging.add ((Expr.lit 9).mul I.stride)
/-- Compute the descriptor address immediately after the sixteen directory words. -/
def descriptor (I : Inputs) := I.directory.add (.lit 16)
/-- Compute the start of the source-copy indices after the descriptor slots. -/
def source (I : Inputs) := I.descriptor.add (.lit (Fintype.card Arg))

/-- Selecting between the two field addresses works in the machine-word ring. -/
def select (bit yes no : Expr) := no.add ((yes.sub no).mul bit)

/-- Build the register expression selecting the actual input buffer for an incident endpoint,
using the recorded layout for supply roles. -/
def base (I : Inputs) (j : Fin 6) : Endpoint → Expr
  | .inl (dir, e) => if j = demandParty dir e then (if e then I.cd dir else I.staging) else .lit 0
  | .inr (dir, e) => if j = supplyParty dir e then
      if e.1 then select I.layout (I.surviving dir e.2) (I.shared e.2)
      else select I.layout (I.shared e.2) (I.surviving dir e.2)
    else .lit 0

/-- Supply each descriptor slot of the selected party with its buffer address, size, copy count
or histogram pointer. -/
def fields (I : Inputs) (j : Fin 6) : Arg → Expr
  | .base f => I.base j f
  | .demand e => I.demand e
  | .payload e => I.payload e
  | .copies => I.copies
  | .directory => I.directory
  | .source => I.source
  | .target => I.source.add I.copies
  | .hist => I.hist

end Inputs

variable {w a g : ℕ} (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w)
variable (X : State a (packingLaneBits a g))
variable {k : Type*} [_root_.Field k] {factor : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (selection : X.ShrinkSelection F) (m : X.packingData.Motif)
local notation "MIdx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "BW" => X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m
local notation "ev" => Expr.eval pub state mem

/-- Readback equations identifying the live register expressions and published header cells
with the selected motif, layout, term row and scratch allocation. -/
structure Stored (I : Inputs) (s : Scratch) (term dense : Word w) (step : ℕ)
    (layout : Bool) (cd : Bool → ℕ) : Prop where
  ordinal : ev I.ordinal = (MIdx : Word w)
  hidden : ev I.hidden = (s.hidden : Word w)
  stride : ev I.stride = (s.stride : Word w)
  motifs : ev I.motifs = (s.motifs : Word w)
  hist : ev I.hist = (s.hist : Word w)
  termBase : ev (I.loadHead 36) = term
  termStride : ev (I.loadHead 37) = (step : Word w)
  layout : ev I.layout = (layout.toNat : Word w)
  denseBase : ev (I.loadHead 47) = dense
  cd : ∀ dir, ev (I.cd dir) = (cd dir : Word w)

open scoped Classical in
/-- The descriptor word at each argument slot for a given motif and party, using the selected
payload widths and fixed block repetition count. -/
noncomputable def values (s : Scratch) (j : Fin 6) (layout : Bool) (cd : Bool → ℕ) : Arg → Word w
  | .base f => s.fieldBase MIdx j layout cd f
  | .demand e => BW e
  | .payload e => (selection m).val e
  | .copies => repetitions F BW
  | .directory => s.directory
  | .source => s.source
  | .target => s.target (repetitions F BW)
  | .hist => s.hist

private theorem cast_val (v : Word w) : (v.val : Word w) = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)

private theorem word_of_val {v : Word w} {n : ℕ} (h : v.val = n) : v = (n : Word w) :=
  h ▸ (cast_val v).symm

variable {pub state mem X F selection m}
variable (I : Inputs) (s : Scratch) (term dense : Word w) (step : ℕ) (layout : Bool) (cd : Bool → ℕ)
variable (h : Stored pub state mem X m I s term dense step layout cd)

include h in
private theorem staging_eval : ev I.staging = (s.staging : Word w) := by
  simp only [Inputs.staging, Scratch.staging, Expr.add, Expr.mul, Expr.eval, BinaryOp.eval,
    h.hidden, h.motifs, h.stride, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

include h in
private theorem base_eval (j : Fin 6) (f : Endpoint) :
    ev (I.base j f) = (s.fieldBase MIdx j layout cd f : Word w) := by
  have stage := staging_eval I s term dense step layout cd h
  have shared (t : Fin 4) : ev (I.shared t) = (s.shared MIdx t : Word w) := by
    simp only [Inputs.shared, Scratch.shared, Expr.add, Expr.mul, Expr.eval, BinaryOp.eval,
      h.ordinal, h.hidden, h.stride, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have surv (dir : Bool) (t : Fin 4) : ev (I.surviving dir t) = (s.surviving dir t : Word w) := by
    change ev I.staging + ((1 + dir.toNat * 4 + t.val : ℕ) : Word w) * ev I.stride = _
    rw [stage, h.stride, ← Nat.cast_mul, ← Nat.cast_add]
    rfl
  rcases f with ⟨dir, e⟩ | ⟨dir, side, t⟩
  · by_cases party : j = demandParty dir e
    · cases e <;> simp [Inputs.base, Scratch.fieldBase, party, stage, h.cd]
    · simp [Inputs.base, Scratch.fieldBase, party, Expr.eval]
  · by_cases party : j = supplyParty dir (side, t)
    · cases side <;> cases layout <;> simp [Inputs.base, Scratch.fieldBase, party, Inputs.select,
        Expr.add, Expr.sub, Expr.mul, Expr.eval, BinaryOp.eval, h.layout, shared, surv]
    · simp [Inputs.base, Scratch.fieldBase, party, Expr.eval]

include h in
open scoped Classical in
/-- Every word to be written into the native call descriptor is read from the
chosen term, the true CD/AB demand record, or its designated private region. -/
theorem fields_eval
    (pair : ShrinkTermInputs.statePairs X dense mem)
    (fields : TermRecordScan.Fields F ShrinkSliceArrays.supplyRoles demandMass_pos BW
      (selection m).val (ShrinkTermSelection.rowBase X term step m) mem)
    (dfit : dense.val + 2 * MIdx + 1 < 2 ^ w)
    (tfit : term.val + MIdx * step + 9 < 2 ^ w)
    (j : Fin 6) (arg : Arg) :
    ev (I.fields j arg) = values X F selection m s j layout cd arg := by
  let n := term.val + MIdx * step
  let row := ShrinkTermSelection.rowBase X term step m
  have hr : row.val = n := Nat.mod_eq_of_lt (by omega)
  have tr : ev I.term = (n : Word w) := by
    change ev (I.loadHead 36) + ev I.ordinal * ev (I.loadHead 37) = _
    rw [h.termBase, h.ordinal, h.termStride, ← cast_val term, ← Nat.cast_mul, ← Nat.cast_add]
  have copies : ev I.copies = ((repetitions F BW : ℕ) : Word w) := by
    change mem (ev I.term + 1).val = _
    rw [tr, ← Nat.cast_add_one, show ((n + 1 : ℕ) : Word w).val = n + 1 from
      Nat.mod_eq_of_lt (by omega)]
    exact word_of_val (hr ▸ fields.2.1)
  have dir : ev I.directory = (s.directory : Word w) := by
    change ev I.staging + 9 * ev I.stride = _
    rw [staging_eval I s term dense step layout cd h, h.stride]
    simp [Scratch.directory]
  have src : ev I.source = (s.source : Word w) := by
    change (ev I.directory + 16) + (Fintype.card Arg : Word w) = _
    rw [dir]
    simp [Scratch.source, Scratch.descriptor]
  cases arg with
  | base f => exact base_eval I s term dense step layout cd h j f
  | copies => exact copies
  | directory => exact dir
  | source => exact src
  | hist => exact h.hist
  | target =>
    change ev I.source + ev I.copies = _
    rw [src, copies, ← Nat.cast_add]
    rfl
  | payload e =>
    let i := ShrinkSliceArrays.supplyRoles.symm e
    have data := fields.2.2 i
    rw [Equiv.apply_symm_apply] at data
    change mem ((ev I.term + 2) + (i.val : Word w)).val = _
    have fit : n + 2 + i.val < 2 ^ w := by have := i.isLt; dsimp [n]; omega
    have cell : ((n : Word w) + 2 + (i.val : Word w)).val = n + 2 + i.val := by
      change ((n : Word w) + ((2 : ℕ) : Word w) + (i.val : Word w)).val = _
      rw [← Nat.cast_add, ← Nat.cast_add]
      exact Nat.mod_eq_of_lt fit
    rw [tr, cell]
    exact word_of_val (hr ▸ data)
  | demand e =>
    have pp := pair m
    change mem ((ev (I.loadHead 47) + 2 * ev I.ordinal) + (e.toNat : Word w)).val =
      ((BW e : ℕ) : Word w)
    rw [h.denseBase, h.ordinal, ← cast_val dense]
    change mem (((dense.val : Word w) + ((2 : ℕ) : Word w) * (MIdx : Word w)) +
      (e.toNat : Word w)).val = _
    rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add]
    cases e
    · rw [Bool.toNat_false, Nat.add_zero, Fin.val_natCast,
        Nat.mod_eq_of_lt (show dense.val + 2 * MIdx < 2 ^ w by omega)]
      exact word_of_val pp.1
    · rw [Bool.toNat_true, Fin.val_natCast, Nat.mod_eq_of_lt dfit]
      exact word_of_val pp.2

end PairSimulation.ShrinkCallFields

end VPVNP
end Computability
end OAI
