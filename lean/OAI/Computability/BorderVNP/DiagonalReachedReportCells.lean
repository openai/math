import OAI.Computability.BorderVNP.DiagonalArgumentFromReachedTask
import OAI.Computability.BorderVNP.DiagonalSignedLaunchedCells

/-! # Native sparse argument inputs before the report continuation

The fitted cells on the reached task producer supply the sparse input
for the inverse private-report construction. Their rank, descriptor and
bound conditions describe physical rows on the genuine emitted memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Evaluator Evaluator.ScheduleClock SignedTaskArena CellSparse CellSparse.Packet
open CellSparse.Packet.Source CellPacket CellPacket.Supplement DiagonalTallyAllocation SparseExterior TypedTaskBuilder

variable {w n : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f orig fit cells) {team frame offsets ctl live ports : ℕ} {data : ℕ → ℕ → Bool}
    {Site : Type}

set_option quotPrecheck false
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "raw" => readings e.output
local notation "num" => (R).before raw (R).cells
local notation "idx" => globalCell (R).toLayout raw
variable (patch : SparsePatch (w:=w) Site (a.controlRows team frame offsets ctl live ports) (readings e.output))
    (row : (i : Fin ((a.controlRows team frame offsets ctl live ports).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a f orig data i.val)
local notation "src" => Batch.produced R raw patch.placed patch.geometry patch.extra
local notation "field" => SparseEmission.globalCells (team:=team) (frame:=frame) (offsets:=offsets) (ctl:=ctl) (live:=live)
  (ports:=ports) e row
local notation "os" => fun i => field (idx i)
local notation "sl" => batchLayout a frame ctl num
local notation "task" => fun i => ((os) i).typed sl (src i).typed
local notation "logical" => fun c => SparseExterior.logicalCell (patch.placed c) (patch.extra c) (field c).field

/-- Native row numbering, packed records, word extents and private call budgets
on one actual sparse task image. -/
structure ReachedReportCells (description : ℕ) : Prop where
  ownerOrder : ∀ i, (row i).number.val=idx i.val
  rank : ∀ c c' : Fin (R).cells, c<c' → raw ((R).sorted+(R).padded+((R).stops+c.val)) <
      raw ((R).sorted+(R).padded+c'.val)
  publicEnd : ∀ c < (R).cells, (patch.placed c).publicBase+((patch.placed c).parts.flatMap Part.publicBuffer).length ≤ (R).sorted
  geometry : ∀ c < (R).cells, patch.geometry c=(patch.placed c).publicBase+
      ((prefixParts (patch.placed c)).flatMap Part.publicBuffer).length
  originals : ∀ c < (R).cells, ∀ j, Sum.inr j ∈ (patch.placed c).boxes →
      (R).sorted+(R).padded≤(patch.placed c).slot j ∧ (patch.placed c).slot j+description≤a.fragments.external ∧
      (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors j)).length≤description
  sup : ∀ c < (R).cells, ((patch.extra c).flatMap record).length ≤ (R).stride
  stored : ∀ i < num, MergeFields (src i) (R).tasks (R).four i patch.built
  sizes : ∀ i < num, ((task) i).cell.payload.length≤a.p.scratchStride ∧ (((task) i).cell.burst w).length≤a.p.burstStride
  paid : ∀ c < (R).cells, (R).owner raw c=(R).team →
      (CompactFrame.pack w (Packet.input ((logical) c).directory ((logical) c).privateWires (field c).field.bytes)).length ≤ TeamScales.width n (1/2) ∧
      ((logical) c).directory.ProfileWidths ∧ SparseExterior.clock w ((logical) c).directory ((logical) c).privateWires (field c).field ≤ n^25

/-- Build the sparse source on this reached typed image before running the
last three argument programs. -/
theorem ReachedReportCells.sparseInput {description u v k : ℕ}
    (facts : ReachedReportCells (n:=n) e patch row description) {pub : Arg → Word w}
    (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (place : a.SparsePlacement frame ctl) (geo : SparseGeometry a f offsets ctl)
    (limit : a.endAddress w u v k<2^w) (fp : (pub 0).val=frame)
    (word : readings orig (frame+30)=w) (controls : ∀ i : Fin 37, readings orig (ctl+i.val)=a.controls i.val)
    (fields : (R).toLayout.Fields raw) : Nonempty (SparseCallInput pub patch.built) := by
  obtain ⟨arg,_⟩ := e.signed_call_input mac s patch row place geo limit fp word controls fields facts.ownerOrder
    facts.rank facts.publicEnd facts.geometry description facts.originals facts.sup facts.stored facts.sizes facts.paid
  exact ⟨arg⟩

end RoutingISA.FragmentRows


namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock FragmentRows SignedTaskArena

variable {w n u v k ctl team offsets live ports : ℕ} {Site : Type} (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (a : SignedTaskArena.Layout)

local notation "head" => readings pub 0
local notation "mem" => readings m
local notation "f" => FragmentRows.Layout.fromFrame head mem
local notation "R" => a.controlRows team head offsets ctl live ports

/-- Construct the post-report argument input from the field rows, packet
descriptors and numerical bounds on the physically reached compact task table.
These conditions can be read before the supplemental, sparse and typed passes. -/
theorem ArgumentInput.ofOwnedCells (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (geo : SparseGeometry a f offsets ctl)
    (cables : (f).host.count=a.cube.cables) (raw : mem (head+9)≤a.cube.maxRows)
    (cellCount : mem (head+11)=a.cube.cells) (high : a.endAddress w u v k<2^w)
    (outer : (R).Fields mem) (word : mem (head+30)=w)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(a.tasks team head offsets ctl).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem (some team)) (description : ℕ)
    (reached : ∀ (first : Returns emitBucket pub mac s m) (e : SparseEmission a f m fit cellCount.symm),
      e.bank=first.val.2.1 → e.output=first.val.2.2 →
      ∀ next : Returns TypedTaskBuilder.program pub mac e.bank e.output,
        readings next.val.2.2=(R).toLayout.published (readings e.output) →
        ∃ (patch : SparsePatch (w:=w) Site (R) (readings e.output)), patch.built=next.val.2.2 ∧
          ∃ (data : ℕ → ℕ → Bool) (rows : (i : Fin ((R).before (readings e.output) (R).cells)) →
            SparseCell a f m data i.val), ReachedReportCells (n:=n) e patch rows description) :
    Nonempty (ArgumentInput pub mac s m) := by
  apply ArgumentInput.ofOwnedTask pub mac s m a fit ptr words place cables raw cellCount high outer calls tasks geometry
  intro first e bank output next image
  obtain ⟨patch,built,data,rows,atRows⟩ := reached first e bank output next image
  rw [←built]
  exact atRows.sparseInput e patch rows mac next.val.2.1 place geo high rfl word words
    (e.task_fields ptr place outer calls tasks words)

/-- Use a fitted geometry on every cell as the geometry of the current owner. -/
theorem ArgumentInput.ofReachedCells (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (geo : SparseGeometry a f offsets ctl)
    (cables : (f).host.count=a.cube.cables) (raw : mem (head+9)≤a.cube.maxRows)
    (cellCount : mem (head+11)=a.cube.cells) (high : a.endAddress w u v k<2^w)
    (outer : (R).Fields mem) (word : mem (head+30)=w)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(a.tasks team head offsets ctl).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem) (description : ℕ)
    (reached : ∀ (first : Returns emitBucket pub mac s m) (e : SparseEmission a f m fit cellCount.symm),
      e.bank=first.val.2.1 → e.output=first.val.2.2 →
      ∀ next : Returns TypedTaskBuilder.program pub mac e.bank e.output,
        readings next.val.2.2=(R).toLayout.published (readings e.output) →
        ∃ (patch : SparsePatch (w:=w) Site (R) (readings e.output)), patch.built=next.val.2.2 ∧
          ∃ (data : ℕ → ℕ → Bool) (rows : (i : Fin ((R).before (readings e.output) (R).cells)) →
            SparseCell a f m data i.val), ReachedReportCells (n:=n) e patch rows description) :
    Nonempty (ArgumentInput pub mac s m) := by
  exact ArgumentInput.ofOwnedCells (Site:=Site) (n:=n) pub mac s m a fit ptr words place geo cables raw cellCount
    high outer word calls tasks (geometry.atTeam team) description reached

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
