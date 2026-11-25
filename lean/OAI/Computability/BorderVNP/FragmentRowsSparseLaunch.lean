import OAI.Computability.BorderVNP.FragmentRowsSparseReadback

/-! # Launching the physical sparse encoder from the actual report memory

Every bounded owned ordinal is decoded by the true typed-task producer.
The report memory supplies its compact cell header, live physical bits and
raw suffix. The fragment and patch images transport those words to the
sparse encoder, with explicit separation between all successive row writes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Diagonal.ExternalSew.Fragments SparseExterior SignedTaskArena TypedTaskBuilder
open private ordered_stop from OAI.Computability.BorderVNP.FragmentRowsOwnedFit

variable {w : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
variable {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}

/-- The actual cell in the chronological report memory, before fragment emission. -/
structure SparseCell (a : SignedTaskArena.Layout) (f : FragmentRows.Layout) (orig : Memory w)
    (data : ℕ → ℕ → Bool) (i : ℕ) where
  /-- Global cell number of the compact task. -/
  number : Fin a.fragments.cells
  /-- Raw chronological count and use bits of this report. -/
  tail : List Bool
  bank : readings orig (f.host.cells+2*number.val+1)=a.cube.cellBank+number.val*a.cube.cellStride
  full : readings orig (f.supplied+number.val)+tail.length≤a.cube.cellStride
  sixNumber : readings orig (a.before.six+6*i)=number.val
  sixWidth : readings orig (a.before.six+6*i+2)=readings orig (f.supplied+number.val)
  tailLength : readings orig (a.before.tailWidths+number.val)=tail.length
  ordered : Ordered (readings orig (f.supplied+number.val)) 0 (spans (f.stream (readings orig)) data number.val)
  sources : ∀ r ∈ spans (f.stream (readings orig)) data number.val, r.Reads orig
  reports : CompactWrite.Source orig (readings orig (f.host.cells+2*number.val+1)+readings orig (f.supplied+number.val)) tail
  extent : (encode (readings orig (f.supplied+number.val)) tail 0 (spans (f.stream (readings orig)) data number.val)).length ≤ a.fragments.stride

variable (e : SparseEmission a f orig fit cells)
variable {team frame offsets ctl live ports : ℕ} {Site : Type} {data : ℕ → ℕ → Bool}
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "src" => readings e.output
local notation "O" => readings orig
local notation "num" => TypedTaskBuilder.Layout.before (CellControlRows.Layout.toLayout R) (readings e.output) a.cube.cells
variable (x : SparsePatch (w:=w) Site (a.controlRows team frame offsets ctl live ports) (readings e.output)) (place : a.SparsePlacement frame ctl)

/-- The fragment collector and task builder address the same physical bank
and the same supplied-width array in the public geometry layout. -/
structure SparseGeometry (a : SignedTaskArena.Layout) (f : FragmentRows.Layout) (offsets ctl : ℕ) : Prop where
  control : f.control=ctl
  controller : ctl+37≤a.cube.header.header
  banks : f.host.cells=a.cube.hostDirectory
  widths : f.supplied=offsets+2*a.cube.cables
  widthEnd : f.supplied+a.cube.cells≤ctl

/-- Native sparse record for the compact owned cell of the selected ordinal. -/
noncomputable def SparseCell.owned {i : ℕ} (c : SparseCell a f orig data i) : SparseExterior.Owned :=
  emittedOwned a f (O) fit cells c.number data ((O) (f.host.cells+2*c.number.val+1))
    ((O) (f.supplied+c.number.val)) c.tail

include e x place in
/-- A live cell's real six-word header, bank and raw report bits in the
post-report memory suffice for its exact native sparse-entry precondition. -/
theorem SparseEmission.initial_in_patch {u v k i : ℕ} (geo : SparseGeometry a f offsets ctl)
    (high : a.endAddress w u v k<2^w) (hi : i<num) (c : SparseCell a f orig data i)
    (global : c.number.val=globalCell (R).toLayout (src) i) :
    (c.owned (fit:=fit) (cells:=cells)).Initial (batchLayout a frame ctl num) i x.memory := by
  let g := c.number.val
  let width := (O) (f.supplied+g)
  let dense := (O) (f.host.cells+2*g+1)
  have ord := a.sparse_order place.cells
  have order := arena_order a
  have frag : a.fragments.start≤a.fragments.limit := by rw [a.fragments.footprint]; omega
  have gc : g<a.cube.cells := c.number.isLt
  have index : i<a.cube.cells := hi.trans_le ((R).before_le (src) (R).cells)
  have pairRoom : a.fragments.start≤a.fragments.pairs ∧ a.fragments.pairs+2*a.fragments.cells ≤ a.fragments.triples ∧
      a.fragments.triples+3*a.fragments.capacity≤a.fragments.cursors ∧ a.fragments.cursors≤a.fragments.limit := by
    simp only [FragmentArena.Layout.pairs,FragmentArena.Layout.quads,FragmentArena.Layout.triples,
      FragmentArena.Layout.cursors,FragmentArena.Layout.limit,FragmentArena.Layout.counts,FragmentArena.Layout.external]; omega
  have size := e.capacity
  have kept (addr : ℕ) (ht : (a.fragments.pairs≤addr ∧ addr<a.fragments.pairs+2*a.fragments.cells) ∨
      (a.fragments.triples≤addr ∧ addr<a.fragments.triples+3*(f.stream (O)).length)) : readings x.memory addr=(src) addr :=
    e.patch_region x place _ (by omega) (by omega)
  have task := x.dense_task (show (R).sorted+(R).padded ≤ (R).tasks by have sorted := place.sortedBank; change a.p.sorted+a.p.padded ≤ (a.tasks 0 0 0 0).tasks; omega)
    (show (R).merged+(R).cells≤(R).tasks by change a.before.merged+a.cube.cells≤(a.tasks 0 0 0 0).tasks; omega) hi
  rw [←global] at task
  have hdr := geo.controller
  have group := a.cube.writer_order
  have limit := place.beforeBank
  have ptr : (src) ((R).banks+2*g+1)=dense := by
    change (src) (a.cube.hostDirectory+2*g+1)=_
    dsimp only [dense]; rw [geo.banks]
    apply e.original _ (by rw [geo.control]; omega) (.inl ?_)
    change _ < a.fragments.quads; omega
  have supplied : (src) ((R).offsets+2*(R).cables+g)=width := by
    change (src) (offsets+2*a.cube.cables+g)=_
    rw [←geo.widths]
    have before := geo.widthEnd
    exact e.original _ (by rw [geo.control]; omega) (.inl (by omega))
  have tail : (src) ((R).tails+g)=c.tail.length := by
    change (src) (a.before.tailWidths+g)=_
    have reserve : a.fragments.limit ≤ a.before.tailWidths := le_rfl
    exact (e.original _ (by rw [geo.control]; omega) (.inr (by omega))).trans c.tailLength
  have beforeCell (z : ℕ) (lo : a.cube.cellBank≤z) (upper : z<a.cube.stop) : readings x.memory z=(O) z :=
    (e.patch_region x place z lo (by omega)).trans (e.original _ (by rw [geo.control]; omega) (.inl (by omega)))
  have location (r : Span) (hr : r ∈ spans (f.stream (O)) data g) : r.source=dense+r.start := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hr
    obtain ⟨hq,tag⟩ := List.mem_filter.mp hq
    have eq : q.cell=g := of_decide_eq_true tag
    have found := (stream_located f.host (O) (fun j => (O) (f.supplied+j)) _ q hq).2
    change q.source=dense+q.start
    rwa [eq] at found
  have bank : dense=a.cube.cellBank+g*a.cube.cellStride := c.bank
  have full : width+c.tail.length≤a.cube.cellStride := c.full
  have spanReads (r : Span) (hr : r ∈ spans (f.stream (O)) data g) : r.Reads x.memory := by
    intro j hj
    have bound := ordered_stop c.ordered hr
    change r.start+r.bits.length ≤ width at bound
    have loc := location r hr
    apply (beforeCell _ (by omega) ?_).trans (c.sources r hr j hj)
    rw [loc,bank,Nat.add_assoc]
    exact cell_address gc (by omega)
  have tailReads : CompactWrite.Source x.memory (dense+width) c.tail := by
    intro j hj
    apply (beforeCell (dense+width+j) (by omega) ?_).trans (c.reports j hj)
    rw [bank,Nat.add_assoc]; exact cell_address gc (by omega)
  exact owned_initial_in_arena a f (O) fit cells c.number data c.tail frame ctl num i u v k e.bank e.output x.memory
    e.result kept c.bank c.full e.cables e.raw ⟨index,index.trans_le place.cells⟩ high
    ((e.six_word x place geo.control index (k:=0) (by decide)).trans c.sixNumber)
    ((e.six_word x place geo.control index (k:=2) (by decide)).trans c.sixWidth)
    (task.1.trans ptr) (task.2.trans (congrArg₂ Nat.add supplied tail)) c.ordered spanReads tailReads c.extent

/-- The total array used by the native loop. Its unused entries have empty fields,
so this definition also covers zero cells and zero owned rows. -/
noncomputable def SparseEmission.ownedArray {count : ℕ} (atRow : (i : Fin count) → SparseCell a f orig data i.val)
    (i : ℕ) : SparseExterior.Owned :=
  if hi : i<count then (atRow ⟨i,hi⟩).owned (fit:=fit) (cells:=cells) else ⟨0,0,0,⟨0,[],[]⟩⟩

include e x place in
/-- All actual sparse entry inputs and independence of earlier writes follow
simultaneously from the post-report owned rows and the genuine native bucket. -/
theorem SparseEmission.launch {u v k : ℕ} (geo : SparseGeometry a f offsets ctl)
    (high : a.endAddress w u v k<2^w) (atRow : (i : Fin num) → SparseCell a f orig data i.val)
    (global : ∀ i, (atRow i).number.val=globalCell (R).toLayout (src) i.val) :
    let os := SparseEmission.ownedArray (fit:=fit) (cells:=cells) atRow
    let l := batchLayout a frame ctl num
    (∀ i < l.count, (os i).Initial l i x.memory) ∧
      ∀ i < l.count, ∀ j < i, ∀ addr, (os i).Source l i addr → (os j).Outside l j addr := by
  intro os l
  have row (i : ℕ) (hi : i<num) : os i=(atRow ⟨i,hi⟩).owned (fit:=fit) (cells:=cells) :=
    dite_eq_left hi
  refine ⟨fun i hi => (row i hi) ▸ e.initial_in_patch x place geo high hi (atRow ⟨i,hi⟩) (global _),?_⟩
  apply batch_independent a frame ctl num os (((R).before_le (src) (R).cells).trans place.cells)
  · intro i hi; rw [row i hi]; exact (atRow ⟨i,hi⟩).number.isLt
  · intro i hi; rw [row i hi]; exact e.triples_bound data (atRow ⟨i,hi⟩).number
  · intro i hi; rw [row i hi]; exact (atRow ⟨i,hi⟩).extent
  · intro i hi; rw [row i hi]; let c := atRow ⟨i,hi⟩
    exact (owned_bank_bounds a f (O) c.number data c.tail c.bank c.full c.ordered).2
  · intro i hi; rw [row i hi]; let c := atRow ⟨i,hi⟩
    exact (owned_bank_bounds a f (O) c.number data c.tail c.bank c.full c.ordered).1

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
