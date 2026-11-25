import OAI.Computability.BorderVNP.FragmentRowsSparsePatch
import OAI.Computability.BorderVNP.FragmentRowsOwnedFit

/-! # Physical sparse inputs through the fragment, task and supplemental stores

The native bucket provides each row's true starting triple and span count.
The typed task and supplemental writers preserve these arrays, the compact
six-word headers, and the original cell bits and report suffix. All uses of
the bucketed memory below refer to this same emitted stream.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Diagonal.ExternalSew.Fragments SparseExterior SignedTaskArena
open DiagonalTallyAllocation TypedTaskBuilder
open private ordered_stop from OAI.Computability.BorderVNP.FragmentRowsOwnedFit

variable {w : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
variable {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
local notation "B" => a.fragments.bucket (List.length (f.stream (readings orig)))
local notation "tag" => f.bucketTag fit B rfl cells
local notation "quad" => f.bucketRow (readings orig) B rfl

/-- The two real consecutive fragment program outputs in the signed allocation. -/
structure SparseEmission (a : SignedTaskArena.Layout) (f : FragmentRows.Layout) (orig : Memory w)
    (fit : f.Fits w (readings orig)) (cells : a.fragments.cells=f.cells) where
  /-- State immediately after the fragment emitter. -/
  middle : NatState
  /-- Registers returned by the stable bucket program. -/
  bank : Bank w
  /-- Word RAM returned by the same stable bucket program. -/
  output : Memory w
  image : middle.mem=f.image (readings orig)
  result : FragmentBucket.Result (a.fragments.bucket (f.stream (readings orig)).length)
    (f.bucketTag fit (a.fragments.bucket (f.stream (readings orig)).length) rfl cells)
    (fun i => fieldValue (f.bucketRow (readings orig) (a.fragments.bucket (f.stream (readings orig)).length) rfl i))
    middle (.ofWords bank output)
  quads : f.quads=a.fragments.quads
  cables : f.host.count=a.cube.cables
  raw : f.count≤a.cube.maxRows

variable (e : SparseEmission a f orig fit cells)
include e

/-- The two genuine cable passes and the raw directory fit the single reserved capacity. -/
theorem SparseEmission.capacity : (f.stream (readings orig)).length≤a.fragments.capacity := by
  have size := stream_length f.host (readings orig) (fun c => readings orig (f.supplied+c))
    ((List.range f.count).map (f.row (readings orig)))
  simp only [List.length_map,List.length_range] at size
  change (f.stream (readings orig)).length≤2*f.host.count+f.count at size
  rw [e.cables] at size
  change _ ≤ 2*a.cube.cables+a.cube.maxRows+1
  have := e.raw; omega

/-- A word outside the fragment reservation, except for control 29, is unchanged
by both native programs. This includes previously published six-word rows above it. -/
theorem SparseEmission.original (addr : ℕ) (clear : addr≠f.control+29)
    (outside : addr<a.fragments.start ∨ a.fragments.limit≤addr) : readings e.output addr=readings orig addr := by
  let l := a.fragments
  have ordered : l.start ≤ l.pairs ∧ l.pairs+2*l.cells ≤ l.triples ∧ l.triples+3*l.capacity ≤ l.cursors ∧
      l.cursors+l.cells ≤ l.limit := by
    simp only [FragmentArena.Layout.pairs,FragmentArena.Layout.quads,FragmentArena.Layout.triples,
      FragmentArena.Layout.cursors,FragmentArena.Layout.limit,FragmentArena.Layout.counts,FragmentArena.Layout.external]
    omega
  have size := e.capacity
  change (f.stream (readings orig)).length≤l.capacity at size
  have old : readings e.output addr=e.middle.mem addr := by
    apply e.result.other addr
    · change addr<l.pairs ∨ l.pairs+2*l.cells ≤ addr; change addr<l.start ∨ l.limit≤addr at outside; omega
    · change addr<l.triples ∨ l.triples+3*(f.stream (readings orig)).length ≤ addr
      change addr<l.start ∨ l.limit≤addr at outside; omega
    · change addr<l.cursors ∨ l.cursors+l.cells ≤ addr; change addr<l.start ∨ l.limit≤addr at outside; omega
  rw [old,e.image,Layout.image,Function.update_of_ne clear]
  apply Packing.BottomReports.Writer.write_outside
  rw [quadWords_length,e.quads]
  change addr<l.start ∨ l.start+4*(f.stream (readings orig)).length≤addr
  rcases outside with h|h
  · exact .inl h
  · apply Or.inr
    have pair : l.start+4*l.capacity=l.pairs := rfl
    change l.limit ≤ addr at h; omega

/-- The true occupied triple subarray of a chosen cell lies inside the allocated table. -/
theorem SparseEmission.triples_bound (data : ℕ → ℕ → Bool) (c : Fin a.fragments.cells) :
    FragmentBucket.start tag c.val + (spans (f.stream (readings orig)) data c.val).length ≤ a.fragments.capacity := by
  have h := (Layout.bucket_header fit B rfl cells data c e.result).2
  have len := (e.result.counts c).symm.trans h
  rw [←len]
  change FragmentBucket.start tag c.val+FragmentBucket.count tag c ≤ a.fragments.capacity
  rw [←FragmentBucket.start_step tag c]
  exact (FragmentBucket.start_le_rows tag (Nat.succ_le_of_lt c.isLt)).trans e.capacity

variable {team frame offsets ctl live ports : ℕ} {Site : Type}
local notation "R" => a.controlRows team frame offsets ctl live ports
local notation "src" => readings e.output
local notation "O" => readings orig
variable (x : SparsePatch (w:=w) Site (a.controlRows team frame offsets ctl live ports) (readings e.output)) (place : a.SparsePlacement frame ctl)
include x place

/-- Controller operands surviving the native emitter and stable bucketer are
read in the chronological supplemental output, including the newly emitted count. -/
theorem SparseEmission.loaded (control : f.control=ctl) (fields : (R).toLayout.Fields (src))
    (controls : ∀ j : Fin 37, (O) (ctl+j.val)=a.controls j.val) :
    (batchLayout a frame ctl ((R).before (src) (R).cells)).Loaded (readings x.memory) := by
  apply x.loaded_in_arena a place fields
  intro k hk
  have order := a.sparse_order place.cells
  have before := place.beforeBank
  have small := k.isLt
  exact (e.original _ (by rw [control]; omega) (.inl (by omega))).trans (controls k)

/-- Both writers preserve the populated native fragment arrays and each actual
receiving bank, irrespective of the shapes of the other teams' sparse arguments. -/
theorem SparseEmission.patch_region (addr : ℕ) (lo : a.cube.cellBank≤addr) (hi : addr<a.fragments.limit) :
    readings x.memory addr=(src) addr := by
  have order := a.sparse_order place.cells
  have merged : addr < (R).merged := hi.trans_le order.2.2.1
  apply x.original _ (.inr (place.sortedBank.trans lo)) (.inl merged)
  have call : (R).merged ≤ (R).calls := (a.task_bounds team frame offsets ctl).1
  have tasks : (R).merged ≤ (R).tasks := (a.task_bounds team frame offsets ctl).2.1
  have before := place.beforeBank
  have head := place.beforeControl
  change ¬(((R).tasks≤addr ∧ _) ∨ (∃ c<(R).cells,addr=(R).calls+3*c) ∨ addr=frame+90)
  rintro (⟨_,_⟩|⟨c,_,_⟩|_) <;> omega

/-- All six native words at a valid compact ordinal survive the subsequent
fragment, task, and supplemental passes. -/
theorem SparseEmission.six_word (control : f.control=ctl) {i k : ℕ} (hi : i<a.cube.cells) (hk : k<6) :
    readings x.memory (a.before.six+6*i+k)=(O) (a.before.six+6*i+k) := by
  let addr := a.before.six+6*i+k
  have order := a.sparse_order place.cells
  have frag : a.fragments.start≤a.fragments.limit := by rw [a.fragments.footprint]; omega
  have above : a.fragments.limit≤addr := by dsimp only [addr]; omega
  have bank : a.cube.cellBank≤addr := by omega
  have ctlLo := place.beforeBank
  have frameLo := place.beforeControl
  have srcWord := e.original addr (by rw [control]; omega) (.inr above)
  apply Eq.trans _ srcWord
  have full : (R).merged+(R).cells≤addr := by change a.before.merged+a.cube.cells≤addr; dsimp only [addr]; omega
  apply x.original addr (.inr (place.sortedBank.trans bank)) (.inr full)
  have last : addr < a.before.limit := by dsimp only [addr]; omega
  have calls : (R).calls=a.before.limit := rfl
  have tasks : a.before.limit ≤ (R).tasks := Nat.le_add_right ..
  change ¬(((R).tasks≤addr ∧ _) ∨ (∃ c<(R).cells,addr=(R).calls+3*c) ∨ addr=frame+90)
  rintro (⟨_,_⟩|⟨c,_,_⟩|_) <;> omega

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
