import OAI.Computability.VPVNP.CompressorGreedyWalkValid
import OAI.Computability.VPVNP.CompressorGreedyVisitAccess
import OAI.Computability.VPVNP.CompressorLogAccess
import OAI.Computability.VPVNP.CompressorGreedyRecordRanges

/-!
# External memory touched by the greedy readers

As the cursor advances through the directory, only the labels can change.
The immutable row fields determine both the direct field reads and the
addresses of the indirect operand reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena

open BurstRAM Compression Greedy SourceTransport
open scoped Fin.CommRing

namespace Assignment

variable {w N width d arity n : ℕ} {V A : Type*}
variable {L : WalkLayout w N width} {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N}
    {rows : OperandRows d} {m : Memory w} {encode : A → Word w} {label : V → A}

open private has_visit from OAI.Computability.VPVNP.CompressorGreedyWalkValid
open private base_bounds from OAI.Computability.VPVNP.CompressorRecordGreedyPrepare
open private stores_iff_fields from OAI.Computability.VPVNP.CompressorRecordGreedyDirectory

/-- Reads in each prepared row are direct header or pointer reads, or indirect
reads at one of the row's operand addresses. Writes affect only label cells. -/
theorem read_access (r : Assignment L T G order rows arity n m encode label)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width)
    (used : arity*n = width) (fit : n < 2^w) (space : L.limit < 2^w)
    (rd wr : ℕ → Prop)
    (dir : ∀ z, L.origin ≤ z → z < L.limit → rd z)
    (ptr : ∀ i : Fin N, ∀ p ∈ rowWords T G order (order.symm i) rows, rd p.val)
    (labels : ∀ i : Fin N, wr (L.label i).val) :
    LogAccess rd wr r.reads := by
  let ptrs := fun i : Fin N ↦ rowWords T G order (order.symm i) rows
  let initial := L.initialMemory ptrs m
  let fixed (mem : Memory w) := ∀ z, z < L.origin ∨ L.origin+N ≤ z → mem z = initial z
  let P := (visitMachine w arity n).program
  let fuel := 1+(visitCode arity n).length
  have scan (left k : ℕ) (stop : k+left = N) (mem : Memory w) (keep : fixed mem)
      (rs : List (Report w)) (run : runSegment P fuel (some (L.base k)) mem (List.replicate left []) = some rs) :
      LogAccess rd wr rs := by
    induction left generalizing k mem rs with
    | zero =>
      have empty : [] = rs := Option.some.inj run
      subst rs
      exact ⟨fun _ _ h ↦ False.elim (List.not_mem_nil h), fun _ _ h ↦ False.elim (List.not_mem_nil h)⟩
    | succ left ih =>
      let i : Fin N := ⟨k, by omega⟩
      let b := L.base k
      have repr : L.Represents initial mem id (Equiv.refl (Fin N)) (fun j ↦ mem (L.label j).val) :=
        ⟨fun _ ↦ rfl,keep⟩
      obtain ⟨dst, next, stored⟩ := repr.record L size i
      obtain ⟨bs, bound⟩ := base_bounds L i
      change b.val = _ at bs
      change b.val+(2+width) ≤ L.limit at bound
      have b1 : (b+1).val = b.val+1 := advance_val b 1 (by omega)
      have b2 : (b+1+1).val = b.val+2 := advance_val b 2 (by omega)
      have values := (stores_iff_fields mem (b+1+1) (ptrs i) (by rw [b2,size i]; omega)).mp stored
      have args (j : ℕ) (hj : j < arity*n) :
          rd (advance (b+1+1) j).val ∧ rd (mem (advance (b+1+1) j).val).val := by
        have pos : j < width := used ▸ hj
        have addr : (advance (b+1+1) j).val = (b+1+1).val+j := advance_val _ _ (by omega)
        rw [addr]
        refine ⟨dir _ (by omega) (by omega), ?_⟩
        have idx : j < (ptrs i).length := (size i).symm ▸ pos
        rw [values ⟨j,idx⟩]
        exact ptr i _ (List.getElem_mem idx)
      obtain ⟨v, es, he, hm, _⟩ := has_visit mem b arity n fit
      have access := Greedy.visit_access mem b arity n rd wr (dir _ (by omega) (by omega))
        (dir _ (by omega) (by omega)) args (dst ▸ labels i) _ he
      rw [show mem b.val = L.label i from dst] at hm
      rw [show mem (b+1).val = L.base (k+1) from next] at he
      rw [List.replicate_succ,runSegment,he] at run
      obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp run
      have nextKeep : fixed (after mem es) := by
        intro z hz
        rw [hm]
        have away : z ≠ (L.label i).val := by rw [WalkLayout.label_val]; have := i.isLt; omega
        exact (ite_eq_right away).trans (keep z hz)
      obtain ⟨tr, tw⟩ := ih _ (by omega) _ nextKeep _ ht
      exact ⟨fun a v ha ↦ (List.mem_append.mp ha).elim (access.1 a v) (tr a v),
        fun a v ha ↦ (List.mem_append.mp ha).elim (access.2 a v) (tw a v)⟩
  apply scan N 0 (Nat.zero_add _) initial (fun _ _ ↦ rfl)
  simpa only [r.prepMemory] using r.readRun

end Assignment

namespace Run

variable {w a g origin : ℕ} {X : ShrinkingState a g} {T : IncidenceDirectory w}
    {m : Memory w} (r : Run X T origin m)
local notation "n" => Fintype.card X.Base

/-- Both direct record reads and indirect color-label reads are above the
old-column lower bound. Every write is to the fresh greedy allocation. -/
theorem color_read_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) :
    LogAccess (fun z ↦ lo ≤ z ∧ z < greedyStop origin n a)
      (fun z ↦ origin ≤ z ∧ z < greedyStop origin n a) r.color.reads := by
  have ho := r.old 0
  have hl := low 0
  have hb := bounds origin n a
  change origin+n ≤ _ ∧ _ at hb
  have room := r.room
  apply r.color.read_access (fun i ↦ rowWords_color_length _ _ _ _) (Nat.one_mul _)
    (colorFits origin n a w Fintype.card_pos r.room)
    (by change offsetBase origin n a < 2^w; omega)
  · intro z hz hz'
    change origin ≤ z at hz
    change z < offsetBase origin n a at hz'
    exact ⟨by omega, by omega⟩
  · intro i p hp
    have range := r.color_pointer_range _ _ hp
    exact ⟨by omega, by omega⟩
  · intro i
    rw [WalkLayout.label_val]
    change origin ≤ origin+i.val ∧ origin+i.val < greedyStop origin n a
    have := i.isLt
    exact ⟨by omega, by omega⟩

/-- The offset reader dereferences only offset labels, projected displacement
words and the shared zero, and writes within the fresh allocation. -/
theorem tag_read_access (lo : ℕ) (low : ∀ c, lo ≤ (T.column c).val) :
    LogAccess (fun z ↦ lo ≤ z ∧ z < greedyStop origin n a)
      (fun z ↦ origin ≤ z ∧ z < greedyStop origin n a) r.offsets.reads := by
  have ho := r.old 0
  have hl := low 0
  have hb := bounds origin n a
  change origin+n ≤ _ ∧ _ at hb
  have room := r.room
  have big := Nat.le_mul_of_pos_left (2+4*WalkLayout.tagCount (2^a)) (Fintype.card_pos (α := X.Base))
  have fit : WalkLayout.tagCount (2^a) < 2^w := by
    unfold shiftBase at hb
    omega
  apply r.offsets.read_access (fun i ↦ by rw [rowWords_tag_length,tagTests_length,Nat.mul_comm]) rfl fit
    (by change shiftBase origin n a < 2^w; omega)
  · intro z hz hz'
    change offsetBase origin n a ≤ z at hz
    change z < shiftBase origin n a at hz'
    exact ⟨by omega, by omega⟩
  · intro i p hp
    have range := r.tag_pointer_range _ _ hp
    exact ⟨by omega, range.2⟩
  · intro i
    rw [WalkLayout.label_val]
    change origin ≤ offsetBase origin n a+i.val ∧ offsetBase origin n a+i.val < greedyStop origin n a
    have := i.isLt
    exact ⟨by omega, by omega⟩

end Run

end CompressorRecords.GreedyArena

end VPVNP
end Computability
end OAI
