import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy
import OAI.Computability.VPVNP.CompressorSourceOnline

/-!
# Cursor progress of the native greedy preparation scans

Each call starts at the index of its vertex and returns the following index.
The memory before that call contains the prepared prefix of the directory.
This gives the exclusive stop guard for both the color and offset scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.GreedyArena

open BurstRAM Compression Greedy SourceOnline
open scoped Fin.CommRing

namespace Assignment

variable {w N width d arity n : ℕ} {V A : Type*}
variable {L : WalkLayout w N width} {T : PortTables w} {G : SlotGraph V d} {order : V ≃ Fin N}
    {rows : OperandRows d} {m : Memory w} {encode : A → Word w} {label : V → A}

/-- In a native preparation scan, every reported return advances to the next
vertex and the final cursor reaches the exclusive vertex count. -/
theorem prep_progress (r : Assignment L T G order rows arity n m encode label)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2 ^ w) (outside : GraphOutside (d := d) L T order)
    (size : ∀ i : Fin N, (rowWords T G order (order.symm i) rows).length = width) :
    Progress (N : Word w) 0 r.prep := by
  let ptrs := fun i : Fin N ↦ rowWords T G order (order.symm i) rows
  let mem := L.prefixMemory ptrs m
  let P := ((Relocated.preparePass rows).table.instantiate w (Relocated.publicWords d L T)).program
  let fuel := 1 + (Relocated.prepareCode rows).length
  have fit : N < 2 ^ w := by unfold WalkLayout.limit at space; omega
  have loop (left k : ℕ) (stop : k + left = N) (rs : List (Report w))
      (run : runSegment P fuel (some (Fin.ofNat _ k)) (mem k) (List.replicate left []) = some rs) :
      Progress (N : Word w) (Fin.ofNat _ k) rs := by
    induction left generalizing k rs with
    | zero =>
      have empty : [] = rs := Option.some.inj run
      subst rs
      simp only [Nat.add_zero] at stop
      subst k
      exact .done le_rfl
    | succ left ih =>
      let i : Fin N := ⟨k, by omega⟩
      obtain ⟨es, he, hm, _, _⟩ := Relocated.prepare_one L T G order rows (mem k) i labels
        (L.prefixMemory_tables ptrs m i.isLt.le rep outside) space outside (size i)
      have next : after (mem k) es = mem (k+1) := hm.trans (L.write_prefixMemory ptrs m size i)
      rw [List.replicate_succ, runSegment, he] at run
      change (runSegment P fuel (some (Fin.ofNat _ (k+1))) (after (mem k) es)
        (List.replicate left [])).map _ = some rs at run
      rw [next] at run
      obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp run
      refine .next (next := Fin.ofNat _ (k+1)) ?_ rfl (ih _ (by omega) _ ht)
      change k % (2 ^ w) < N % (2 ^ w)
      rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ w), Nat.mod_eq_of_lt fit]
      omega
  have zero : Fin.ofNat _ 0 = (0 : Word w) := Fin.ext (Nat.zero_mod _)
  rw [← zero]
  apply loop N 0 (Nat.zero_add N)
  rw [show mem 0 = m from L.prefixMemory_zero ptrs m, zero]
  exact r.prepRun

end Assignment

namespace Run

variable {w a g origin : ℕ} {X : ShrinkingState a g} {T : IncidenceDirectory w}
    {m : Memory w} (r : Run X T origin m)

open private projection_frame from OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy

include r in
private theorem projected_below (z : ℕ) (hz : z < origin) : projectedMemory X T origin m z = m z := by
  have hb := bounds origin (Fintype.card X.Base) a
  change origin + _ ≤ _ ∧ _ at hb
  exact projection_frame X T origin m r.room r.projection z (by omega)

/-- Progress for the color initializer on the memory left by tag projection. -/
theorem color_prepare_progress : Progress ((Fintype.card X.Base : ℕ) : Word w) 0 r.color.prep := by
  let n := Fintype.card X.Base
  have hb := bounds origin n a
  change origin + n ≤ _ ∧ _ at hb
  have room : greedyStop origin n a < 2 ^ w := r.room
  have colorFit := colorFits origin n a w Fintype.card_pos room
  have baseFit := r.old.baseFits.trans (by omega : origin ≤ 2 ^ w)
  have preRep := r.old.preserve r.input (projected_below r)
  exact r.color.prep_progress rfl (tables_rep preRep _ _ _ (by omega) baseFit)
    (by change offsetBase origin n a < 2 ^ w; omega)
    (r.old.graphOutside _ le_rfl _ _ _) (fun i ↦ rowWords_color_length _ _ _ _)

/-- Progress for the offset initializer on the memory left by the color reader. -/
theorem tag_prepare_progress : Progress ((Fintype.card X.Base : ℕ) : Word w) 0 r.offsets.prep := by
  let n := Fintype.card X.Base
  have hb := bounds origin n a
  change origin + n ≤ _ ∧ _ at hb
  have room : greedyStop origin n a < 2 ^ w := r.room
  have colorFit := colorFits origin n a w Fintype.card_pos room
  have baseFit := r.old.baseFits.trans (by omega : origin ≤ 2 ^ w)
  have colorBelow (z : ℕ) (hz : z < origin) : r.color.post z = m z :=
    (r.color.frame z (.inl hz)).trans (projected_below r z hz)
  have colorRep := r.old.preserve r.input colorBelow
  exact r.offsets.prep_progress rfl (tables_rep colorRep _ _ _ (by omega) baseFit)
    (by change shiftBase origin n a < 2 ^ w; omega)
    (r.old.graphOutside _ (by change origin ≤ offsetBase origin n a; omega) _ _ _)
    (fun i ↦ by rw [rowWords_tag_length, tagTests_length, Nat.mul_comm])

end Run

end CompressorRecords.GreedyArena

end VPVNP
end Computability
end OAI
