import OAI.Computability.BorderVNP.DiagonalExternalFragmentCover

/-! # Reading occupied and omitted bits after the private sparse-input expansion

The dense index of a span bit is its logical start plus its lane. Only gaps
are filled with zero, and the unexpanded report suffix follows the bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

private theorem ordered_mem_start {width pos : ℕ} {ss : List Span} (h : Ordered width pos ss)
    {s : Span} (mem : s ∈ ss) : pos ≤ s.start := by
  induction ss generalizing pos with
  | nil => simp at mem
  | cons a ss ih =>
    rcases List.mem_cons.mp mem with rfl | hs
    · exact h.1
    · exact h.1.trans ((Nat.le_add_right ..).trans (ih h.2 hs))

/-- Restoring an ordered sparse bank gives precisely the fragment bit at its
logical index. This works for both crossing-wire and free-field fragments. -/
theorem expand_span_read (width : ℕ) (tail : List Bool) {pos : ℕ} {ss : List Span}
    (order : Ordered width pos ss) {s : Span} (mem : s ∈ ss) (i : Fin s.bits.length) :
    (expand width tail pos ss)[s.start+i.val-pos]? = some s.bits[i.val] := by
  induction ss generalizing pos with
  | nil => simp at mem
  | cons a ss ih =>
    rcases List.mem_cons.mp mem with rfl | hs
    · have lo := order.1
      rw [expand,List.append_assoc,List.getElem?_append_right (by simp only [List.length_replicate]; omega),
        List.length_replicate,show s.start+i.val-pos-(s.start-pos) = i.val by omega,
        List.getElem?_append_left i.isLt,List.getElem?_eq_getElem i.isLt]
    · have before := order.1
      have hit := ordered_mem_start order.2 hs
      change a.start+a.bits.length ≤ s.start at hit
      rw [expand,List.getElem?_append_right (by
        simp only [List.length_append,List.length_replicate]
        omega),List.length_append,List.length_replicate]
      have loc : s.start+i.val-pos-(a.start-pos+a.bits.length) = s.start+i.val-a.stop := by
        unfold Span.stop
        omega
      rw [loc]
      exact ih order.2 hs

/-- Every logical supplied index outside all transmitted spans is restored as
zero, independent of the report data. -/
theorem expand_gap_read (width : ℕ) (tail : List Bool) {pos index : ℕ} {ss : List Span}
    (order : Ordered width pos ss) (lo : pos ≤ index) (hi : index < width)
    (miss : ∀ s ∈ ss, ¬(s.start ≤ index ∧ index < s.stop)) :
    (expand width tail pos ss)[index-pos]? = some false := by
  induction ss generalizing pos with
  | nil =>
    rw [expand,List.getElem?_append_left (by simp only [List.length_replicate]; omega),List.getElem?_replicate]
    simp [show index-pos < width-pos by omega]
  | cons s ss ih =>
    have before := order.1
    by_cases lt : index < s.start
    · rw [expand,List.append_assoc,List.getElem?_append_left (by simp only [List.length_replicate]; omega),
        List.getElem?_replicate]
      simp [show index-pos < s.start-pos by omega]
    · have past : s.stop ≤ index := by
        have := miss s List.mem_cons_self
        omega
      have hp : s.start+s.bits.length ≤ index := past
      rw [expand,List.getElem?_append_right (by simp only [List.length_append,List.length_replicate]; omega),
        List.length_append,List.length_replicate,
        show index-pos-(s.start-pos+s.bits.length) = index-s.stop by unfold Span.stop; omega]
      exact ih order.2 past fun a ha => miss a (List.mem_cons_of_mem _ ha)

end RoutingISA.SparseExterior

namespace Diagonal.ExternalSew.Fragments

open Packing.Directory BorderVNP.Cube RoutingISA.SparseExterior

variable {R r w link V g entries desc : ℕ}

/-- On a genuinely used grouped input, the private restoration of the three
physical fragment passes reads the original bit of the receiving cell. -/
theorem expand_free_lane_read (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)
    (pp lp : ℕ → ℕ × ℕ) (supplied : ℕ → ℕ)
    (fit : ∀ a : FreeBlock R V, let dest := lp (a.1.val*V+a.2.val); dest.2+g ≤ supplied dest.1)
    (l : HostScatter.Layout) (m : ℕ → ℕ) (data : ℕ → ℕ → Bool) (z : FreePort R r w) (tail : List Bool) :
    let pos := laneAddress lp (freeLane hg room z)
    let ss := spans (stream l m supplied ((freeDirectory R r w link V g entries desc).directory pp lp)) data pos.1
    Ordered (supplied pos.1) 0 ss → (expand (supplied pos.1) tail 0 ss)[pos.2]? = some (data pos.1 pos.2) := by
  intro pos ss order
  obtain ⟨s,mem,i,addr,_,bit⟩ := spans_free_lane (entries := entries) (desc := desc)
    hg room pp lp supplied fit l m data z
  have hs : s ∈ ss := mem
  have read := expand_span_read (supplied pos.1) tail order hs i
  simpa only [Nat.sub_zero,addr,bit] using read

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
