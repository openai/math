import OAI.Computability.BorderVNP.CellSparseExterior
import OAI.Computability.BorderVNP.CubeHostScatterLayout
import OAI.Computability.BorderVNP.PackedDirectoryKeys

/-! # The public sparse incoming-fragment stream

The two geometry passes visit all source endpoints and then all destination
endpoints. The third pass visits the populated placement rows. Private
description slots lie beyond the supplied interval. Every emitted quadruple
uses the cell's actual absolute bank pointer and relative supplied offset.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.Fragments

open RoutingISA RoutingISA.SparseExterior Packing.Directory BorderVNP.Cube
open VPVNP.BurstRAM

/-- The four scalar operands passed to the stable per-cell bucketer. -/
structure Quad where
  /-- Destination cell in the sparse geometry. -/
  cell : ℕ
  /-- Logical lane offset in the supplied cell input. -/
  start : ℕ
  /-- First physical source address. -/
  source : ℕ
  /-- Number of consecutive source words. -/
  width : ℕ
  deriving DecidableEq

/-- Concrete RAM words in source-stream order. -/
def Quad.words (q : Quad) := [q.cell,q.start,q.source,q.width]

/-- The corresponding three-word per-cell descriptor and genuine supplied data. -/
def Quad.span (q : Quad) (data : ℕ → ℕ → Bool) : Span :=
  ⟨q.start,q.source,List.ofFn fun j : Fin q.width => data q.cell (q.start+j.val)⟩

@[simp] theorem Quad.span_words (q : Quad) (data : ℕ → ℕ → Bool) :
    (q.span data).words = [q.start,q.source,q.width] := by simp [Quad.span,Span.words]

/-- The remaining absolute address is the native cell-table base plus its
relative supplied offset. -/
def cable (l : HostScatter.Layout) (m : ℕ → ℕ) (side : Bool) (i : ℕ) : Option Quad :=
  if l.cell m i false = l.cell m i true ∨ l.width m i = 0 then none else
    some ⟨l.cell m i side,m (l.relative+2*i+side.toNat),l.dest m i side,l.width m i⟩

/-- A populated data row contributes exactly when its destination begins
inside the supplied interval. Private descriptions begin after it. -/
def live (supplied base : ℕ → ℕ) (r : Row) : Option Quad :=
  if r.slot < supplied r.cell ∧ 0 < r.width then some ⟨r.cell,r.slot,base r.cell+r.slot,r.width⟩ else none

/-- The finite sequence emitted by the two cable loops and the actual
compact seven-word raw delivery loop. -/
def stream (l : HostScatter.Layout) (m : ℕ → ℕ) (supplied : ℕ → ℕ) (rows : List Row) : List Quad :=
  (List.range l.count).filterMap (cable l m false) ++ (List.range l.count).filterMap (cable l m true) ++
    rows.filterMap (live supplied fun c => m (l.cells+2*c+1))

/-- At most two rows per sparse cable ID and one per populated delivery. -/
theorem stream_length (l : HostScatter.Layout) (m supplied : ℕ → ℕ) (rows : List Row) :
    (stream l m supplied rows).length ≤ 2*l.count+rows.length := by
  have a := List.length_filterMap_le (l := List.range l.count) (f := cable l m false)
  have b := List.length_filterMap_le (l := List.range l.count) (f := cable l m true)
  have c := List.length_filterMap_le (l := rows) (f := live supplied fun c => m (l.cells+2*c+1))
  simp only [stream,List.length_append,List.length_range] at *
  omega

/-- No source quadruple contains a blank interval or names an address in a
different consumer's physical bank. -/
theorem stream_located (l : HostScatter.Layout) (m supplied : ℕ → ℕ) (rows : List Row)
    (q : Quad) (hq : q ∈ stream l m supplied rows) :
    0 < q.width ∧ q.source = m (l.cells+2*q.cell+1)+q.start := by
  simp only [stream,List.mem_append,List.mem_filterMap] at hq
  rcases hq with (⟨i,_,hi⟩ | ⟨i,_,hi⟩) | ⟨r,_,hr⟩
  · unfold cable at hi
    split at hi <;> simp_all [HostScatter.Layout.dest]
    subst q
    exact ⟨by change 0 < l.width m i; omega,rfl⟩
  · unfold cable at hi
    split at hi <;> simp_all [HostScatter.Layout.dest]
    subst q
    exact ⟨by change 0 < l.width m i; omega,rfl⟩
  · unfold live at hr
    split at hr <;> simp_all
    subst q
    exact ⟨(show r.slot < supplied r.cell ∧ 0 < r.width by assumption).2,rfl⟩

/-- The stable subsequence for one cell, read as the compact writer's real
source descriptors. -/
def spans (qs : List Quad) (data : ℕ → ℕ → Bool) (c : ℕ) := (qs.filter (·.cell = c)).map (·.span data)

/-- Monotone true occupied intervals induce the exact encoder ordering after
stable bucketing. Unused slots and a trailing gap need no row. -/
theorem spans_ordered {qs : List Quad} {c cap : ℕ} (data : ℕ → ℕ → Bool)
    (order : qs.Pairwise fun a b => a.cell = c → b.cell = c → a.start+a.width ≤ b.start)
    (fits : ∀ q ∈ qs, q.cell = c → q.start+q.width ≤ cap) : Ordered cap 0 (spans qs data c) := by
  suffices aux : ∀ (pos : ℕ), pos ≤ cap → (∀ q ∈ qs, q.cell = c → pos ≤ q.start) →
      Ordered cap pos (spans qs data c) by exact aux 0 (Nat.zero_le _) (fun _ _ _ => Nat.zero_le _)
  induction qs with
  | nil => exact fun _ h _ => h
  | cons a as ih =>
    intro pos hp bound
    have tail := ih order.tail (fun b hb => fits b (List.mem_cons_of_mem _ hb))
    by_cases ha : a.cell = c
    · have hpos := bound a List.mem_cons_self ha
      have hcap := fits a List.mem_cons_self ha
      simp only [spans,List.filter_cons,ha,decide_true,ite_true,List.map_cons]
      refine ⟨hpos,?_⟩
      change Ordered cap (a.span data).stop (spans as data c)
      rw [show (a.span data).stop = a.start+a.width by simp [Quad.span,Span.stop]]
      exact tail _ hcap fun b hb hbc => (List.pairwise_cons.mp order).1 b hb ha hbc
    · simp only [spans,List.filter_cons,ha]
      exact tail pos hp fun b hb hbc => bound b (List.mem_cons_of_mem _ hb) hbc

/-- Each descriptor reads precisely its interval of received bits. -/
theorem Quad.span_reads {w : ℕ} (q : Quad) (data : ℕ → ℕ → Bool) (m : Memory w)
    (read : ∀ j : Fin q.width, (m (q.source+j.val)).val = (data q.cell (q.start+j.val)).toNat) :
    (q.span data).Reads m := by
  intro i hi
  have h : i < q.width := by simpa [Quad.span] using hi
  simpa [Quad.span] using read ⟨i,h⟩

end Diagonal.ExternalSew.Fragments

end BorderVNP
end Computability
end OAI
