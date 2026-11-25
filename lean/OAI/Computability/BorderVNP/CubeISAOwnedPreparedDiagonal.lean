import OAI.Computability.BorderVNP.CubeISAOwnedPreparedView

/-! # Inputs of the actual diagonal team view

A diagonal role takes no shared bits. Every selected singleton value is a
private choice, stored in the real ordered label-pair rectangle. The outer
machine already supplied both identical symbols and both absolute cursors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowSources

open Physical Physical.Owned Scatter RoutingISA RoutingISA.OwnedStages VPVNP.BurstRAM Tally DiagonalResidueRAM
open Padding.Banks

variable {w n d blocks b h K s : ℕ} {A : Data n d blocks b h K s}
variable {l : TeamRowPrepare.Layout} {power vertexBase stop : ℕ} {pub : Arg → Word w} {original m : Memory w}

/-- Complete diagonal calling convention and prepared destinations from the actual outer prepare return. -/
structure DiagonalReady (A : Data n d blocks b h K s) (l : TeamRowPrepare.Layout) (power : ℕ)
    (g : Fin d) (pub : Arg → Word w) (r : Bank w) (m : Memory w) : Prop where
  /-- The grouping axis and both ordered endpoint registers. -/
  entry : Entry A.axis g g r
  /-- Actual cursor at the start of the diagonal's empty selector prefix. -/
  selector : r 36 = word w (l.view (key (g,g)))
  /-- Actual cursor at the start of the diagonal's empty crossing stream. -/
  crossing : r 37 = word w (l.crossing (key (g,g)))
  /-- Current header and alphabet powers. -/
  loaded : (rowLayout A l power).Loaded n (readings pub) (readings m)
  /-- Machine-word bounds of the common setup. -/
  fit : (rowLayout A l power).Fits w n (readings pub 0)
  /-- The genuine destination words and empty source prefix for every selected singleton. -/
  prepared : (A.single g g (l.view (key (g,g))) (l.crossing (key (g,g)))).PreparedRow (source l power n) m
  /-- Protected actual singleton frame operands. -/
  fields : (pub 0).val+56 ∈ source l power n ∧ (pub 0).val+88 ∈ source l power n
  /-- Product-label range read from the native frame. -/
  labels : readings m ((pub 0).val+56) = d^(n+1)
  /-- Absolute singleton destination base read from the native frame. -/
  bank : readings m ((pub 0).val+88) = A.singleBase
  /-- Fit of both the endpoint keys and their physical address intervals. -/
  room : SingleRoom w n d (blocks*(h*b)) (pub 0).val A.singleBase

/-- A diagonal role is prepared by the same concrete header and allocation as a strict
role. No incoming payload or table of per-row preparation certificates is necessary. -/
theorem diagonal_ready (seed : Seed A l power pub original) (space : Allocation A l power vertexBase stop w)
    (g : Fin d) (r : Bank w) (room : vertexBase ≤ stop) (same : ∀ j ∈ source l power n, m j = original j)
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m)) :
    DiagonalReady A l power g pub r m := by
  have current := seed.transfer same
  have fr : (pub 0).val = l.frame := seed.frame
  let q := key (g,g)
  let D := A.single g g (l.view q) (l.crossing q)
  have left : q/l.d = g.val := by rw [seed.alphabet]; exact (key_digits (g,g)).1
  have right : q%l.d = g.val := by rw [seed.alphabet]; exact (key_digits (g,g)).2
  have ready : D.PreparedRow (source l power n) m := by
    apply D.preparedRow_of_streams
    · change Resident (source l power n) m D.crossing (if g=g then [] else _)
      simp only [ite_true]
      exact Resident.nil ..
    · intro t _ j hj
      exact space.singleDest room (D.pair t).1 (D.pair t).2 hj
  have rs : (r 36).val = l.view q := prep.selectorCursor
  have rc : (r 37).val = l.crossing q := prep.crossingCursor
  refine ⟨⟨prep.zero,prep.one,prep.axis.trans seed.axis,?_,?_⟩,
    Fin.ext (rs.trans (word_val _ _ (rs ▸ (r 36).isLt)).symm),
    Fin.ext (rc.trans (word_val _ _ (rc ▸ (r 37).isLt)).symm),current.loaded,
    seed.frame ▸ space.packets.layout,ready,⟨fr ▸ primary (by decide),fr ▸ primary (by decide)⟩,
    fr ▸ current.labels,fr ▸ current.singles,fr ▸ space.singles⟩
  · apply prep.smaller.trans
    change min (q/l.d) (q%l.d) = _
    simp only [left,right,min_self]
  · apply prep.larger.trans
    change max (q/l.d) (q%l.d) = _
    simp only [left,right,max_self]

/-- The actual native diagonal role writes exactly its owned singleton words and retains all
protected frame, declared-row, owner and routed-view words for the next iteration. -/
theorem diagonal_scatter (g : Fin d) (r : Bank w) (mac : TeamOpcode.Macros w 8)
    (ready : DiagonalReady A l power g pub r m) :
    let q := key (g,g)
    let D := A.single g g (l.view q) (l.crossing q)
    Owned.TraceRun pub mac (diagonalSide n) r m (Owned.rowChoices D.selected D.localBits) (singleStageCost D)
      (fun t mt => Keeps r t ∧ t 36 = word w D.selector ∧ t 37 = word w (D.before m (singlePairTrials n d)).1 ∧
        mt = (D.before m (singlePairTrials n d)).2 ∧ ∀ j ∈ source l power n, mt j = m j) := by
  intro q D
  have run := singleStage_run pub mac (rowLayout A l power) D (source l power n) r m ready.entry
    ready.selector ready.crossing ready.loaded ready.fit ready.prepared ready.fields.1 ready.fields.2
    ready.labels ready.bank ready.room.frameFit ready.room.keys ready.room.allocation
  apply run.mono le_rfl
  rintro t mt ⟨keep,rs,rc,hm⟩
  exact ⟨keep,rs,rc,hm,fun j hj => (congrFun hm j).trans (D.before_source m ready.prepared _ j hj)⟩

end Cube.TeamRowSources

end BorderVNP
end Computability
end OAI
