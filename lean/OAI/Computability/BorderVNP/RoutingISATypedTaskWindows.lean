import OAI.Computability.BorderVNP.RoutingISATypedTaskAllocation

/-! # Explicit length-only allocation of the task producer's output windows

Given a common ceiling on all inputs, use consecutive arenas for the global
three-word calls, compact seven-word task table, unpacked scratch, and retained
bursts. The choice depends on the public dimensions and the worst-case sizes.
Only populated words count toward the execution budget.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM

/-- Place all task-produced outputs after the last input address. -/
def Layout.windows (l : Layout) (limit scratchWidth burstWidth : ℕ) : Layout :=
  { l with
    calls := limit
    tasks := limit+3*l.cells
    scratch := limit+3*l.cells+7*l.cells
    bursts := limit+3*l.cells+7*l.cells+scratchWidth*l.cells
    scratchStride := scratchWidth
    burstStride := burstWidth }

/-- End of the final length-only arena. -/
def Layout.windowsEnd (l : Layout) (limit scratchWidth burstWidth : ℕ) : ℕ :=
  limit+3*l.cells+7*l.cells+scratchWidth*l.cells+burstWidth*l.cells

/-- All read-only geometry, compact extent and header addresses lie in the lower input area. -/
structure Layout.InputBounds (l : Layout) (mem : ℕ → ℕ) (limit : ℕ) : Prop where
  /-- The machine frame and the entire 28-word allocation header fit below the ceiling. -/
  frames : l.frame+112 ≤ limit ∧ l.control+28 ≤ limit
  /-- Actual data arrays fit below the ceiling, and do not use the mutable count word of the frame. -/
  arrays : l.banks+2*l.cells ≤ limit ∧ l.offsets+2*l.cables+l.cells ≤ limit ∧
    l.tails+l.cells ≤ limit ∧ l.sorted+2*l.padded ≤ limit
  /-- The physical arrays begin after the machine frame. -/
  afterFrame : l.frame+112 ≤ l.banks ∧ l.frame+112 ≤ l.offsets ∧ l.frame+112 ≤ l.tails ∧ l.frame+112 ≤ l.sorted
  /-- True first and stop markers are within the returned inverse sort. -/
  markers : l.cells ≤ l.stops ∧ l.stops+l.cells ≤ l.padded
  /-- Physical permutation ranks are bounded by the padded descriptor sort. -/
  ranks : ∀ c < l.cells, mem (l.sorted+l.padded+c) < l.padded ∧
    mem (l.sorted+l.padded+(l.stops+c)) < l.padded
  /-- The transmitted canonical inputs and measured report bits fit the same ceiling. -/
  extents : ∀ c < l.cells, l.owner mem c=l.team → mem (l.offsets+2*l.cables+c)+mem (l.tails+c) ≤ limit

/-- The explicit allocation satisfies every address calculation and memory separation
condition of the real native task producer. -/
theorem windows_room (l : Layout) (mem : ℕ → ℕ) (limit sw bw w : ℕ)
    (h : l.InputBounds mem limit) (word : l.windowsEnd limit sw bw < 2^w) :
    (l.windows limit sw bw).Room mem w := by
  let q := l.windows limit sw bw
  have e := h.extents
  obtain ⟨ff,fc⟩ := h.frames
  obtain ⟨ab,ae,at',as'⟩ := h.arrays
  unfold Layout.windowsEnd at word
  refine ⟨by dsimp [Layout.windows]; omega,by dsimp [Layout.windows]; omega,
    by dsimp [Layout.windows]; omega,by dsimp [Layout.windows]; omega,by dsimp [Layout.windows]; omega,
    by dsimp [Layout.windows]; omega,fun c hc own => (e c hc own).trans_lt (by omega),by dsimp [Layout.windows]; omega,
    by dsimp [Layout.windows]; omega,h.markers,h.ranks,by dsimp [Layout.windows]; omega,
    by dsimp [Layout.windows]; omega,?_,by dsimp [Layout.windows]; omega,by dsimp [Layout.windows]; omega⟩
  intro c hc a ha
  change c < l.cells at hc
  change l.inputAt c a at ha
  obtain ⟨lb,le,lt',ls⟩ := h.afterFrame
  have below : a < limit ∧ l.frame+90 < a := by
    rcases ha with h1|h1|h1|h1|h1|h1 <;> subst a <;> have := h.markers <;> omega
  change ¬((limit+3*l.cells ≤ a ∧ a < (limit+3*l.cells)+7*l.cells) ∨
    (∃ v < l.cells, a=limit+3*v) ∨ a=l.frame+90)
  rintro (ht|⟨v,hv,ha⟩|ha) <;> omega

/-- Within the explicit length-only windows the initializer fits, including arbitrary
true supplemental chunks, whenever each live source lies in the input area and its
actual output sizes obey the public stride bounds. -/
theorem windows_arenas (l : Layout) (mem : ℕ → ℕ) (limit sw bw w : ℕ) (tasks : ℕ → TypedBatch.Task)
    (starts : ∀ j < l.before mem l.cells,
      let c := globalCell l mem j
      (tasks j).callRow=limit+3*c ∧ (tasks j).cell.scratchBase=limit+3*l.cells+7*l.cells+sw*c ∧
      (tasks j).cell.burstBase=limit+3*l.cells+7*l.cells+sw*l.cells+bw*c)
    (desc : ∀ j < l.before mem l.cells, (tasks j).cell.descriptorBase+3*(tasks j).cell.chunks.length ≤ limit)
    (ext : ∀ j < l.before mem l.cells, (tasks j).cell.externalBase+(tasks j).cell.external.length ≤ limit)
    (src : ∀ j < l.before mem l.cells, ∀ u ∈ (tasks j).cell.chunks, u.endSource ≤ limit)
    (size : ∀ j < l.before mem l.cells, (tasks j).cell.payload.length ≤ sw ∧
      ((tasks j).cell.burst w).length ≤ bw) :
    (l.windows limit sw bw).Arenas mem w tasks := by
  let q := l.windows limit sw bw
  have before (i : ℕ) : q.before mem i=l.before mem i := by
    induction i with
    | zero => rfl
    | succ i ih => simp only [Layout.before,ih]; rfl
  have total : q.before mem q.cells=l.before mem l.cells := before l.cells
  have order (j : ℕ) (hj : j < l.before mem l.cells) : globalCell q mem j=globalCell l mem j := by
    obtain ⟨hc,own,rk⟩ := global_spec l mem hj
    have h := global_at q mem (c := globalCell l mem j) hc own
    rw [before,rk] at h
    exact h
  refine ⟨by dsimp [Layout.windows]; omega,by dsimp [Layout.windows]; omega,le_rfl,?_,?_,?_,?_,fun j hj => size j (total ▸ hj)⟩
  · intro j hj
    change _ = q.call (globalCell q mem j) ∧ _ = q.scratch+q.scratchStride*globalCell q mem j ∧
      _=q.bursts+q.burstStride*globalCell q mem j
    rw [order j (total ▸ hj)]
    exact starts j (total ▸ hj)
  · intro j hj; have d := desc j (total ▸ hj)
    exact ⟨d.trans (by dsimp [Layout.windows]; omega),Or.inl d⟩
  · intro j hj; have d := ext j (total ▸ hj)
    exact ⟨d.trans (by dsimp [Layout.windows]; omega),Or.inl d⟩
  · intro j hj u hu; have d := src j (total ▸ hj) u hu
    exact ⟨d.trans (by dsimp [Layout.windows]; omega),Or.inl d⟩

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
