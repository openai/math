import OAI.Computability.BorderVNP.CubeISALocalRowGroupLayout

/-! # Address and word bounds of the native histogram and team assignment

The histogram writes above both its claimed-row input and the data returned by
the label chooser. Each team's total and each group's owner occupy their own
intervals above the histogram. The aggregate scaled load bounds all histogram
words before the allocator runs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube Finset

private theorem groupIntervals (a : CubeArena.Layout) :
    a.header.packetBase ≤ a.publicBase ∧ a.publicBase+a.cells ≤ a.demands ∧
    a.demands+a.cells ≤ a.powerBase ∧ 2*a.alphabet ≤ a.powerBase ∧ a.pairDirectory ≤ a.stop := by
  have header := (arenaExtents a).1
  have ⟨raw,single,vertex,_,_,_⟩ := a.separated
  have twice := Nat.le_self_pow (by decide : 2 ≠ 0) a.alphabet
  refine ⟨by omega,?_,?_,?_,?_⟩
  · unfold CubeArena.Layout.demands CubeArena.Layout.nodes CubeArena.Layout.heads
    omega
  · unfold CubeArena.Layout.powerBase CubeArena.Layout.ordinalBase CubeArena.Layout.widthBase
      CubeArena.Layout.dataMean CubeArena.Layout.cableMean
    omega
  · unfold CubeArena.Layout.powerBase CubeArena.Layout.ordinalBase CubeArena.Layout.widthBase
    omega
  · unfold CubeArena.Layout.stop CubeArena.Layout.cellBank CubeArena.Layout.pairBase TableLayout.reserveEnd
      CubeArena.Layout.records CubeArena.Layout.hostDirectory
    omega

private theorem groupPointers (a : CubeArena.Layout) :
    a.powerBase+(a.n+1) = a.groupWeights ∧ a.groupWeights+a.header.d = a.teamTotals ∧
    a.teamTotals+a.teams = a.ownerBase ∧ a.ownerBase+a.header.d = a.pairDirectory :=
  ⟨rfl,rfl,rfl,rfl⟩

private theorem row_before_public (a : CubeArena.Layout) (frame axis s t : ℕ)
    (axes : a.header.a = a.n+1) (valid : axis < a.n+1) (hs : s < a.header.d) (ht : t < a.header.d) :
    (weightLayout a frame axis).rowAddr s t < a.publicBase := by
  have minLt := (min_le_left s t).trans_lt hs
  have maxLt := max_lt hs ht
  have row : min s t*a.header.d+max s t < a.header.d*a.header.d := by
    have step := Nat.mul_le_mul_right a.header.d minLt
    rw [Nat.succ_mul] at step
    omega
  have cell := Nat.mul_le_mul_right (a.n+1) row
  rw [Nat.succ_mul] at cell
  have head := (groupIntervals a).1
  unfold CubeHeaderInstall.Inputs.packetBase at head
  have count : a.header.entries = a.header.d*a.header.d*(a.n+1) := by simp [CubeHeaderInstall.Inputs.entries,axes]
  change a.header.header+13+a.header.entries+(min s t*a.header.d+max s t)*(a.n+1)+axis < a.publicBase
  omega

/-- The checked aggregate histogram bounds every intermediate group sum.
The compact rows, chosen labels, and incoming demands all precede the histogram. -/
theorem weightFits_of_arena (a : CubeArena.Layout) (w frame axis : ℕ) (mem : ℕ → ℕ)
    (axes : a.header.a = a.n+1) (alphabet : 0 < a.header.d) (valid : axis < a.n+1)
    (high : a.stop < 2^w)
    (mass : ∑ i ∈ range a.header.d, (weightLayout a frame axis).weight mem i < 2^w) :
    (weightLayout a frame axis).Fits w mem := by
  let l := weightLayout a frame axis
  obtain ⟨head,labels,data,_,stop⟩ := groupIntervals a
  obtain ⟨powers,weights,totals,owners⟩ := groupPointers a
  have square : a.header.d*a.header.d ≤ a.header.entries := by
    change _ ≤ a.header.d*a.header.d*a.header.a
    apply Nat.le_mul_of_pos_right
    omega
  have hdr : a.header.entries ≤ a.header.packetBase := by unfold CubeHeaderInstall.Inputs.packetBase; omega
  refine ⟨alphabet,by change a.header.d*a.header.d < 2^w; omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro s hs
    change s < a.header.d at hs
    change a.groupWeights+s < 2^w
    omega
  · intro s hs t ht
    exact (row_before_public a frame axis s t axes valid hs ht).trans (by omega)
  · intro c hc
    change c < a.cells at hc
    change a.publicBase+c < 2^w
    omega
  · intro c hc
    change c < a.cells at hc
    change a.demands+c < 2^w
    omega
  · intro s hs t ht u _
    have row := row_before_public a frame axis s t axes valid hs ht
    change (weightLayout a frame axis).rowAddr s t ≠ a.groupWeights+u
    omega
  · intro c hc u _
    change c < a.cells at hc
    change a.publicBase+c ≠ a.groupWeights+u
    omega
  · intro c hc u _
    change c < a.cells at hc
    change a.demands+c ≠ a.groupWeights+u
    omega
  · intro s hs
    exact (single_le_sum (f := l.weight mem) (fun _ _ => Nat.zero_le _) (mem_range.mpr hs)).trans_lt mass

/-- Frame reads, the power lookup at the selected axis, and twice the label
alphabet all fit; the histogram bounds the remaining intermediate products. -/
theorem weightSetup_of_arena (a : CubeArena.Layout) (w frame axis : ℕ) (mem : ℕ → ℕ)
    (primary : frame+112 ≤ a.header.header) (valid : axis < a.n+1) (high : a.stop < 2^w)
    (million : 1000000 < 2^w) (fit : (weightLayout a frame axis).Fits w mem) :
    (weightLayout a frame axis).SetupRoom w := by
  obtain ⟨head,labels,data,twice,stop⟩ := groupIntervals a
  obtain ⟨powers,weights,totals,owners⟩ := groupPointers a
  have hHead : a.header.header+13 ≤ a.header.packetBase := by unfold CubeHeaderInstall.Inputs.packetBase; omega
  apply GroupWeights.Layout.setupRoom_of_fits fit rfl (Nat.succ_pos _)
  · change frame+75 < 2^w
    omega
  · change a.header.header+7 < 2^w
    omega
  · change a.powerBase+axis < 2^w
    omega
  · exact million
  · change 2*a.alphabet < 2^w
    omega

/-- The native assignment's two writable intervals are disjoint and follow
the exact range of input group words. -/
theorem teamAllocated_of_arena (a : CubeArena.Layout) (w r : ℕ)
    (teams : a.teams = r+1) (high : a.stop < 2^w) : (teamLayout a r).Allocated w := by
  have stop := (groupIntervals a).2.2.2.2
  obtain ⟨_,weights,totals,owners⟩ := groupPointers a
  constructor <;> dsimp only [teamLayout] <;> intros <;> (try have hj := (‹Fin (r+1)›).isLt) <;> omega

/-- The fixed scale constant and the scaled volume fit before either capacity
division. All team total addresses come from the actual allocated table. -/
theorem budgetFits_of_arena (a : CubeArena.Layout) (w frame r X : ℕ)
    (teams : a.teams = r+1) (primary : frame+112 ≤ a.header.header) (high : a.stop < 2^w)
    (million : 1000000 < 2^w) (scaled : 1000000*X*(r+1) < 2^w) :
    (⟨r+1,X,a.teamTotals⟩ : TeamBudget.Layout).Fits frame w := by
  have head := (groupIntervals a).1
  have below := a.separated
  have ext := (groupIntervals a).2.2.2.2
  have hh : a.header.header ≤ a.header.packetBase := by unfold CubeHeaderInstall.Inputs.packetBase; omega
  obtain ⟨_,weights,totals,owners⟩ := groupPointers a
  refine ⟨?_,million,(Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans_lt scaled,scaled,?_⟩
  · have pub := below.2.2.2.1
    have pair := below.2.2.2.2.1
    have endCell := below.2.2.2.2.2
    omega
  · intro i hi
    change i < r+1 at hi
    change a.teamTotals+i < 2^w
    omega

/-- The full primary frame survives all group-weight, team-total, and owner
stores, including the frame fields subsequently read by the guard. -/
theorem groupFrame_before (a : CubeArena.Layout) (frame : ℕ) (primary : frame+112 ≤ a.header.header) :
    frame+112 ≤ a.groupWeights ∧ frame+112 ≤ a.teamTotals ∧ frame+112 ≤ a.ownerBase := by
  obtain ⟨head,labels,data,_,_⟩ := groupIntervals a
  obtain ⟨powers,weights,totals,_⟩ := groupPointers a
  unfold CubeHeaderInstall.Inputs.packetBase at head
  omega

/-- Every addressed primary field lies outside all three scheduling arrays. -/
theorem groupFrame_ne (a : CubeArena.Layout) (frame : ℕ) (primary : frame+112 ≤ a.header.header)
    (k : ℕ) (hk : k < 112) :
    (∀ i, frame+k ≠ a.groupWeights+i) ∧ (∀ j, frame+k ≠ a.teamTotals+j) ∧
      (∀ i, frame+k ≠ a.ownerBase+i) := by
  obtain ⟨hw,ht,ho⟩ := groupFrame_before a frame primary
  exact ⟨fun i => by omega, fun j => by omega, fun i => by omega⟩

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
