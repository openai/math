import OAI.ThreeFlat.Diagonal.PhysicalNodeCountSpace
import OAI.ThreeFlat.Diagonal.PhysicalNodeHeaderSpace
import OAI.ThreeFlat.Diagonal.PublicationLayerBounds
import OAI.ThreeFlat.Diagonal.TickWorkspace

namespace OAI
/-! # Word addresses of the chronological node publisher -/

namespace ThreeFlat.Diagonal.NavigationPass

open NavigationDirectory PhysicalStage

/-- The control, header, charge and directory addresses of a mounted publisher,
including the physical heap containing each previous layer's owner array. -/
structure NodeArchive.PublicationSpace (a : NodeArchive) (u heapEnd : ℕ) (rows : List Layers) : Prop where
  wide : 16 < 2^(16*u^10)
  current : a.banks.current < a.banks.charges
  counter : a.counter < a.headerBase
  header : a.headerBase + 16*rows.length ≤ a.banks.charges
  heapBeforeCharges : TickWorkspace.base u 22 + TickWorkspace.stride u ≤ a.banks.charges
  heap : heapEnd ≤ a.banks.charges
  chargeEnd : a.banks.charges + 2*(rows.map (fun z => z.actual.count)).sum ≤ a.banks.nodes
  nodeEnd : a.banks.nodes + 8*(rows.map (fun z => z.actual.count)).sum < 2^(16*u^10)
  span : ∀ z ∈ rows, a.banks.charges + 2*(z.actual.first+z.actual.count) ≤ a.banks.nodes ∧
    a.banks.nodes + 8*(z.actual.first+z.actual.count) < 2^(16*u^10)

set_option maxHeartbeats 800000 in
/-- All the addresses used to publish the complete repeated physical program fit
the selected word size, both collectively and at every actual layer. -/
theorem Parameters.node_publication_arena {F : Type} [Field F] [Fintype F] (B : Block F)
    (u rem low stride cells : ℕ) (shape : RAM.PhysicalPinsExpr.Shape) (tableOffset unitWork : ℕ)
    (hu : 40 ≤ u) (levels : B.levels+1 ≤ u) (factor : B.allocations.sum ≤ u)
    (half : low = u^10/2) (depth : (B.repeat (u^8)).charge+rem+low ≤ u^10+2*u^6) :
    let p := Parameters.cursor B u rem low stride cells shape tableOffset unitWork
    let A := p.archive (2^(B.exponent 0)) (16*u^10)
    let ss := (B.repeat (u^8)).directory rem p.axes
    let D := p.nodeArchive A ss (16*u^10)
    let rows := nodeLayers A.K ss A.cursor A.seedLayer
    D.PublicationSpace u (finish A.K ss A.cursor).heap rows := by
  intro p A ss D rows
  have word := node_word_space hu
  have headers : 16*rows.length ≤ TickWorkspace.stride u := by
    change 16*(nodeLayers A.K ss A.cursor A.seedLayer).length ≤ _
    rw [nodeLayers_length]
    exact B.directory_header_space hu levels rem p.axes
  have counts := node_count_space B p hu levels factor half depth (by rfl)
  have rowBound : ∀ z ∈ rows, 8*(z.actual.first+z.actual.count) ≤ 2^(u^10-u^4) := counts.1
  have totalBound : 8*(rows.map (fun z => z.actual.count)).sum ≤ 2^(u^10-u^4) := counts.2.2
  have register : 2^(u^10-u^4) ≤ TickWorkspace.stride u :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le (u^10) (u^4))).trans
      (Nat.le_self_pow (by decide : 4 ≠ 0) _)
  have heapRoom : (finish A.K ss A.cursor).heap ≤ TickWorkspace.base u 22 + TickWorkspace.stride u :=
    cursor_heap_end B hu levels factor half depth A.K A.cursor
  have heapCap : TickWorkspace.base u 22 + TickWorkspace.stride u ≤ D.banks.charges :=
    TickWorkspace.apart (by decide : 22 < 43)
  have starts : D.banks.current + TickWorkspace.stride u ≤ D.headerBase :=
    TickWorkspace.apart (by decide : 40 < 41)
  have endHeader : D.headerBase + TickWorkspace.stride u ≤ D.banks.charges :=
    TickWorkspace.apart (by decide : 41 < 43)
  have endCharges : D.banks.charges + TickWorkspace.stride u ≤ D.banks.nodes :=
    TickWorkspace.apart (by decide : 43 < 44)
  have endNodes : D.banks.nodes + TickWorkspace.stride u < 2^(16*u^10) :=
    TickWorkspace.word_space (by omega : 1 ≤ u) word.2
  have ends (n : ℕ) (hn : 8*n ≤ 2^(u^10-u^4)) :
      D.banks.charges + 2*n ≤ D.banks.nodes ∧ D.banks.nodes + 8*n < 2^(16*u^10) := by
    have limit := hn.trans register
    exact ⟨(Nat.add_le_add_left (by omega : 2*n ≤ TickWorkspace.stride u) _).trans endCharges,
      (Nat.add_le_add_left limit _).trans_lt endNodes⟩
  have ctr : D.counter = D.banks.current+3 := rfl
  obtain ⟨charges,nodes⟩ := ends _ totalBound
  refine ⟨word.1,?_,?_,(Nat.add_le_add_left headers _).trans endHeader,heapCap,heapRoom.trans heapCap,
    charges,nodes,fun z hz => ends _ (rowBound z hz)⟩
  · have positive := word.2
    omega
  · rw [ctr]
    have positive := word.2
    omega

end ThreeFlat.Diagonal.NavigationPass

end OAI
