import OAI.Computability.BorderVNP.CubeTeamOwnedPhysicalSetup
import OAI.Computability.BorderVNP.CubeScatterArenaAllocation
import OAI.Computability.BorderVNP.CubeISALocalRowArena
import Mathlib.Data.Nat.Choose.Bounds

/-! # Row directory, table, and pointer bounds for an actual evaluation arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned BorderVNP.Cube.TeamRows
open BorderVNP.Cube.Tally BorderVNP.Cube.Padding.Banks BorderVNP.Cube.TeamRowSources VPVNP.BurstRAM

/-- Native fixed-length selector spelling for every distinct symbol row of the arena. -/
def Layout.rowSelectorBits (a : Layout) := a.header.volume a.n (selectorWidth a.n a.K a.h)

/-- The true selector-prefix field equals the number of raw selector bits used
by the side iterator. -/
theorem Layout.rowSelectorBits_eq (a : Layout) : a.rowSelectorBits =
    2*a.header.blocks*(a.header.d.choose 2)^a.n*
      VPVNP.MotifWidths.selectorBits a.K (Fintype.card (Edge (a.n+1))) a.h := by
  simp [rowSelectorBits,CubeHeaderInstall.Inputs.volume,selectorWidth,VPVNP.MotifWidths.selectorBits,Selector]

/-- The real native row inputs and the geometric local-check inputs have the
same layout when the packet base is placed at its arena address. -/
theorem Layout.rowLayout_eq (a : Layout) (frame team axis sels : ℕ)
    (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s) (packet : A.packetBase = a.header.packetBase) :
    TeamRowSources.rowLayout A (a.scanner frame team axis sels) a.powerBase =
      LocalRow.rowLayout a.header a.b a.h a.powerBase := by
  simp [TeamRowSources.rowLayout,LocalRow.rowLayout,scanner,packet]

/-- The allocated directory covers all triples emitted by a team, including a
team that owns both roles of every strict row. -/
theorem Layout.scanner_capacity (a : Layout) (frame team axis sels : ℕ) (owner : ℕ → ℕ) :
    let l := a.scanner frame team axis sels
    a.vertexBase+3*vertexPrefix l owner a.n a.header.blocks (l.d*l.d) ≤ a.publicBase := by
  intro l
  have each : strictVertices a.n a.header.d a.header.blocks ≤
      packetTrials a.n a.header.d a.header.blocks*2^(a.n+1) := by
    have ch : a.header.d.choose 2 ≤ a.header.d*a.header.d := by
      simpa only [pow_two] using Nat.choose_le_pow a.header.d 2
    have pow := Nat.pow_le_pow_left ch a.n
    have slots := Nat.mul_le_mul_left (2*a.header.blocks) pow
    have corners : 2^a.n ≤ 2^(a.n+1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ _)
    have bounds := Nat.mul_le_mul slots corners
    simpa only [strictVertices,packetTrials,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bounds
  have num : vertexPrefix l owner a.n a.header.blocks (l.d*l.d) ≤ a.vertexCap := by
    unfold vertexPrefix
    calc
      _ ≤ ∑ _k ∈ Finset.range (l.d*l.d), packetTrials a.n a.header.d a.header.blocks*2^(a.n+1) := by
        apply Finset.sum_le_sum
        intro k _
        split
        · exact each
        · exact Nat.zero_le _
      _ = a.vertexCap := by simp [vertexCap,l,scanner,pow_two,Nat.mul_assoc]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 3 num) _

/-- All native outer row cursor calculations fit in the shared arena. -/
theorem Layout.scanner_fits (a : Layout) (w frame team axis : ℕ)
    (low : frame+112 ≤ a.header.header) (high : a.stop < 2^w) (square : a.header.d*a.header.d < 2^w) :
    (a.scanner frame team axis a.rowSelectorBits).Fits w := by
  let l := a.scanner frame team axis a.rowSelectorBits
  have bank := a.separated
  have pr := a.source_order
  have pairStop : a.pairBase ≤ a.stop := (Nat.le_add_right _ _).trans (bank.2.2.2.2.1 ▸ bank.2.2.2.2.2)
  have header : a.header.header+13 ≤ a.packetEnd := by
    unfold packetEnd CubeHeaderInstall.bankStop CubeHeaderInstall.Inputs.packetBase
    omega
  have endTo : a.packetEnd < a.publicBase := by
    have before := bank.2.1
    unfold singleBank at before
    unfold publicBase
    omega
  refine ⟨by dsimp only [scanner]; omega,by dsimp only [scanner]; omega,square,pr.2.2.trans (pairStop.trans high.le),?_⟩
  intro q hq
  change q < a.header.d*a.header.d at hq
  have iq := Nat.mul_le_mul_left a.pairStride hq
  rw [Nat.mul_succ] at iq
  have endView : a.pairBase+a.pairStride*(a.header.d*a.header.d) ≤ a.stop := by
    rw [← pow_two,Nat.mul_comm]
    exact bank.2.2.2.2.1 ▸ bank.2.2.2.2.2
  have sz : a.rowSelectorBits < a.pairStride := by unfold rowSelectorBits pairStride; omega
  change a.pairBase+a.pairStride*q+(if q/a.header.d=q%a.header.d then 0 else a.rowSelectorBits) < 2^w
  split <;> omega

/-- The actual declared table and H[0], H[1] reside in the protected sources of
the outer scan, so future row writes cannot invalidate their word addresses. -/
theorem Layout.checkImage (a : Layout) {w : ℕ} (frame team axis sels : ℕ)
    (A : Data a.n a.header.d a.header.blocks a.b a.h a.K a.s)
    (m : Memory w) (rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ) (axes : a.header.a = a.n+1)
    (actual : readings m a.header.header = a.header.header+13)
    (claimed : readings m (a.header.header+1) = a.header.header+13+a.header.entries)
    (table : CubeLengths.StoredRows (readings m) (a.header.header+13+a.header.entries) rows) :
    let l := a.scanner frame team axis sels
    CheckImage (TeamRowSources.rowLayout A l a.powerBase) (source l a.powerBase a.n) a.n
      (a.header.header+13) (a.header.header+13+a.header.entries) rows m := by
  intro l
  refine ⟨actual,claimed,table,?_,?_⟩
  · have he (k : ℕ) (hk : k < 13) : a.header.header+k ∈ source l a.powerBase a.n :=
      Or.inr (Or.inl (Or.inl (Or.inr ⟨Nat.le_add_right ..,Nat.add_lt_add_left hk _⟩)))
    exact ⟨he 0 (by decide),he 1 (by decide)⟩
  · intro u v j
    have hv := (CubeLengths.entryOrder a.header.d (a.n+1) ((u,v),j)).isLt
    apply Or.inl
    apply Or.inl
    change _ ≤ _ ∧ _ < _
    simp only [l,scanner,TeamRowSources.rowLayout,CubeHeaderInstall.Inputs.entries,axes] at *
    omega

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
