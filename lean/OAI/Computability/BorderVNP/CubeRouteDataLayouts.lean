import OAI.Computability.BorderVNP.RoutingISACellBankPhysical
import OAI.Computability.BorderVNP.RoutingISACubeArenaPreserveGroups

/-! # Physical layouts of the two directories preceding the data writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube VPVNP.BurstRAM

/-- Cell receiving addresses, using the actual declared coordinate and its positional divisor. -/
def Layout.cellWriter (a : Layout) (frame controls : ℕ) (axis : Fin (a.n+1)) : CellBanks.Layout :=
  ⟨frame,a.cells,a.header.d,a.publicBase,a.ownerBase,a.hostDirectory,a.cellBank,a.cellStride,
    a.powerBase,a.header.header,controls,axis.val,a.header.d^axis.val⟩

/-- Three words per ordered pair of product labels in the public pair directory. -/
def Layout.pairWriter (a : Layout) (frame : ℕ) : PairDirectory.Layout :=
  ⟨frame,a.header.header,a.header.d,a.n+1,a.header.blocks,a.pairDirectory⟩

/-- Address ordering around the two native output directories. -/
theorem Layout.writer_order (a : Layout) :
    a.header.header+13 ≤ a.publicBase ∧ a.publicBase+a.cells ≤ a.groupWeights ∧
    a.groupWeights ≤ a.ownerBase ∧ a.ownerBase+a.header.d = a.pairDirectory ∧
    a.pairDirectory+3*a.alphabet^2 = a.hostDirectory ∧ a.hostDirectory+2*a.cells = a.records ∧
    a.records+7*a.maxRows ≤ a.pairBase ∧ a.pairBase ≤ a.stop := by
  obtain ⟨_,heads,_,_,_,_,power,_,_,_,_,_⟩ := a.group_order
  have hp : a.header.packetBase ≤ a.publicBase := by
    dsimp only [Layout.publicBase,Layout.vertexBase,Layout.singleBank,Layout.packetEnd,CubeHeaderInstall.bankStop]
    omega
  dsimp only [CubeHeaderInstall.Inputs.packetBase] at hp
  refine ⟨by omega,?_,?_,rfl,rfl,rfl,?_,?_⟩
  · dsimp only [Layout.groupWeights,Layout.powerBase,Layout.ordinalBase,Layout.widthBase,Layout.dataMean,
      Layout.cableMean,Layout.demands,Layout.nodes,Layout.heads]; omega
  · dsimp only [Layout.ownerBase,Layout.teamTotals]; omega
  · dsimp only [Layout.pairBase,TableLayout.reserveEnd]; omega
  · dsimp only [Layout.stop,Layout.cellBank]; omega

/-- All field arithmetic of the cell-bank installer fits into the one physical arena. -/
theorem Layout.cellWriter_fits (a : Layout) (frame controls : ℕ) (axis : Fin (a.n+1)) {w : ℕ}
    (positive : 0 < a.header.d) (low : frame+112 ≤ a.header.header)
    (ctl : controls+10 < a.header.header) (room : a.stop < 2^w) :
    (a.cellWriter frame controls axis).Fits w := by
  obtain ⟨hh,lab,gw,own,pair,host,rec,stop⟩ := a.writer_order
  have hp : a.powerBase+(a.n+1) = a.groupWeights := rfl
  have ha := axis.isLt
  constructor <;> dsimp only [cellWriter] <;> first | exact positive | exact pow_pos positive _ | exact room | omega

/-- The same allocator also covers unscaled pair ranks, binary vertex numbers, and
all scaled packet ordinals, even if no physical blocks are required. -/
theorem Layout.pairWriter_fits (a : Layout) (frame : ℕ) {w : ℕ}
    (two : 2 ≤ a.header.d) (bank : 0 < Cube.Tally.bankWidth a.n a.b a.h a.K a.s)
    (low : frame+112 ≤ a.header.header) (room : a.stop < 2^w) : (a.pairWriter frame).Fits w := by
  obtain ⟨hh,lab,gw,own,pair,host,rec,stop⟩ := a.writer_order
  have group : a.powerBase+(a.n+1) = a.groupWeights := rfl
  have positive : 0 < a.header.d := by omega
  have sym : a.header.d ≤ a.alphabet := by
    exact (pow_one a.header.d ▸ Nat.pow_le_pow_right positive (by omega : 1 ≤ a.n+1))
  have binary : 2^(a.n+1) ≤ a.alphabet := Nat.pow_le_pow_left two _
  have alph : 0 < a.alphabet := pow_pos positive _
  have small := Nat.le_mul_of_pos_right a.alphabet alph
  have square := Nat.mul_le_mul sym sym
  have pkt : a.packetEnd ≤ a.publicBase := by
    dsimp only [Layout.publicBase,Layout.vertexBase,Layout.singleBank]; omega
  have used := Nat.le_mul_of_pos_right ((a.alphabet*a.alphabet)*2*a.header.blocks) bank
  have exactEnd : a.packetEnd = a.header.packetBase + (a.alphabet*a.alphabet)*2*a.header.blocks*
      Cube.Tally.bankWidth a.n a.b a.h a.K a.s := by simp [Layout.packetEnd,CubeHeaderInstall.bankStop,mul_pow,Layout.alphabet]
  have count : (a.pairWriter frame).count = a.alphabet*a.alphabet := rfl
  rw [pow_two] at pair
  refine ⟨positive,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.n+1 < _; omega
  · change a.header.d*a.header.d < _; omega
  · change 2^(a.n+1) < _; omega
  · change 2*((a.pairWriter frame).count)*(a.header.blocks+1) < _
    rw [count,Nat.mul_add,Nat.mul_one,Nat.mul_comm 2 (a.alphabet*a.alphabet)]
    omega
  · change a.pairDirectory+3*((a.pairWriter frame).count) < _
    rw [count]; omega
  · change frame+91 < _; omega
  · change a.header.header+7 < _; omega

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
