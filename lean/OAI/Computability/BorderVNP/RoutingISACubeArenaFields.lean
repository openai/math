import OAI.Computability.BorderVNP.RoutingISACubeArena
import OAI.Computability.BorderVNP.TransmissionJointPacket

/-! # Length-only literal fields for the joint cube, routing and lookup allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally

/-- Scalar installed at an absolute extended-frame position. The geometric
reconstruction fields, actual header and report-scan controls have their own
encoders and remain available through the caller's vector. -/
noncomputable def Layout.operand (l : Layout) : ℕ → Option ℕ
  | 47 => some (CubeConstants.idBase l.stop l.n l.b l.h l.K l.s)
  | 48 => some l.publicBase
  | 49 => some l.heads
  | 50 => some l.nodes
  | 51 => some l.demands
  | 52 => some l.cableMean
  | 53 => some l.dataMean
  | 56 => some l.alphabet
  | 57 => some l.widthBase
  | 58 => some l.ordinalBase
  | 62 => some l.powerBase
  | 72 => some l.hostDirectory
  | 74 => some l.header.d
  | 75 => some l.groupWeights
  | 76 => some l.teamTotals
  | 77 => some l.ownerBase
  | 78 => some l.vertexBase
  | 79 => some (l.stop+2)
  | 81 => some l.stop
  | 82 => some (l.stop+1)
  | 83 => some (argumentWidth l.n l.b l.h l.K l.s)
  | 84 => some (Fintype.card (Vertex (l.n+1)))
  | 85 => some l.pairBase
  | 86 => some l.pairStride
  | 88 => some l.singleBank
  | 91 => some l.pairDirectory
  | 93 => some (bankWidth l.n l.b l.h l.K l.s)
  | 94 => some (selectorWidth l.n l.K l.h)
  | _ => none

/-- Pack the address choices into the true 81-word literal extension. -/
noncomputable def Layout.extension {w : ℕ} (l : Layout) (old : Fin 81 → Word w) (j : Fin 81) : Word w :=
  (l.operand (31+j.val)).elim (old j) (TeamTapeInputEmit.word w)

/-- The actual memory left by the distributed literal copy and native unpacking
contains the intended operand, provided this particular scalar fits. -/
theorem Layout.read_operand {w : ℕ} (l : Layout) (old : Fin 81 → Word w)
    (m : ℕ → ℕ) (frame : ℕ) (resident : ∀ i : Fin 81, m (frame+31+i.val) = (l.extension old i).val)
    {k x : ℕ} (bounds : 31 ≤ k ∧ k ≤ 111) (operand : l.operand k=some x) (fit : x<2^w) :
    m (frame+k)=x := by
  let i : Fin 81 := ⟨k-31,by omega⟩
  have eq : 31+i.val=k := by dsimp [i]; omega
  have r := resident i
  rw [Nat.add_assoc,eq] at r
  simpa [extension,eq,operand,TeamTapeInputEmit.word,Nat.mod_eq_of_lt fit] using r

/-- Fields outside the joint cube allocation still come from their own
geometry, tally or host-task address vector. -/
theorem Layout.extension_other {w : ℕ} (l : Layout) (old : Fin 81 → Word w) (i : Fin 81)
    (h : l.operand (31+i.val)=none) : l.extension old i = old i := by
  simp [extension,h]

/-- Ordinary public operands controlling the actual contiguous routing table.
A native table starts at its true frame-12 pointer and computes its row count
before using these four address banks. -/
def Layout.bootOperand (l : Layout) (frame : ℕ) : ℕ → Option ℕ
  | 13 => some l.records
  | 14 => some 0
  | 17 => some (l.table frame 0).widths
  | 18 => some (l.table frame 0).offsets
  | 19 => some (l.table frame 0).used
  | 21 => some (l.table frame 0).ordinals
  | _ => none

/-- The six operand values are length-only, including when the emitted
descriptor count differs from the reserved row capacity. -/
theorem Layout.boot_table (l : Layout) (frame count : ℕ) :
    l.bootOperand frame 13=some (l.table frame count).records ∧
    l.bootOperand frame 14=some 0 ∧
    l.bootOperand frame 17=some (l.table frame count).widths ∧
    l.bootOperand frame 18=some (l.table frame count).offsets ∧
    l.bootOperand frame 19=some (l.table frame count).used ∧
    l.bootOperand frame 21=some (l.table frame count).ordinals := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
