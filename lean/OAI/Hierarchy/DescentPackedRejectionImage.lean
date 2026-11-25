import OAI.Hierarchy.DescentPackedRejection
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Deterministic physical image of the packed initial seed rejection -/
namespace Hierarchy.DescentPackedRejection
open DescentSIMDLookup DescentPackedScore ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {a M H r w : ℕ}

def after (out : ℕ) (f : Cell a→ℕ) (x : Fin H→ Fin r→ Cell a) (m : Memory w) :=
  fillSegment out (H*chunks r M+1) (SumScores.word out 1 (scores (M:=M) f x)) m

theorem exact_run (src rom : Bank) (out : ℕ) (f : Cell a→ℕ) (x : Fin H→ Fin r→ Cell a) (m : Memory w)
    (zero : f 0=0) (positive : 0 < M) (sf : src.Fits w out) (rf : rom.Fits w out)
    (rows : H*chunks r M ≤ src.size) (width : rom.bits=a*M) (room : out+(H*chunks r M+1) < 2^w)
    (packed : ∀p : Row H r M,m (src.base+(row H r M p).val)=((data x p).val:Word w))
    (table : Table (M:=M) f rom m) :
    let o:=after (M:=M) out f x m
    (DescentPackedScore.raw src rom out 1 H r M w).Exec m o (4+(H*chunks r M+1)*66) ∧
    (o (out+H*chunks r M)=if ∀v j,f (x v j)=0 then 0 else 1) ∧
    ∀i,i < out ∨ out+(H*chunks r M+1) ≤ i → o i=m i := by
  have reads : SumScores.Reads m (DescentPackedScore.read src rom) (scores (M:=M) f x) := by
    intro i
    let p:=(row H r M).symm i
    have packed_ := packed p
    rw [show row H r M p=i from (row H r M).apply_symm_apply i] at packed_
    have good : (data x p).val < rom.size := by simp [Bank.size,width]
    change rom.read m (src.read m (i.val:Word w))=_
    rw [show src.read m (i.val:Word w)=m (src.base+i.val) by
      simp [Bank.read,Fin.val_cast_of_lt ((i.isLt.trans_le rows).trans sf.2.1),Nat.mod_eq_of_lt (i.isLt.trans_le rows)],packed_]
    rw [show rom.read m ((data x p).val:Word w)=m (rom.base+(data x p).val) by
      simp [Bank.read,Fin.val_cast_of_lt (good.trans rf.2.1),Nat.mod_eq_of_lt good]]
    exact table _
  have fits : (∑i,scores (M:=M) f x i) ≤ H*chunks r M := by
    calc
      _ ≤ ∑_ : Fin (H*chunks r M),1 := Finset.sum_le_sum fun i _=>by
        dsimp [scores,badChunk];split <;> decide
      _ = _ := by simp
  refine ⟨?_,?_,?_⟩
  · intro P R K machine pc reg pub exit installed data cfg input start eqn
    subst input
    exact SumScores.run out 1 (DescentPackedScore.read src rom) (scores (M:=M) f x)
      (show (DescentPackedScore.read src rom).Fits w out from ⟨rf,sf,trivial⟩)
      room (by omega) (by omega) machine pc reg pub exit installed data cfg m start reads
  · unfold after
    rw [SumScores.read_flag]
    have char:=invalid_iff f zero x positive
    by_cases z : (∑i,scores (M:=M) f x i)=0
    · simp [z,char.mp z]
    · rw [ite_eq_left (show 1 ≤ _ from Nat.pos_of_ne_zero z),ite_eq_right (mt char.mpr z)]
  · intro i apart
    simp [after,fillSegment,show ¬(out ≤ i ∧ i < out+(H*chunks r M+1)) by omega]

end
end Hierarchy.DescentPackedRejection

end OAI
