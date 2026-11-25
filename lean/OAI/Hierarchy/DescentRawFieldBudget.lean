import OAI.Hierarchy.DescentFiveRawFields

namespace OAI
/-! # Linear instruction price of the full padded five-column issued graph -/

namespace Hierarchy.DescentOrdinaryRawRows.Five
open ProtocolRAM
variable (S : Sources) (O : Output) (N : Padded.Counts) (b : ℕ)

theorem first_work (f : Column) : (Padded.guarded N.old (S.old b f)).work≤32 := by
  cases f <;> first
    | exact (by decide : 22 ≤ 32)
    | exact (by decide : 17 ≤ 32)
    | exact (by decide : 21 ≤ 32)

theorem new_work (f : Column) (v : Born) : (Padded.guarded N.pairs (S.born b v f)).work≤64 := by
  cases f <;> cases v <;> first
    | exact (by decide : 36 ≤ 64)
    | exact (by decide : 50 ≤ 64)
    | exact (by decide : 11 ≤ 64)

theorem address_work (j : ℕ) : (Padded.address O N j).work≤64 := by
  exact (by decide : 40 ≤ 64)

theorem field_work (f : Column) (oc pc k : ℕ) :
    Padded.passCost S O N b f oc pc k≤4+68*(oc+10*pc)+k*(11+274*pc) := by
  induction k with
  | zero=>
    have := Nat.mul_le_mul_left (oc+10*pc)
      (show 2*(Padded.guarded N.old (S.old b f)).work+4≤68 by have:=first_work S N b f;omega)
    simpa [Padded.passCost,Nat.mul_comm] using Nat.add_le_add_left this 4
  | succ k ih=>
    have ha:=Nat.mul_le_mul_left pc (show 2*(Padded.address O N k).work+4≤132 by have:=address_work O N k;omega)
    have hb:=Nat.mul_le_mul_left pc (show 2*(Padded.guarded N.pairs (S.born b (band k) f)).work+4≤132 by
      have:=new_work S N b f (band k);omega)
    have step : ProtocolRAMGeneratedWrite.work pc (Padded.address O N k)
        (Padded.guarded N.pairs (S.born b (band k) f)) ≤ 11 + 274*pc := by
      unfold ProtocolRAMGeneratedWrite.work
      omega
    change Padded.passCost S O N b f oc pc k + ProtocolRAMGeneratedWrite.work pc (Padded.address O N k)
      (Padded.guarded N.pairs (S.born b (band k) f)) ≤ _
    rw [Nat.succ_mul k (11+274*pc)]
    exact (Nat.add_le_add ih step).trans_eq (Nat.add_assoc _ _ _)

theorem stages_work (base oc pc t : ℕ) :
    steps S N b base oc pc t≤4+t*(114+68*oc+3420*pc) := by
  induction t with
  | zero=>simp [steps]
  | succ t ih=>
    have h:=field_work S (output base oc pc t) N b (column t) oc pc 10
    dsimp [steps,Padded.field_cost]
    rw [Nat.succ_mul]
    omega

theorem five_work (base oc pc : ℕ) : steps S N b base oc pc 5≤574+340*oc+17100*pc := by
  have :=stages_work S N b base oc pc 5
  omega

end Hierarchy.DescentOrdinaryRawRows.Five

end OAI
