import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.ProgramDirectoryData

namespace OAI
/-! # Stage count of the physical program on each realized history -/

namespace ThreeFlat.Diagonal.PhysicalStage.Program
variable {F : Type} [Field F]

theorem stageLength_recast {d l l' n : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) : (recast e A r).StageLength n ↔ r.StageLength n := by
  cases e
  rfl

theorem stageLength_run {s : ℕ} (P : Program F s) (r : ℕ) (A : State (2^s) (P.charge+r)) :
    (P.run r A).StageLength P.length := by
  induction P with
  | done s => rfl
  | shrink s t T small tail ih =>
    let eqv:=Nat.add_assoc (shrinkCharge s) tail.charge r
    let B : State (2^s) (shrinkCharge s+(tail.charge+r)):=eqv ▸ A
    let R:=shrinkBinary T s (2^t) (tail.charge+r) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    exact (stageLength_recast (n:=tail.length+1) eqv A (Run.step R (fun i=>tail.run r (R.next i)))).mpr
      (fun i=>ih _)
  | refresh s t h pad c γ C T hm hh sym rows loopless conn degree tail ih =>
    let eqv:=Nat.add_assoc s tail.charge r
    let B : State (2^s) (s+(tail.charge+r)):=eqv ▸ A
    let R:=recastMove degree (refreshBinary T B hm hh sym rows loopless conn)
    exact (stageLength_recast (n:=tail.length+1) eqv A (Run.step R (fun i=>tail.run r (R.next i)))).mpr
      (fun i=>ih _)

end ThreeFlat.Diagonal.PhysicalStage.Program

end OAI
