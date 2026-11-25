import OAI.Optimization.LinearProgramming.Geometry.WirePredicates
import OAI.Optimization.LinearProgramming.Contraction.MachineExchange

/-! A named final transcript certifies the actual packet at each executed oracle edge. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Contract OracleSpec Contraction.Machine

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem oracleStep_history_extension {p : OracleProgram} {o : ScalarOracle K} {u v : Config K} {c : ℕ}
    (edge : oracleStep p o u=some (c,v)) : ∃ new : Contract.History K, v.history=new++u.history := by
  obtain ⟨st,hist⟩ := u
  cases stop : st.output with
  | some tag => simp [oracleStep,stop] at edge
  | none =>
    cases ins : p[st.pc]? with
    | none => simp [oracleStep,stop,ins] at edge
    | some instruction =>
      cases instruction with
      | core i =>
        cases act : execInstr i st with
        | none => simp [oracleStep,stop,ins,act] at edge
        | some z =>
          have step := core_instruction p o st z hist i ins stop act
          rw [step] at edge
          cases edge
          exact ⟨[],rfl⟩
      | query src len dst size =>
        have step := query_exchange p o st hist ins stop
        dsimp only at step
        rw [step] at edge
        cases edge
        exact ⟨[(_,_)],rfl⟩

/-- Every earlier exchange remains in the physical history of the same run. -/
theorem oracleRun_history_extension {p : OracleProgram} {o : ScalarOracle K} {u v : Config K} {k : ℕ}
    (run : OracleRun p o u k v) : ∃ new : Contract.History K, v.history=new++u.history := by
  induction run with
  | refl => exact ⟨[],rfl⟩
  | next edge tail ih =>
    obtain ⟨one,h₁⟩ := oracleStep_history_extension edge
    obtain ⟨later,h₂⟩ := ih
    exact ⟨later++one,by rw [h₂,h₁,List.append_assoc]⟩

/-- The latest history entry contains exactly the caller's submitted scalar words. -/
theorem oracleQuery_history {p : OracleProgram} {o : ScalarOracle K} {u v : Config K}
    {c src len dst count : ℕ} (instr : p[u.state.pc]?=some (.query src len dst count))
    (edge : oracleStep p o u=some (c,v)) :
    v.history=(registerPacket u.state src len,o u.history (registerPacket u.state src len))::u.history := by
  obtain ⟨st,hist⟩ := u
  have live : st.output=none := by
    cases h : st.output with
    | none => rfl
    | some _ => simp [oracleStep,h] at edge
  have step := query_exchange p o st hist instr live
  dsimp only at step
  exact congrArg (fun x : ℕ × Config K => x.2.history) (Option.some.inj (edge.symm.trans step))

/-- At an individual executed query the words in the caller's specified scalar block
encode a genuine nonzero minor. This uses only the final named transcript and the
remaining execution; unrelated temporary registers need no semantic interpretation. -/
theorem NamedTraffic.query_edge {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
    {p : OracleProgram} {o : ScalarOracle ℚ} {u v final : Config ℚ} {c k src len dst size : ℕ}
    (known : NamedTraffic D E final.history) (instr : p[u.state.pc]?=some (.query src len dst size))
    (edge : oracleStep p o u=some (c,v)) (rest : OracleRun p o v k final) :
    let sent := registerPacket u.state src len
    let ans := o u.history sent
    ∃ minor : MinorLog.Index D E, sent=(MinorLog.words minor.val).map Nat.cast ∧ (ans=[1] ∨ ∃ q, ans=[0,q]) := by
  have past := oracleQuery_history instr edge
  obtain ⟨extra,historia⟩ := oracleRun_history_extension rest
  apply known (registerPacket u.state src len,o u.history (registerPacket u.state src len))
  rw [historia,past]
  simp

/-- Only the newly produced packets need to be valid. The incoming history may
contain unrelated packets or come from an earlier service epoch. -/
theorem NamedTraffic.query_edge_recent {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}
    {p : OracleProgram} {o : ScalarOracle ℚ} {u v final : Config ℚ} {c k src len dst size : ℕ}
    {old fresh : Contract.History ℚ} (known : NamedTraffic D E fresh) (shape : final.history=fresh++old)
    (seen : ∃ prior, u.history=prior++old) (instr : p[u.state.pc]?=some (.query src len dst size))
    (edge : oracleStep p o u=some (c,v)) (rest : OracleRun p o v k final) :
    let sent := registerPacket u.state src len
    ∃ minor : MinorLog.Index D E, sent=(MinorLog.words minor.val).map Nat.cast := by
  let sent := registerPacket u.state src len
  let w := (sent,o u.history sent)
  obtain ⟨prior,hp⟩ := seen
  obtain ⟨afterQuery,ha⟩ := oracleRun_history_extension rest
  have ep : v.history=w::u.history := oracleQuery_history instr edge
  have same : fresh++old=(afterQuery++w::prior)++old := by
    rw [←shape,ha,ep,hp]
    simp only [List.append_assoc,List.cons_append]
  have freshEq := List.append_cancel_right same
  have mem : w∈fresh := by rw [freshEq]; simp
  obtain ⟨minor,eq,_⟩ := known w mem
  exact ⟨minor,eq⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
