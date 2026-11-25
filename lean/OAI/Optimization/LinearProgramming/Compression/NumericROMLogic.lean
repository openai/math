import OAI.Optimization.LinearProgramming.Compression.InnerRAMAdapter

/-! Recover the canonical finite request position and specialize the inner bit machine
and its reachable-call guarantee to the exact stored magnitude vector. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec SignWire

/-- The manuscript service clock, assembled explicitly from the underlying bit procedures. -/
noncomputable def numericInnerClock : Polynomial ℕ := Inner.clock

noncomputable def numericWordOracle {g : ℕ} (n : ℕ) (mag : Fin (g+1) → ℚ) : WordOracle :=
  cachedWordOracle (g+1) (manuscriptProxyFuel n) (paperRadius n+7) (RAM.start [] (List.ofFn mag)).data

/-- The public membership/rank protocol selects the same representation as the
mathematical shared-minor request. All allowed calls have room in the physical arena. -/
theorem numericInner_run {n g : ℕ} (hg : g≤paperWidth n) (pos : Option (Fin g)) (rank : ℕ)
    (hr : rank≤g) (hit : ∀ i,pos=some i → i.val=rank) (mag : Fin (g+1)→ℚ) (hp : ∀ i,0 < mag i) :
    let w := Inner.inputWord n g pos.isSome rank
    let bo := numericWordOracle n mag
    let q := numericInnerClock.eval n
    let value := numericalValue n pos mag
    (∃ steps≤q, ∃ d : Inner.machine.Config, Inner.machine.Run bo (Inner.machine.initial w) steps d ∧
      d.pc=none ∧ d.bufferRev.reverse=Inner.outputWord value) ∧
      BitRAM.Dispatch.PermittedAsksFrom Inner.machine bo
        (AllowedSignPacket (g+1) (q+1) (Inner.coefficientCap n) Inner.machine) (Inner.machine.initial w) ∧
      (Inner.outputWord value).length≤q := by
  obtain ⟨hpos,member⟩ := Inner.position_of_coherent pos rank hit
  let tape : ℕ → ℚ := (RAM.start [] (List.ofFn mag)).data
  have tape_at (i : Fin (g+1)) : tape i = mag i := by
    change ((List.ofFn mag)[i.val]?).getD 0 = mag i
    rw [List.getElem?_ofFn, dite_eq_left i.isLt]
    rfl
  have hp' (i : Fin (g+1)) : 0 < tape i := by
    rw [tape_at i]
    exact hp i
  obtain ⟨computes,valid,word⟩ := Inner.machine_cached_clock n g hg pos.isSome rank hr
    member tape hp'
  have hm : (fun i : Fin (g+1) => tape i)=mag := funext tape_at
  rw [hpos,hm] at computes word
  obtain ⟨steps,d,run,limit,halt,result,_⟩ := computes
  refine ⟨⟨steps,limit,d,run,halt,result⟩,?_,word⟩
  intro u k q next front pc ask
  obtain ⟨before,rest⟩ := valid u k q next front pc ask
  exact ⟨Nat.lt_succ_of_lt before,rest⟩

end Compression
end LinearProgramming
end Optimization
end OAI
