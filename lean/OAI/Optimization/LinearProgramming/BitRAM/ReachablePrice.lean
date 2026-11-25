import OAI.Optimization.LinearProgramming.BitRAM.DispatchPrefixFacts
import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame
import OAI.Optimization.LinearProgramming.OracleSpec.CompilerProof

/-! A completed PCG machine certificate validates each price packet before its numeric
callback is evaluated, including on branches with arbitrary inconsistent answers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open OracleSpec

private theorem tick_keeps_entry {p : BitProgram} {o : WordOracle} {a t : p.Config} {n : ℕ}
    (edge : p.tick o a=some (n,t)) {e : Word × Word} (mem : e∈a.transcript) : e∈t.transcript := by
  cases pc : a.pc with
  | none => simp [BitProgram.tick,pc] at edge
  | some q =>
    cases row : p.instruction q (a.store (p.scan q)).head? <;>
      simp [BitProgram.tick,pc,row] at edge <;> obtain ⟨rfl,rfl⟩ := edge <;>
      first | exact mem | exact List.mem_cons_of_mem _ mem

theorem run_keeps_entry {p : BitProgram} {o : WordOracle} {a t : p.Config} {n : ℕ}
    (run : p.Run o a n t) {e : Word × Word} (mem : e∈a.transcript) : e∈t.transcript := by
  induction run with
  | refl => exact mem
  | step edge _ ih => exact ih (tick_keeps_entry edge mem)

/-- The reported time bound includes the complete current question after every earlier
instruction. The frozen contract provides a true index and a full-dimensional rational vector. -/
theorem reachable_price_request {p : BitProgram} {N R budget used : ℕ} {a : Fin N}
    (reply : Transcript → Word → Bool)
    (valid : p.ComputesWithin (fun h w => [reply h w]) (priceInput R a) budget (pricePost R a))
    {c : p.Config} (pre : p.Run (fun h w => [reply h w]) (p.initial (priceInput R a)) used c)
    {pc next : Fin p.states} (live : c.pc=some pc)
    (ask : p.instruction pc (c.store (p.scan pc)).head? = .ask next) :
    (∃ i : Fin N, ∃ prices : Fin N → ℚ, c.bufferRev.reverse = priceQuery i prices) ∧
      used+2+c.bufferRev.reverse.length ≤ budget := by
  let bo : WordOracle := fun h w => [reply h w]
  have edge := tick_ask (bo := bo) live ask
  have after := pre.append (BitProgram.Run.single edge)
  obtain ⟨total,out,whole,bound,ended,post⟩ := valid
  obtain ⟨rest,hk,finish⟩ := suffix_of_bit_prefix after whole ended
  let packet := c.bufferRev.reverse
  let pair := (packet,bo c.transcript packet)
  have entry : pair∈(answered bo c next).transcript := List.mem_cons_self
  have shape := post.1 pair (run_keeps_entry finish entry)
  refine ⟨shape,?_⟩
  change used+(1+c.bufferRev.reverse.length+1)+rest=total at hk
  omega

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
