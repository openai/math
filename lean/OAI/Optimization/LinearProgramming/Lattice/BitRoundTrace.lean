import OAI.Optimization.LinearProgramming.Lattice.BitRoundState

/-! Physical requests paired with their exact live continuations. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
open OracleSpec

abbrev Request := Word × Carry

/-- A finite sequence of requests with the actual continuation kept at each request. -/
inductive Dialogue (f : Kernels) (reply : Word → Word) : Action → List Request → Word → Prop
  | done (out : Word) : Dialogue f reply (.inl out) [] out
  | ask {q c steps out} (tail : Dialogue f reply (dispatch f (.inr (reply q,c))) steps out) :
      Dialogue f reply (.inr (q,c)) ((q,c)::steps) out

def rowOracle (reply : Word → Word) (a : Row) : Bool := nonnegativeAnswer (reply (signPacket a))

/-- Any finite probe, including its final reduction decision, embeds in the same word
controller. Its prefix retains the exact dispatched rows and their actual reachable states. -/
theorem probeDialogue (f : Kernels) (reply : Word → Word) (env : Env) {origin a : Probe.Action}
    {qs : List Row} {r : Probe.Result} (h : Probe.Runs (rowOracle reply) a qs r)
    (ha : Probe.Reaches origin a) {tail : List Request} {out : Word}
    (final : Dialogue f reply (receiveProbe f env (.inl r)) tail out) :
    ∃ pre : List Request, Dialogue f reply (receiveProbe f env a) (pre++tail) out ∧
      pre.map Prod.fst = qs.map signPacket ∧
      ∀ u ∈ pre, ∃ row c, u = (signPacket row,(env,c)) ∧ Probe.Reaches origin (.inr (row,c)) := by
  induction h with
  | done r => exact ⟨[], final, rfl, by simp⟩
  | @ask row c qs r _ ih =>
    obtain ⟨pre,run,hpack,reach⟩ := ih (ha.step (rowOracle reply row)) final
    refine ⟨(signPacket row,(env,c))::pre, Dialogue.ask run, ?_, ?_⟩
    · simp [hpack]
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hm
      · exact ⟨row,c,rfl,ha⟩
      · exact reach u hm

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
