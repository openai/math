import OAI.Computability.VPVNP.PairVertexDispatch

/-! # Exact consumption of the final vertex call through the histogram flush -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS PrimedCounter.GuessWord
open scoped Fin.CommRing
open private guessed_addFuel from OAI.Computability.VPVNP.PairSimulationDFSDecode
open private execute_component nextConfig word componentEvents from OAI.Computability.VPVNP.PairSimulationCounters

variable {W p r k : ℕ} {M : Machine W p r k}

private theorem returns_after {c d : Config W p r} {m m' : Memory W} {bits tail : List Bool}
    {cost : ℕ} {extend : Report W → Report W}
    (step : ∀ fuel, execute M.program (fuel+cost) c m bits = (execute M.program fuel d m' tail).map extend) :
    Returns M c m bits ↔ Returns M d m' tail := by
  constructor
  · rintro ⟨f,rep,h⟩
    obtain ⟨path,correct,consumed⟩ := execute_iff.mp h
    have big := execute_iff.mpr ⟨guessed_addFuel path cost,correct,consumed⟩
    rw [Nat.add_comm cost f,step] at big
    obtain ⟨out,run,_⟩ := Option.map_eq_some_iff.mp big
    exact ⟨f,out,run⟩
  · rintro ⟨f,out,run⟩
    exact ⟨f+cost,extend out,by rw [step,run]; rfl⟩

/-- The word-arithmetic counter loop terminates even when an arbitrary
incoming private address wraps at the word boundary. The public count is
one word, and the loop advances the external cursor exactly that many times. -/
theorem counters_terminal {pc : Fin 7 → Fin p} {reg : Fin 6 ↪ Fin r} {done : Fin p}
    (linked : Counters.Linked M pc reg done)
    (finish : ∀ (c : Config W p r) m bits, c.pc = done → (Returns M c m bits ↔ bits = []))
    (n : ℕ) (fit : n < 2^W) (c : Config W p r) (m : Memory W) (bits : List Bool)
    (here : c.pc = pc 0) (unit : c.reg (reg 3) = 1) (endWord : c.reg (reg 1) = c.reg (reg 0) + (n : Word W)) :
    Returns M c m bits ↔ bits = [] := by
  induction n generalizing c m with
  | zero =>
    have stop : c.reg (reg 0) = c.reg (reg 1) := by simpa using endWord.symm
    let out := {c with pc := done}
    have hs : M.program.step c = .localStep out := by
      change (M.code c.pc).run _ _ = _
      rw [here,linked]
      change CallAction.localStep {c with pc := if c.reg (reg 0)=c.reg (reg 1) then done else _} = _
      rw [ite_eq_left stop]
    exact (returns_after (cost := 1) (extend := Report.prepend .tick)
      (fun f => by simp only [execute,hs])).trans (finish out m bits rfl)
  | succ n ih =>
    have diff : c.reg (reg 0) ≠ c.reg (reg 1) := by
      intro eqn
      have z : ((n+1 : ℕ) : Word W) = 0 := (add_eq_left.mp (endWord.symm.trans eqn.symm))
      have nat := congrArg Fin.val z
      change (n+1) % 2^W = 0 at nat
      rw [Nat.mod_eq_of_lt fit] at nat
      omega
    let src := (c.reg (reg 2)).val
    let dst := (c.reg (reg 0)).val
    have srcEq : c.reg (reg 2) = word W src := by simp [word,src]
    have dstEq : c.reg (reg 0) = word W dst := by simp [word,dst]
    let mid := nextConfig c pc reg src dst (m dst)
    let mm := writeMemory m (word W dst) (m dst+c.privateMem (word W src))
    have step := returns_after (fun f => execute_component linked c here src dst
      (c.reg (reg 0)).isLt srcEq dstEq unit diff f m bits)
    have endMid : mid.reg (reg 1) = mid.reg (reg 0) + (n : Word W) := by
      simp [mid,nextConfig,word,Config.put,dst,endWord,add_comm,add_assoc]
    exact step.trans (ih (by omega) mid mm rfl (by simpa [mid,nextConfig,Config.put] using unit) endMid)

variable {S : Part → Segment} {A : Placement S p r} {N : Machine W p r 11}

/-- Flush terminality uses no validity premise for the incoming private
memory. This supplies the arbitrary-configuration terminal case of the
DFS equivalence, as well as the case of a successfully prepared histogram. -/
theorem flush_terminal (linked : Contains A N)
    (finish : ∀ (c : Config W p r) m bits, c.pc = A.entry .finish → (Returns N c m bits ↔ bits = []))
    (c : Config W p r) (m : Memory W) (bits : List Bool) (hc : c.pc = A.core (.histBase 0)) :
    Returns N c m bits ↔ bits = [] := by
  obtain ⟨mid,geom,hpc,_,_,_,_⟩ := geometry_run (histBase_linked A N linked)
    (A.counter.injective.ne (by decide)) c hc
  let pc := A.flushStartPC
  let reg := A.counter
  have step (i : Fin 7) (d : Config W p r) (hd : d.pc = pc i) :
      N.program.step d = (flushStartRows pc reg (A.flushPC 0) i).run N.publicData d := by
    change (N.code d.pc).run _ _ = _
    rw [hd,flushStart_linked A N linked]
  let c₁ := mid.put (pc 1) (reg 0) (N.publicData 4)
  let c₂ := c₁.put (pc 2) (reg 4) (N.publicData 5)
  let c₃ := c₂.put (pc 3) (reg 0) (c₂.reg (reg 0)+c₂.reg (reg 4))
  let c₄ := c₃.put (pc 4) (reg 1) (N.publicData 9)
  let c₅ := c₄.put (pc 5) (reg 1) (c₄.reg (reg 0)+c₄.reg (reg 1))
  let c₆ := c₅.put (pc 6) (reg 2) (c₅.privateMem (c₅.reg (reg 2)))
  let start := c₆.put (A.flushPC 0) (reg 3) 1
  have init : Prefix N mid (List.replicate 7 .tick) start :=
    .tick (step 0 mid hpc) (.tick (step 1 c₁ rfl) (.tick (step 2 c₂ rfl) (.tick (step 3 c₃ rfl)
      (.tick (step 4 c₄ rfl) (.tick (step 5 c₅ rfl) (.tick (step 6 c₆ rfl) (.nil _)))))))
  have pre : Prefix N c (List.replicate 10 .tick) start := geom.append init
  apply (returns_after (fun fuel => pre.execute fuel m bits)).trans
  apply counters_terminal (core_linked A N linked).2.2 finish (N.publicData 9).val (N.publicData 9).isLt start m bits rfl
  · change start.reg (reg 3) = 1
    simp [start,Config.put]
  · change start.reg (reg 1) = start.reg (reg 0) + _
    simp [start,c₆,c₅,c₄,c₃,c₂,c₁,Config.put]

/-- The assembled per-site control returns exactly on those streams
accepted by the ordered role visits, with the empty suffix at the flush. -/
theorem site_returns {endAddr : ℕ} (linked : Contains A N) (G offset hist : Word W) (m : Memory W)
    (domain : Word W → Scratch W endAddr → Prop)
    (geometry : ∀ node saved, domain node saved → ResidentGeometry saved G offset hist)
    (handlers : NodeDispatch.Role → HookParser W endAddr)
    (exactRole : ∀ role, (handlers role).ExactOn
      (fun node saved => domain node saved ∧ NodeDispatch.role (m (offset+node).val) = role)
      N (A.entry (rolePart role)) (A.dfsPC 3) A.dfs m)
    (finish : ∀ (c : Config W p r) m bits, c.pc = A.entry .finish → (Returns N c m bits ↔ bits = []))
    {pending nodes : List (Word W)} {events : List (Event W)} (visits : Visits m endAddr pending nodes events)
    (c : Config W p r) (here : c.pc = A.dfsPC 0) (top : ℕ) (stack : Represents c.privateMem top pending)
    (length : top+pending.length = endAddr) (sp : c.reg (A.dfs 5) = (top : Word W))
    (endReg : c.reg (A.dfs 6) = (endAddr : Word W)) (one : c.reg (A.dfs 3) = 1) (bits : List Bool)
    (valid : (dispatcher handlers m offset).ValidAlong domain nodes (scratch endAddr c.privateMem) bits) :
    Returns N c m bits ↔ ∃ out, (dispatcher handlers m offset).decode nodes (scratch endAddr c.privateMem) bits = some (out,[]) := by
  obtain ⟨dfs,copy,_⟩ := core_linked A N linked
  exact returns_iff_decode_on dfs copy visits _ (dispatch_exactOn linked G offset hist m domain geometry handlers exactRole)
    (fun cfg bs h => flush_terminal linked finish cfg m bs h) c here top stack length sp endReg one bits valid

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
