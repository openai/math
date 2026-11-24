import OAI.Computability.VPVNP.PairSimulationRoutePrepare
import OAI.Computability.VPVNP.PairSimulationLeafBootRows

/-!
# Passing the decoded leaf and its private-arena pointers to the verifier

The routing scan may reuse its cache-address temporary. After a cursor-zero
success the parent reloads the frame's cache pointer and computes the node
argument base from the preserved node word, the arena stride, and the arena
start. All seven instructions are private and deterministic.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafBootHandoff

open BurstRAM PrivateRAM RAMTape PrimedCounter.GuessWord NodeArguments
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Seven native operand transfers from a successful route to the leaf initializer. -/
def instruction (pc : Fin 7 → Fin p) (boot : LeafBoot.Reg ↪ Fin r) (leaf : LeafAddress.Reg ↪ Fin r)
    (pub : RoutePrepare.Field → Fin k) (done : Fin p) : Fin 7 → Instr w p r k :=
  ![.copy (LeafBoot.sources boot .address) (leaf .site) (pc 1),
    .copy (LeafBoot.sources boot .header) (leaf .header) (pc 2),
    .publicWord (LeafBoot.cacheBase boot) (pub .cache) (pc 3),
    .publicWord (LeafBoot.tmp boot) (pub .stride) (pc 4),
    .binary .mul (LeafBoot.nodeBase boot) (leaf .node) (LeafBoot.tmp boot) (pc 5),
    .publicWord (LeafBoot.tmp boot) (pub .start) (pc 6),
    .binary .add (LeafBoot.nodeBase boot) (LeafBoot.tmp boot) (LeafBoot.nodeBase boot) done]

theorem resize_instruction (pc : Fin 7 → Fin p) (boot : LeafBoot.Reg ↪ Fin r) (leaf : LeafAddress.Reg ↪ Fin r)
    (pub : RoutePrepare.Field → Fin k) (done : Fin p) (i : Fin 7) :
    (instruction (w := 1) pc boot leaf pub done i).resize w = instruction pc boot leaf pub done i := by
  fin_cases i <;> rfl

/-- Registers overwritten during the successful route handoff. -/
def Written (boot : LeafBoot.Reg ↪ Fin r) (j : Fin r) : Prop :=
  j = LeafBoot.sources boot .address ∨ j = LeafBoot.sources boot .header ∨ j = LeafBoot.cacheBase boot ∨
    j = LeafBoot.tmp boot ∨ j = LeafBoot.nodeBase boot

theorem run (M : Machine w p r k) (pc : Fin 7 → Fin p) (boot : LeafBoot.Reg ↪ Fin r)
    (leaf : LeafAddress.Reg ↪ Fin r) (pub : RoutePrepare.Field → Fin k) (done : Fin p)
    (link : ∀ i, M.code (pc i) = instruction pc boot leaf pub done i)
    (headSep : leaf .header ≠ LeafBoot.sources boot .address) (nodeSep : ¬ Written boot (leaf .node))
    (R : LeafArena.Regions) (node : ℕ) (site head : Word w) (c : Config w p r) (entry : c.pc = pc 0)
    (hv : c.reg (leaf .site) = site) (hh : c.reg (leaf .header) = head) (hn : c.reg (leaf .node) = (node : Word w))
    (hb : M.publicData (pub .cache) = (R.cacheBase : Word w))
    (hs : M.publicData (pub .stride) = (R.arguments.stride : Word w))
    (ha : M.publicData (pub .start) = (R.arguments.start : Word w)) :
    ∃ out, Prefix M c (List.replicate 7 .tick) out ∧ out.pc = done ∧
      out.reg (LeafBoot.sources boot .address) = site ∧ out.reg (LeafBoot.sources boot .header) = head ∧
      out.reg (LeafBoot.cacheBase boot) = (R.cacheBase : Word w) ∧
      out.reg (LeafBoot.nodeBase boot) = (R.arguments.base node : Word w) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      ∀ j, ¬ Written boot j → out.reg j = c.reg j := by
  let a := c.put (pc 1) (LeafBoot.sources boot .address) site
  let b := a.put (pc 2) (LeafBoot.sources boot .header) head
  let f := b.put (pc 3) (LeafBoot.cacheBase boot) (R.cacheBase : Word w)
  let g := f.put (pc 4) (LeafBoot.tmp boot) (R.arguments.stride : Word w)
  let n := g.put (pc 5) (LeafBoot.nodeBase boot) ((node*R.arguments.stride : ℕ) : Word w)
  let u := n.put (pc 6) (LeafBoot.tmp boot) (R.arguments.start : Word w)
  let out := u.put done (LeafBoot.nodeBase boot) ((R.arguments.base node : ℕ) : Word w)
  have step (i : Fin 7) (s : Config w p r) (hpc : s.pc = pc i) :
      M.program.step s = (instruction pc boot leaf pub done i).run M.publicData s := by
    change (M.code s.pc).run M.publicData s = _
    rw [hpc,link]
  have keep {j : Fin r} (h : ¬Written boot j) : j ≠ LeafBoot.sources boot .address ∧
      j ≠ LeafBoot.sources boot .header ∧ j ≠ LeafBoot.cacheBase boot ∧
      j ≠ LeafBoot.tmp boot ∧ j ≠ LeafBoot.nodeBase boot := by
    simpa only [Written, not_or] using h
  obtain ⟨n₁,n₂,n₃,n₄,_⟩ := keep nodeSep
  have run : Prefix M c (List.replicate 7 .tick) out := by
    refine .tick (next := a) ?_ (.tick (next := b) ?_ (.tick (next := f) ?_ (.tick (next := g) ?_
      (.tick (next := n) ?_ (.tick (next := u) ?_ (.tick ?_ (.nil _)))))))
    · rw [step 0 c entry]; change CallAction.localStep (c.put _ _ _) = _; rw [hv]
    · rw [step 1 a rfl]; change CallAction.localStep (a.put _ _ _) = _
      rw [show a.reg (leaf .header) = head from (Function.update_of_ne headSep ..).trans hh]
    · rw [step 2 b rfl]; change CallAction.localStep (b.put _ _ _) = _; rw [hb]
    · rw [step 3 f rfl]; change CallAction.localStep (f.put _ _ _) = _; rw [hs]
    · rw [step 4 g rfl]
      have word : g.reg (leaf .node) = (node : Word w) := by
        simp only [g,f,b,a,Config.put,Function.update_of_ne n₁,Function.update_of_ne n₂,
          Function.update_of_ne n₃,Function.update_of_ne n₄,hn]
      change CallAction.localStep (g.put _ _ (g.reg (leaf .node)*g.reg (LeafBoot.tmp boot))) = _
      rw [word,show g.reg (LeafBoot.tmp boot) = _ from Function.update_self .., ← Nat.cast_mul]
    · rw [step 5 n rfl]; change CallAction.localStep (n.put _ _ _) = _; rw [ha]
    · rw [step 6 u rfl]
      change CallAction.localStep (u.put _ _ (u.reg (LeafBoot.tmp boot)+u.reg (LeafBoot.nodeBase boot))) = _
      simp [u,n,out,Config.put,LeafBoot.tmp,LeafBoot.nodeBase,Arena.base]
  refine ⟨out,run,rfl,?_,?_,?_,Function.update_self ..,rfl,rfl,?_⟩
  · simp [out,u,n,g,f,b,a,Config.put,LeafBoot.tmp,LeafBoot.nodeBase,LeafBoot.cacheBase]
  · simp [out,u,n,g,f,b,Config.put,LeafBoot.tmp,LeafBoot.nodeBase,LeafBoot.cacheBase]
  · simp [out,u,n,g,f,Config.put,LeafBoot.tmp,LeafBoot.nodeBase,LeafBoot.cacheBase]
  · intro j h
    obtain ⟨j₁,j₂,j₃,j₄,j₅⟩ := keep h
    simp only [out,u,n,g,f,b,a,Config.put,Function.update_of_ne j₁,Function.update_of_ne j₂,
      Function.update_of_ne j₃,Function.update_of_ne j₄,Function.update_of_ne j₅]

end PairSimulation.LeafBootHandoff

end VPVNP
end Computability
end OAI
