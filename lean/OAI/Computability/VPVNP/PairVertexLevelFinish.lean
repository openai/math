import OAI.Computability.VPVNP.PairVertexLevelScan

/-!
# Recovering the selected site's packed ordinal and old header
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevel

open BurstRAM BurstRAM.PrivateRAM TraversalControllerInputs NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r : ℕ}

/-- A completed level lookup identifies the successor layer, its row start and owner ordinal,
and the headers required by the role handler. -/
structure Located (pub : Fin 11 → Word w) (m : Memory w) (reg : Fin 14 ↪ Fin r)
    (node : Word w) (oldLevel : ℕ) (owner : Word w) (c : Config w p r) : Prop where
  state : ScanState pub m reg node (oldLevel + 1) c
  start : c.reg (reg 5) = levelField pub m (oldLevel + 1) 14
  owner : c.reg (reg 7) = owner
  oldHead : c.reg (reg 11) = levelHead pub m oldLevel
  oldFields : c.reg (reg 12) = levelHead pub m oldLevel + 14
  stage : c.reg (reg 13) = (oldLevel : Word w)

/-- After the bracketing comparison, five native arithmetic instructions compute
the old header, its child directory, and the popped row's packed site ordinal. -/
theorem finish_run {M : Machine w p r 11} {pc : Fin 5 → Fin p} {reg : Fin 14 ↪ Fin r}
    {done : Fin p} {m : Memory w} {node owner : Word w} {j : ℕ}
    (link : ∀ i, M.code (pc i) = finish pc reg done i)
    (c : Config w p r) (hc : c.pc = pc 0) (st : ScanState M.publicData m reg node (j + 1) c)
    (base : c.reg (reg 5) = levelField M.publicData m (j + 1) 14)
    (quot : BinaryOp.div.eval (node - levelField M.publicData m (j + 1) 14)
      (terminalField M.publicData m 15) = owner) :
    ∃ out, Prefix M m c out [] (List.replicate 5 .tick) ∧ out.pc = done ∧
      Located M.publicData m reg node j owner out ∧ Frame reg c out := by
  let a := c.put (pc 1) (reg 13) (j : Word w)
  let b := a.put (pc 2) (reg 11) (levelHead M.publicData m j)
  let d := b.put (pc 3) (reg 12) (levelHead M.publicData m j + 14)
  let e := d.put (pc 4) (reg 9) (node - levelField M.publicData m (j + 1) 14)
  let out := e.put done (reg 7) owner
  have atRow (i : Fin 5) (q : Config w p r) (hp : q.pc = pc i) :
      M.program.step q = (finish pc reg done i).run M.publicData q := by
    simp only [Machine.program, hp, link]
  have s₀ : M.program.step c = .localStep a := by
    rw [atRow 0 c hc]
    change CallAction.localStep (c.put _ _ (c.reg (reg 3) - c.reg (reg 8))) = _
    simp [a, st.index, st.one]
  have s₁ : M.program.step a = .localStep b := by
    rw [atRow 1 a rfl]
    change CallAction.localStep (a.put _ _ (a.reg (reg 4) - a.reg (reg 2))) = _
    simp [a, b, Config.put, st.current, st.pitch, levelHead, add_mul, ← add_assoc]
  have s₂ : M.program.step b = .localStep d := by
    rw [atRow 2 b rfl]
    change CallAction.localStep (b.put _ _ (b.reg (reg 11) + b.reg (reg 10))) = _
    simp [a, b, d, Config.put, st.offset]
  have s₃ : M.program.step d = .localStep e := by
    rw [atRow 3 d rfl]
    change CallAction.localStep (d.put _ _ (d.reg (reg 0) - d.reg (reg 5))) = _
    simp [a, b, d, e, Config.put, st.node, base]
  have s₄ : M.program.step e = .localStep out := by
    rw [atRow 4 e rfl]
    change CallAction.localStep (e.put _ _ (BinaryOp.div.eval (e.reg (reg 9)) (e.reg (reg 6)))) = _
    simp [a, b, d, e, out, Config.put, st.stride, quot]
  have pre : ReadPrefix M m c (List.replicate 5 .tick) out :=
    ReadPrefix.tick s₀ (ReadPrefix.tick s₁ (ReadPrefix.tick s₂ (ReadPrefix.tick s₃
      (ReadPrefix.tick s₄ (ReadPrefix.nil _)))))
  refine ⟨out, ReadPrefix.execute pre, rfl, ?_, ⟨?_, rfl, rfl⟩⟩
  · constructor
    · constructor <;> simp [out, e, d, b, a, Config.put, st.node, st.header, st.pitch,
        st.index, st.current, st.stride, st.one, st.offset]
    all_goals simp [out, e, d, b, a, Config.put, base]
  · intro i hi
    have h (j : Fin 14) : i ≠ reg j := fun e => hi ⟨j, e.symm⟩
    simp [out, e, d, b, a, Config.put, Function.update_of_ne (h _)]

end PairSimulation.VertexLevel

end VPVNP
end Computability
end OAI
