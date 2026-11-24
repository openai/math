import OAI.Computability.VPVNP.PrimedInputRAMFlowLinks
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# Advancing the field offsets of one decoded motif copy

Each selected base profile supplies one fixed width for each demand or supply
group. Loading its public width and adding it to the group's offset takes two
private instructions. The finite group list is part of the fixed template.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapOffsets

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {E : Type*} {w p r k : ℕ}

/-- Load each listed group's public width into `tmp` and add it to the group's offset. -/
def code (off : E ↪ Fin r) (delta : E → Fin k) (tmp : Fin r) : List E → Flow r k
  | [] => .line (.guardEq tmp tmp)
  | e :: es =>
    (Flow.line (.publicWord tmp (delta e))).seq
      ((Flow.line (.binary .add (off e) (off e) tmp)).seq (code off delta tmp es))

/-- After one pass over distinct groups, their offset registers contain the
old value plus the selected public width. Registers outside the group list
and the scratch register retain their original values. -/
theorem native [DecidableEq E] (off : E ↪ Fin r) (delta : E → Fin k) (tmp : Fin r)
    (disjoint : ∀ e, off e ≠ tmp) (es : List E) (hd : es.Nodup)
    (M : Machine w p r k) (label : (code off delta tmp es).Label → Fin p)
    (stop bad : Fin p) (link : Flow.Linked M (code off delta tmp es) label stop bad)
    (c : Config w p r) (hc : c.pc = label (code off delta tmp es).entry) :
    ∃ out, Prefix M c (List.replicate (2 * es.length + 1) .tick) out ∧ out.pc = stop ∧
      (∀ e, out.reg (off e) = c.reg (off e) + if e ∈ es then M.publicData (delta e) else 0) ∧
      (∀ j, j ≠ tmp → (∀ e ∈ es, j ≠ off e) → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  induction es generalizing c with
  | nil =>
    have hs : M.program.step c = .localStep {c with pc := stop} := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hc, link.atLabel]
      change CallAction.localStep {c with pc := if c.reg tmp = c.reg tmp then stop else bad} = _
      simp
    exact ⟨_, .tick hs (.nil _), rfl, by simp, fun _ _ _ ↦ rfl, rfl, rfl⟩
  | cons e es ih =>
    let tail := code off delta tmp es
    let addLabel : (code off delta tmp (e :: es)).Label := .inr (.inl ())
    let c₁ := c.put (label addLabel) tmp (M.publicData (delta e))
    let enter := label (.inr (.inr tail.entry))
    let c₂ := c₁.put enter (off e) (c.reg (off e) + M.publicData (delta e))
    have s₀ : M.program.step c = .localStep c₁ := by
      rw [show M.program.step c = (M.code c.pc).run M.publicData c from rfl, hc, link.atLabel]
      rfl
    have s₁ : M.program.step c₁ = .localStep c₂ := by
      rw [show M.program.step c₁ = (M.code (label addLabel)).run M.publicData c₁ from rfl,
        link.atLabel addLabel]
      change CallAction.localStep (c₁.put enter (off e) (c₁.reg (off e) + c₁.reg tmp)) = _
      simp [c₂, c₁, Config.put, Function.update_of_ne (disjoint e)]
    have short : Prefix M c [.tick, .tick] c₂ := .tick s₀ (.tick s₁ (.nil _))
    obtain ⟨out, pre, ho, regs, other, hm, hp⟩ :=
      ih (List.nodup_cons.mp hd).2 ((label ∘ Sum.inr) ∘ Sum.inr) link.seqRight.seqRight c₂ rfl
    refine ⟨out, ?_, ho, ?_, ?_, hm, hp⟩
    · convert short.append pre using 1
      change List.replicate (2 * (e :: es).length + 1) _ =
        List.replicate 2 _ ++ List.replicate (2 * es.length + 1) _
      rw [← List.replicate_add, List.length_cons]
      congr 1
      omega
    · intro x
      rw [regs]
      by_cases h : x = e
      · subst x
        simp [c₂, (List.nodup_cons.mp hd).1]
      · simp [c₂, c₁, Config.put, Function.update_of_ne (disjoint x), h]
    · intro j htmp hgroup
      rw [other j htmp (fun i hi ↦ hgroup i (List.mem_cons_of_mem _ hi))]
      simp [c₂, c₁, Config.put, Function.update_of_ne (hgroup e List.mem_cons_self),
        Function.update_of_ne htmp]

end PairSimulation.MapOffsets

end VPVNP
end Computability
end OAI
