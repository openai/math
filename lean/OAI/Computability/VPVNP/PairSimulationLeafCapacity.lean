import OAI.Computability.VPVNP.PairSimulationLeafScalarStartup

/-! # Native computation of the verifier's private port capacity -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafCapacity

open BurstRAM PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- Read n, square to its eighth power, retain that factor, then square to its
thirty-second power and multiply. The stride can immediately be used by the
pointer allocation table. -/
def instruction (pc : Fin 8 → Fin p) (dst tmp : Fin r) (nPub : Fin k) (done : Fin p) : Fin 8 → Instr w p r k :=
  ![.publicWord dst nPub (pc 1), .binary .mul dst dst dst (pc 2), .binary .mul dst dst dst (pc 3),
    .binary .mul dst dst dst (pc 4), .copy tmp dst (pc 5), .binary .mul dst dst dst (pc 6),
    .binary .mul dst dst dst (pc 7), .binary .mul dst dst tmp done]

theorem resize_instruction (pc : Fin 8 → Fin p) (dst tmp : Fin r) (nPub : Fin k) (done : Fin p)
    (i : Fin 8) : (instruction (w := 1) pc dst tmp nPub done i).resize w = instruction pc dst tmp nPub done i := by
  fin_cases i <;> rfl

theorem run (M : Machine w p r k) (pc : Fin 8 → Fin p) (dst tmp : Fin r) (sep : dst ≠ tmp) (nPub : Fin k)
    (done : Fin p) (link : ∀ i, M.code (pc i) = instruction pc dst tmp nPub done i)
    (c : Config w p r) (hc : c.pc = pc 0) (n : ℕ) (hpub : M.publicData nPub = (n : Word w)) :
    ∃ out, Prefix M c (List.replicate 8 .tick) out ∧ out.pc = done ∧ out.reg dst = ((n^40 : ℕ) : Word w) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      ∀ i, i ≠ dst → i ≠ tmp → out.reg i = c.reg i := by
  let a := (n : Word w)
  let s₁ := c.put (pc 1) dst a
  let s₂ := s₁.put (pc 2) dst (a^2)
  let s₃ := s₂.put (pc 3) dst (a^4)
  let s₄ := s₃.put (pc 4) dst (a^8)
  let s₅ := s₄.put (pc 5) tmp (a^8)
  let s₆ := s₅.put (pc 6) dst (a^16)
  let s₇ := s₆.put (pc 7) dst (a^32)
  let out := s₇.put done dst (a^40)
  have step (i : Fin 8) (s : Config w p r) (hs : s.pc = pc i) :
      M.program.step s = (instruction pc dst tmp nPub done i).run M.publicData s := by
    change (M.code s.pc).run _ _ = _; rw [hs,link]
  refine ⟨out, .tick (next := s₁) ?_ (.tick (next := s₂) ?_ (.tick (next := s₃) ?_ (.tick (next := s₄) ?_ (.tick (next := s₅) ?_ (.tick (next := s₆) ?_ (.tick (next := s₇) ?_ (.tick (next := out) ?_ (.nil _)))))))), rfl,
    by simp [out,a,Config.put],rfl,rfl,?_⟩
  · rw [step 0 c hc]; simp [instruction,Instr.run,s₁,hpub,a]
  · rw [step 1 s₁ rfl]; simp [instruction,Instr.run,s₁,s₂,Config.put,BinaryOp.eval,pow_two]
  · rw [step 2 s₂ rfl]; simp [instruction,Instr.run,s₂,s₃,Config.put,BinaryOp.eval,← pow_add]
  · rw [step 3 s₃ rfl]; simp [instruction,Instr.run,s₃,s₄,Config.put,BinaryOp.eval,← pow_add]
  · rw [step 4 s₄ rfl]; simp [instruction,Instr.run,s₄,s₅,Config.put]
  · rw [step 5 s₅ rfl]; simp [instruction,Instr.run,s₄,s₅,s₆,Config.put,BinaryOp.eval,sep,← pow_add]
  · rw [step 6 s₆ rfl]; simp [instruction,Instr.run,s₆,s₇,Config.put,BinaryOp.eval,← pow_add]
  · rw [step 7 s₇ rfl]; simp [instruction,Instr.run,s₅,s₆,s₇,out,Config.put,BinaryOp.eval,sep.symm,← pow_add]
  · intro i hd ht; simp [out,s₇,s₆,s₅,s₄,s₃,s₂,s₁,Config.put,Function.update_of_ne hd,Function.update_of_ne ht]

end PairSimulation.LeafCapacity

end VPVNP
end Computability
end OAI
