import OAI.Computability.BorderVNP.CellBitFeasible
import OAI.Computability.BorderVNP.CellExpressionCall
import OAI.Computability.BorderVNP.CellLeafRead

/-! # Evaluating a parameter bit during private bytecode generation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open RationalHitting RationalHitting.StackLanguage CellSparse

private abbrev BitInput (d : ℕ) := (Address.Layout d × Address.Layout d) × List ℕ

private def literalWord (d : ℕ) (s : BitInput d) : BitWord :=
  ⟨(Op.literal ((Address.eval d (s.1.1,s.2)).testBit (Address.eval d (s.1.2,s.2)))).bits⟩

private theorem literalWord_poly (d : ℕ) : Poly (literalWord d) := by
  have hv : Poly (fun s : BitInput d => Address.eval d (s.1.1,s.2)) :=
    (Address.feasible d).comp (show Poly (fun s : BitInput d => (s.1.1,s.2)) by fun_prop)
  have hi : Poly (fun s : BitInput d => Address.eval d (s.1.2,s.2)) :=
    (Address.feasible d).comp (show Poly (fun s : BitInput d => (s.1.2,s.2)) by fun_prop)
  apply (Poly.cond (testBit_poly.comp (hv.pair hi))
    (StackLanguage.Poly.const (BitWord.mk (Op.literal true).bits)) (StackLanguage.Poly.const (BitWord.mk (Op.literal false).bits))).of_eq
  intro s
  dsimp [literalWord]
  cases (Address.eval d (s.1.1,s.2)).testBit (Address.eval d (s.1.2,s.2)) <;> rfl

private noncomputable def bitProcedure (d : ℕ) :
    Procedure (pairCode Coding.code Coding.code) BitWord.val (literalWord d) :=
  (literalWord_poly d).some

/-- Evaluate both expressions, select the requested binary digit, and emit its literal instruction. -/
noncomputable def bitLeaf (d : ℕ) : Fragment IO :=
  (pairCall (bitProcedure d)).seq fixedLeaf

/-- A polynomial in the combined binary syntax and lexical environment bounds the entire
instruction emission, regardless of the magnitude of its evaluated bit index. -/
noncomputable def bitClock (d : ℕ) : TimeBound := pairClock (bitProcedure d) + 10

/-- The selected bit is written to the output as reversed bytecode. Both expressions see
the same lexical indices and the caller's earlier output is preserved as a suffix. -/
theorem bitLeaf_run (d : ℕ) (v i : NatExpr) (env : List ℕ) (out : List Bool)
    (hv : Address.depth v ≤ d) (hi : Address.depth i ≤ d) :
    ∃ t ≤ (bitClock d).eval ((Coding.code ((Address.pack d v,Address.pack d i),env)).length+1),
      (bitLeaf d).Runs t (io (Coding.code (Address.pack d v,Address.pack d i)) (Coding.code env) out)
        (io [] (Coding.code env) ((Op.literal ((v.eval env).testBit (i.eval env))).bits.reverse ++ out)) := by
  obtain ⟨t,ht,hr⟩ := pairCall_run (bitProcedure d) (Address.pack d v,Address.pack d i) env out
  dsimp only [literalWord] at hr
  rw [Address.eval_pack v env hv, Address.eval_pack i env hi] at hr
  obtain ⟨u,hu,hs⟩ := fixedLeaf_run (Op.literal ((v.eval env).testBit (i.eval env))).bits (Coding.code env) out
  refine ⟨t+u, ?_, Fragment.runs_seq _ _ hr hs⟩
  simp only [bitClock, TimeBound.eval_add, TimeBound.eval_numeral]
  change u ≤ 4*2+2 at hu
  exact Nat.add_le_add ht hu

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
