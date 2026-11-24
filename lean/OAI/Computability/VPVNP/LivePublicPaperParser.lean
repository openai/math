import OAI.Computability.VPVNP.LivePublicParser

/-! # The paper's full-degree parser with its prescribed state count

The grammar family uses state zero as its root and allocates `n^(C+5)`
states. Both public operands are independent of the coefficients later
installed in the grammar.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram

theorem PublicExpr.fits_natPow {g : Geometry} {e : PublicExpr} {b : ℕ}
    (hf : e.Fits g b) (hp : 0 < e.eval g) (k : ℕ) (hk : (e.eval g)^k < b) :
    (e.natPow k).Fits g b := by
  induction k with
  | zero => exact ⟨by simpa using hk,trivial⟩
  | succ k ih =>
    exact ⟨by simpa only [PublicExpr.eval_natPow] using hk,
      ih ((Nat.pow_le_pow_right hp (Nat.le_succ k)).trans_lt hk),hf⟩

namespace ParserPublic

open PrimedInputRAM PrimedCounter

/-- Build the full-degree parser inputs with root state zero and grammar state count n^(C+5),
where n is the assembler input length. -/
def paperInputs (assembler : Fin 16 → PublicExpr) (C : ℕ) : Inputs :=
  ⟨assembler,(assembler 1).natPow (C+5),.lit 0⟩

variable {L : PrimedInputRAM.Lengths} {n r H w C : ℕ} {Q : Layout L n r H w}
  (D : PrimedCounter.Data Q (n^(C+5))) (g : Geometry) (assembler : Fin 16 → PublicExpr)

theorem paper_values (ha : ∀ i, (assembler i).eval g = Opcodes.pubNat Q i)
    (hroot : D.root.val = 0) : (paperInputs assembler C).Values g D := by
  refine ⟨ha,?_,hroot.symm⟩
  change ((assembler 1).natPow (C+5)).eval g = _
  rw [PublicExpr.eval_natPow, ha]
  rfl

theorem paper_table (ha : ∀ i, (assembler i).eval g = Opcodes.pubNat Q i)
    (hf : D.Fits) (hroot : D.root.val = 0) (hasm : ∀ i, (assembler i).Fits g (2^w)) (j : Fin 34) :
    Fin.ofNat (2^w) (((paperInputs assembler C).table j).eval g) = D.pub j ∧
      ((paperInputs assembler C).table j).Fits g (2^w) := by
  have hv := paper_values D g assembler ha hroot
  have hn : 0 < n := (Nat.zero_le _).trans_lt D.degree.isLt
  have hnum : (assembler 1).eval g = n := ha 1
  refine ⟨Inputs.table_eval _ _ D hv hf.degree_eq j, Inputs.table_fits _ _ D hv hf hasm ?_ ?_ j⟩
  · exact PublicExpr.fits_natPow (hasm 1) (hnum ▸ hn) _ (hnum ▸ hf.states)
  · exact ⟨Nat.two_pow_pos _,trivial⟩

end ParserPublic
end LiveProgram

end VPVNP
end Computability
end OAI
