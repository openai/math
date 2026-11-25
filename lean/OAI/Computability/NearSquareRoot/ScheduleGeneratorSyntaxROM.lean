import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFamily
import OAI.Computability.NearSquareRoot.ScheduleGeneratorAlphabet

/-! # A computable literal ROM for a family of P192 programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet

variable {A : Type} [Fintype A] (a : Numbering A) {R : ℕ}

noncomputable def blockCode (p : Prog A) : CommonAlphabet.Code (Data p) :=
  oneHot (dataNum a p).equiv none

/-- Installable program over the common three-symbol tape alphabet and fixed
register bank, including all compiler, output-copy, and serialization phases. -/
noncomputable def rom (hR : 0 < R) (p : Prog A) (bound : CommonRegisters.Within R p) :
    List (Universal.Tag (Option Bool) (Option (Option (Fin R)))) :=
  Numbering.program (dataNum a p) (controlNum a p) (Padding.fixed R) (blockCode a p)
    (paddedRule hR p bound) (entry p)

/-- A computable source syntax family needs only a shared register bound to emit
the exact ROM of its physical machine at each parameter. -/
theorem computable_rom (hR : 0 < R) (p : ℕ → Prog A) (hp : Effective (letter a) p)
    (bound : ∀ j, CommonRegisters.Within R (p j)) {M : ℕ}
    (enum : Universal.Tag (Option Bool) (Option (Option (Fin R))) ≃ Fin (M+1)) :
    Computable fun j => (rom a hR (p j) (bound j)).map (fun t => (enum t).val) := by
  obtain ⟨ha,hq,he,rows,hr,h⟩ := paddedRows a hR p hp bound
  have hb : Computable (fun j => ((dataNum a (p j)).equiv none).val) := by
    simp only [blank_rank]
    exact Computable.const 0
  exact Generator.Phase.computable_program (fun j => dataNum a (p j)) (fun j => controlNum a (p j))
    (Padding.fixed R) ha hq (fun _ => none) hb rows hr (fun j => paddedRule hR (p j) (bound j))
    h (fun j => entry (p j)) he enum

theorem computable_ltr_rom [Fintype Code.Ltr] (hR : 0 < R) (p : ℕ → Code.Cmd)
    (hp : Effective ltr p) (bound : ∀ j, CommonRegisters.Within R (p j)) {M : ℕ}
    (enum : Universal.Tag (Option Bool) (Option (Option (Fin R))) ≃ Fin (M+1)) :
    Computable fun j => (rom ltrNumbering hR (p j) (bound j)).map (fun t => (enum t).val) :=
  computable_rom ltrNumbering hR p hp bound enum

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
