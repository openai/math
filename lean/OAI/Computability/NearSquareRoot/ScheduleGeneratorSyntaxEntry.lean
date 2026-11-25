import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackInput

/-! # Effective initial addresses of the closed-program compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet Generator.SyntaxAddress

variable {A : Type} [Fintype A] (a : Numbering A)

/-- A closed program enters at its root with no enclosing ties. -/
noncomputable def start (p : Prog A) : Prog.Pc (Prog.sites [] p) :=
  some ⟨([],p), Prog.sites_self p []⟩

/-- Register zero is present even when no instruction names it. -/
def zeroStack (U : List (Prog.Loc A)) : Prog.Ix U :=
  some ⟨0, by simp [Prog.used]⟩

theorem start_val (p : Prog A) :
    ((pcs a (Prog.sites [] p)).equiv (start p)).val =
      rank (file (letter a) p).2 ([], key (letter a) p) + 1 := by
  exact Generator.StackRows.option_some _ _

omit [Fintype A] in
theorem zeroStack_val (U : List (Prog.Loc A)) :
    ((Pack.stacks U).equiv (zeroStack U)).val = rank (Prog.used U) 0 + 1 := by
  rw [zeroStack, Pack.stacks, Generator.StackRows.option_some, idx_rank]

variable {X : Type} [Primcodable X] {p : X → Prog A}

theorem computable_start (hp : Effective (letter a) p) :
    Computable fun x => ((pcs a (Prog.sites [] (p x))).equiv (start (p x))).val := by
  simp only [start_val]
  exact Computable.succ.comp (primrec_rank.to_comp.comp (Computable.snd.comp hp)
    ((Computable.const []).pair hp.key))

theorem computable_zeroStack (hp : Effective (letter a) p) :
    Computable fun x => ((Pack.stacks (Prog.sites [] (p x))).equiv (zeroStack _)).val := by
  simp only [zeroStack_val]
  exact Computable.succ.comp (primrec_rank.to_comp.comp hp.used (Computable.const 0))

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
