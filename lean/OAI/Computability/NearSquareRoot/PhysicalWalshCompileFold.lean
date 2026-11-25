import OAI.Computability.NearSquareRoot.KernelPassComputableSyntax
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFold

/-! # Effective interpretation of a prefix program with total computable leaves -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open KernelPass.ComputableSyntax

/-- The instruction list, parameter, and emitted program for each raw leaf
may all vary computably. The parse includes the grammar's default cases. -/
theorem computable_parse {X σ : Type} [Primcodable X] [Primcodable σ]
    (a : X → Algebra σ) (z : σ) (hz : ∀ x, (a x).empty = z)
    (h₁ : Computable₂ fun x k => (a x).leaf k)
    (h₂ : Computable₂ fun x (p : σ × σ) => (a x).seq p.1 p.2)
    (h₃ : Computable₂ fun x (p : σ × σ) => (a x).parallel p.1 p.2)
    (ops : X → List Op) (ho : Computable ops) : Computable fun x => (a x).parse (ops x) := by
  let S := X × Op × List σ
  have k : Computable (fun v : S => v.2.1) := Computable.fst.comp Computable.snd
  have s : Computable (fun v : S => v.2.2) := Computable.snd.comp Computable.snd
  have tag := Computable.fst.comp k
  have args := ((Primrec.list_getD z).to_comp.comp s (Computable.const 0)).pair
    ((Primrec.list_getD z).to_comp.comp s (Computable.const 1))
  have drop := Primrec.list_drop.to_comp.comp (Computable.const 2) s
  have seq := Computable.list_cons.comp (h₂.comp Computable.fst args) drop
  have par := Computable.list_cons.comp (h₃.comp Computable.fst args) drop
  have leaf := Computable.list_cons.comp (h₁.comp Computable.fst k) s
  have h4 := Primrec.eq.decide.to_comp.comp tag (Computable.const 4)
  have h5 := Primrec.eq.decide.to_comp.comp tag (Computable.const 5)
  have step : Computable₂ (fun x (p : Op × List σ) => (a x).step p.1 p.2) := by
    simpa only [Algebra.step,hz,Bool.cond_decide] using
      (Computable.cond h4 seq (Computable.cond h5 par leaf)).to₂
  simpa only [Algebra.parse,hz] using (Primrec.list_getD z).to_comp.comp
    (GeneratorSyntax.computable_foldr ho (Computable.const []) step) (Computable.const 0)

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
