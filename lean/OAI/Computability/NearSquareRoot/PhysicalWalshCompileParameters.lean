import OAI.Computability.NearSquareRoot.PhysicalWalshCompileEffective

/-! # Adding and specializing a fixed parameter in generated command files -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open GeneratorSyntax IntegerMultiplication Code

theorem ignoreParameter {Z X Y : Type} [Primcodable Z] [Primcodable X] [Primcodable Y]
    {f : X → Y → Cmd} (hf : Effective ltr (Function.uncurry f)) :
    Effective ltr (Function.uncurry (fun (k : Z × X) y => f k.2 y)) := by
  let forget (k : (Z × X) × Y) := (k.1.2,k.2)
  have h : Computable forget := (Computable.snd.comp Computable.fst).pair Computable.snd
  have step := Computable.comp (f := fun e : X × Y => file ltr (Function.uncurry f e)) hf h
  apply step.of_eq
  rintro ⟨⟨z,x⟩,y⟩
  rfl

theorem fixParameter {Z X Y : Type} [Primcodable Z] [Primcodable X] [Primcodable Y]
    {f : Z × X → Y → Cmd} (hf : Effective ltr (Function.uncurry f)) (z : Z) :
    Effective ltr (Function.uncurry (fun x y => f (z,x) y)) := by
  let put (k : X × Y) := ((z,k.1),k.2)
  have h : Computable put := ((Computable.const z).pair Computable.fst).pair Computable.snd
  have step := Computable.comp (f := fun e : (Z × X) × Y => file ltr (Function.uncurry f e)) hf h
  apply step.of_eq
  rintro ⟨x,y⟩
  rfl

theorem fixCommandParameter {Z X : Type} [Primcodable Z] [Primcodable X]
    {f : Z × X → Cmd} (hf : Effective ltr f) (z : Z) :
    Effective ltr (fun x => f (z,x)) :=
  Computable.comp (f := fun e : Z × X => file ltr (f e)) hf ((Computable.const z).pair Computable.id)

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
