import OAI.Computability.NearSquareRoot.InterchangeROMEffective
import OAI.Computability.NearSquareRoot.InterchangeROMProgram

/-! # Quoting complete physical interchange stage programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROM

open IntegerMultiplication IntegerMultiplication.Code GeneratorSyntax

variable {X T M : Type} [Primcodable X] [Primcodable T] [Primcodable M]

private theorem precomp {Y Z : Type} [Primcodable Y] [Primcodable Z] (c : Y → Cmd) (f : Z → Y)
    (hc : Effective ltr c) (hf : Computable f) : Effective ltr (fun x => c (f x)) :=
  Computable.comp (f:=fun y => file ltr (c y)) (g:=f) hc hf

set_option maxHeartbeats 350000 in
theorem effective_instruction {table : X → T → Cmd} {moveRow : X → M → Cmd}
    (ht : Effective ltr (fun z : X × T => table z.1 z.2))
    (hm : Effective ltr (fun z : X × M => moveRow z.1 z.2)) :
    Effective ltr (fun z : X × Instruction T M => instruction (table z.1) (moveRow z.1) z.2) := by
  let A := X × Instruction T M
  have atTable : Effective ltr (fun z : A × T => underHeader (table z.1.1 z.2)) :=
    effective_underHeader (precomp (fun u : X × T => table u.1 u.2) (fun z : A × T => (z.1.1,z.2)) ht
      ((Computable.fst.comp Computable.fst).pair Computable.snd))
  have atMove : Effective ltr (fun z : (A × List (ℕ × M)) × M => moveRow z.1.1.1 z.2) :=
    precomp (fun u : X × M => moveRow u.1 u.2) (fun z : (A × List (ℕ × M)) × M => (z.1.1.1,z.2)) hm
      ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)
  have atRoute : Effective ltr (fun z : A × List (ℕ × M) => routeCommand (moveRow z.1.1) z.2) :=
    effective_route (entries:=fun z : A × List (ℕ × M) => z.2) (op:=fun z m => moveRow z.1.1 m)
      Computable.snd atMove
  have choice := Computable.sumCasesOn
    (g:=fun z : A => fun t : T => file ltr (underHeader (table z.1 t)))
    (h:=fun z : A => fun legs : List (ℕ × M) => file ltr (routeCommand (moveRow z.1) legs))
    (Computable.snd (α:=X) (β:=Instruction T M))
    atTable.to₂ atRoute.to₂
  unfold Effective
  apply choice.of_eq
  rintro ⟨x,_|_⟩ <;> rfl

/-- A total numeric template generator gives the full P192 command file. -/
theorem effective_program {table : X → T → Cmd} {moveRow : X → M → Cmd}
    (ht : Effective ltr (fun z : X × T => table z.1 z.2))
    (hm : Effective ltr (fun z : X × M => moveRow z.1 z.2))
    {stages : X → List (Instruction T M)} (hs : Computable stages) :
    Effective ltr (fun x => program (table x) (moveRow x) (stages x)) :=
  effective_foldr_join ltr (l:=stages) (p:=fun x a => instruction (table x) (moveRow x) a)
    (z:=fun _ => .pass) hs (effective_instruction ht hm) (effective_const ltr .pass)

end InterchangeROM

end NearSquareRoot
end Computability
end OAI
