import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveCell
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFoldJoin

/-! # Effective bank routing -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROM
open IntegerMultiplication IntegerMultiplication.Code LoomRegisters GeneratorSyntax

variable {X M K : Type} [Primcodable X] [Primcodable M] [Primcodable K]

open private build from OAI.Computability.NearSquareRoot.ScheduleRegisterLoomSeries

omit [Primcodable K] in
private theorem build_fold (p : K → Cmd) (l : List K) :
    build p l = l.foldr (fun a rest => ((clone 1 0 2).join ((p a).join (pack 0))).join rest) .pass := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [build,List.foldr_cons,ih]

theorem effective_series {p : X → K → Cmd} {l : X → List K}
    (hp : Effective ltr (fun v : X × K => p v.1 v.2)) (hl : Computable l) :
    Effective ltr (fun x => seriesCommand (p x) (l x)) := by
  let field := fun x k => (clone 1 0 2).join ((p x k).join (pack 0))
  have gen := effective_foldr_join ltr (l:=fun x => (l x).reverse) (p:=field)
    (z:=fun _ => .pass) (Primrec.list_reverse.to_comp.comp hl)
    ((effective_const ltr (clone 1 0 2)).join (hp.join (effective_const ltr (pack 0))))
    (effective_const ltr .pass)
  have b : Effective ltr (fun x => build (p x) (l x).reverse) :=
    gen.of_eq (fun x => congrArg (file ltr) (build_fold _ _).symm)
  exact (effective_const ltr (move 0 1 2)).join
    ((effective_const ltr (give 0 false)).join (b.join (effective_const ltr (discard 1))))

end InterchangeROM

end NearSquareRoot
end Computability
end OAI
