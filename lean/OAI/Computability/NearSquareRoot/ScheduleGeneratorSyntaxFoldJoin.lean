import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFold

/-! # Effective concatenation of P192 programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax
open IntegerMultiplication
variable {X B : Type} [Primcodable X] [Primcodable B]

variable {A : Type} [Fintype A] (letter : A ↪ ℕ)

set_option maxHeartbeats 800000 in
/-- Concatenation of a computably generated list of physical program fragments. -/
theorem effective_foldr_join {l : X → List B} {p : X → B → Prog A} {z : X → Prog A}
    (hl : Computable l) (hp : Effective letter (fun v : X × B => p v.1 v.2))
    (hz : Effective letter z) :
    Effective letter (fun x => (l x).foldr (fun b s => (p x b).join s) (z x)) := by
  change Computable (fun v : X × B => file letter (p v.1 v.2)) at hp
  change Computable (fun x => file letter (z x)) at hz
  have step : Computable₂ (fun (x : X) (v : B × File) => joinFile (file letter (p x v.1)) v.2) :=
    primrec_joinFile.to_comp.comp
      (hp.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)
  have run := computable_foldr (l := l) (z := fun x => file letter (z x))
    (f := fun x (v : B × File) => joinFile (file letter (p x v.1)) v.2) hl hz step
  unfold Effective
  apply run.of_eq
  intro x
  change (l x).foldr (fun b s => joinFile (file letter (p x b)) s) (file letter (z x)) =
    file letter ((l x).foldr (fun b s => (p x b).join s) (z x))
  induction l x with
  | nil => rfl
  | cons a rest ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, joinFile_file]

end GeneratorSyntax

end NearSquareRoot
end Computability
end OAI
