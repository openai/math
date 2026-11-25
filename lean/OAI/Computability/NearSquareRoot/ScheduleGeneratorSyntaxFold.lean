import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax

/-! # Effective list folds for parameterized P192 program generation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax
open IntegerMultiplication

variable {X B S : Type} [Primcodable X] [Primcodable B] [Primcodable S]

/-- Right-fold a computably generated sequence, allowing the accumulator update
to depend on the family parameter and to perform an arbitrary total computation. -/
theorem computable_foldr {l : X → List B} {z : X → S} {f : X → B × S → S}
    (hl : Computable l) (hz : Computable z) (hf : Computable₂ f) :
    Computable fun x => (l x).foldr (fun b s => f x (b,s)) (z x) := by
  let step (x : X) (ns : ℕ × S) : S :=
    Option.casesOn ((l x)[(l x).length - (ns.1+1)]?) ns.2 (fun b => f x (b,ns.2))
  have len := Computable.list_length.comp hl
  have hs : Computable₂ step := by
    let j : X × ℕ × S → ℕ := fun v => (l v.1).length - (v.2.1+1)
    have hj : Computable j := Primrec.nat_sub.to_comp.comp (len.comp Computable.fst)
      (Computable.succ.comp (Computable.fst.comp Computable.snd))
    apply Computable.option_casesOn (Computable.list_getElem?.comp (hl.comp Computable.fst) hj)
      (Computable.snd.comp Computable.snd)
    exact hf.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.pair (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have run := Computable.nat_rec len hz hs
  apply run.of_eq
  intro x
  have partialRun (n : ℕ) (h : n ≤ (l x).length) :
      Nat.rec (z x) (fun j acc => step x (j,acc)) n =
        ((l x).drop ((l x).length-n)).foldr (fun b s => f x (b,s)) (z x) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hj : (l x).length - (n+1) < (l x).length := by omega
      have eq : (l x).length - (n+1) + 1 = (l x).length - n := by omega
      rw [List.drop_eq_getElem_cons hj, eq]
      simp [step, List.getElem?_eq_getElem hj, ih (by omega)]
  simpa only [Nat.sub_self, List.drop_zero] using partialRun (l x).length le_rfl

theorem computable_map {l : X → List B} {f : X → B → S}
    (hl : Computable l) (hf : Computable₂ f) :
    Computable fun x => (l x).map (f x) := by
  have step : Computable₂ (fun x (v : B × List S) => f x v.1 :: v.2) :=
    Computable.list_cons.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (computable_foldr (z := fun _ => []) hl (Computable.const []) step).of_eq
  intro x
  induction l x <;> simp_all

end GeneratorSyntax

end NearSquareRoot
end Computability
end OAI
