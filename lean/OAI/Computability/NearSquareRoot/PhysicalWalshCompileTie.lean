import OAI.Computability.NearSquareRoot.PhysicalWalshRecursion
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax
import OAI.Computability.NearSquareRoot.ScheduleRegisterWitness
import OAI.Computability.IntegerMultiplication.Interface

/-! # Effective closure of the physical Walsh recursion

The physical program reads the tag in the query before running the base case
or the open successor. The emitted files contain the enclosing tie in every
recursive site's lexical scope.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space CommonRegisters GeneratorSyntax PhysicalWalsh

variable {J : Type} [Primcodable J]

private theorem effective_splitRoot (z : ℕ) (f : J → Bool → Cmd) (p : J → Cmd)
    (hf : ∀ b, Effective ltr (fun j => f j b)) (hp : Effective ltr p) :
    Effective ltr (fun j => splitRoot z (f j) (p j)) := by
  unfold splitRoot
  apply effective_look ltr (Computable.const z)
  intro a
  apply (effective_const ltr (.pop z)).join
  rcases a with _|(_|_|_)
  · exact effective_const _ _
  · exact hf _
  · exact hp
  · exact effective_const _ _

/-- Both branches use the same data-register assignment at all recursion levels. -/
theorem tied_within {N : ℕ} (hN : 0 < N) {base step : Cmd} (hb : Within N base) (hs : Within N step) :
    Within N (.tie (decodeBit base step)) := by
  change Within N (splitRoot 0 _ _)
  exact RegisterWitness.splitRoot_within.mpr ⟨hN,trivial,trivial,
    RegisterWitness.splitRoot_within.mpr ⟨hN,hb,hs,trivial⟩⟩

/-- The emitted file is the actual tie of the varying checked commands. -/
theorem effective_tied {base step : J → Cmd} (hb : Effective ltr base) (hs : Effective ltr step) :
    Effective ltr (fun j => .tie (decodeBit (base j) (step j))) := by
  apply Effective.tie
  apply effective_splitRoot 0 (fun _ _ => .pass) _ (fun _ => effective_const _ _)
  apply effective_splitRoot 0 (fun j b => bif b then step j else base j) (fun _ => .pass)
  · intro b
    cases b
    · exact hb
    · exact hs
  · exact effective_const _ _

/-- Closing the named base and successor delivers a single effective family
of complete recursive commands. On every parameter the same command on every
input meets any solution of its recurrence. -/
theorem tie_family {X U : J → Type} (d : (j : J) → RecSpec (X j) (U j)) (calls : J → ℕ) (base step : J → Cmd)
    (eb : Effective ltr base) (es : Effective ltr step) {N : ℕ} (hN : 0 < N)
    (rb : ∀ j, Within N (base j)) (rs : ∀ j, Within N (step j))
    (one : ∀ j, ClosedRuns (base j) (fun x : (d j).Base => (d j).scan ((d j).world x.val))
      (fun x => (d j).arena ((d j).world x.val)) (fun x => (d j).payload x.val) (fun x => (d j).reply x.val))
    (next : ∀ j, Runs (step j) (d j).meter (calls j) (fun x : (d j).Step => (d j).world x.val)
      (fun x => (d j).payload x.val) (fun x => (d j).reply x.val)) :
    let c j := Prog.tie (decodeBit (base j) (step j))
    Effective ltr c ∧ (∀ j, Within N (c j)) ∧
      ∀ j, ∃ C, ∀ T S : U j → ℕ, (d j).Recurrence (calls j) C T S →
      ∀ x env p b, DeckCap b p → BoundedFits env (c j) (pile 0 ((d j).query x) p)
        (pile 0 ((d j).reply x) p) (T ((d j).world x)) (b+S ((d j).world x)) (S ((d j).world x)) :=
  ⟨effective_tied eb es,fun j => tied_within hN (rb j) (rs j),fun j => (d j).tieNamed _ _ (one j) (next j)⟩

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
