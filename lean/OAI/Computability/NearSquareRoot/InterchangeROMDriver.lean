import OAI.Computability.NearSquareRoot.InterchangeROMFrame
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBank
import OAI.Computability.NearSquareRoot.BoundedBranch

/-! # The effective outer command of the recursive interchange -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFrame

open IntegerMultiplication IntegerMultiplication.Code Space CommonRegisters GeneratorSyntax

def literal (b n : ℕ) : Tree := send (tally b,tally n)

/-- Attach the template to the original request, run the common physical
prelude and tail-dispatch the generated stage if the center is nonempty. -/
def node (prelude stage : Cmd) (b n : ℕ) : Cmd :=
  (((Task.prepare 0 (literal b n)).join (pack 0)).join prelude).join (Space.decodeBit .pass stage)

def controller (prelude stage : Cmd) (b n : ℕ) : Cmd := .tie (node prelude stage b n)

theorem effective_node {X : Type} [Primcodable X] (prelude : Cmd)
    {stage : X → Cmd} {b n : X → ℕ} (hs : Effective ltr stage) (hb : Computable b) (hn : Computable n) :
    Effective ltr (fun x => node prelude (stage x) (b x) (n x)) := by
  have radix : Effective ltr (fun x => Task.prepare 0 (send (tally (b x)))) :=
    PhysicalWalshCompile.effective_tally_prepare.comp hb
  have count : Effective ltr (fun x => Task.prepare 0 (send (tally (n x)))) :=
    PhysicalWalshCompile.effective_tally_prepare.comp hn
  have pair := count.join (radix.join (effective_const ltr (pack 0)))
  have choose : Effective ltr (fun x => Space.decodeBit .pass (stage x)) := by
    apply KernelEffectiveFamily.effective_splitRoot _ (fun _ => effective_const _ _)
    apply KernelEffectiveFamily.effective_splitRoot _ _ (effective_const _ _)
    intro bit
    cases bit
    · exact effective_const _ _
    · exact hs
  exact ((pair.join (effective_const ltr (pack 0))).join (effective_const ltr prelude)).join choose

theorem effective_controller {X : Type} [Primcodable X] (prelude : Cmd)
    {stage : X → Cmd} {b n : X → ℕ} (hs : Effective ltr stage) (hb : Computable b) (hn : Computable n) :
    Effective ltr (fun x => controller prelude (stage x) (b x) (n x)) :=
  (effective_node prelude hs hb hn).tie

theorem node_within {R b n : ℕ} {prelude stage : Cmd} (hR : 0 < R)
    (hf : Within R prelude) (hs : Within R stage) : Within R (node prelude stage b n) := by
  change _ ∧ _
  refine ⟨⟨⟨(RegisterWitness.prepare_within _).mpr hR,hR⟩,hf⟩,?_⟩
  apply RegisterWitness.splitRoot_within.mpr
  refine ⟨hR,trivial,trivial,?_⟩
  exact RegisterWitness.splitRoot_within.mpr ⟨hR,trivial,hs,trivial⟩

/-- The prelude finishes before passing its single value to the stage. Thus
its full local footprint can be reused by every later recursive descent.
Only one pending join must be accounted for during this prelude. -/
theorem node_run (b n : ℕ) (prelude stage : Cmd) (env : Env) (deck : Deck) (base : ℕ)
    (hd : DeckCap base deck) (input middle output : Tree) (select : Bool)
    (t u cap depth : ℕ)
    (pre : Fits env prelude (pile 0 (.fork (literal b n) input) deck)
      (pile 0 (.fork (.atom select) middle) deck) t)
    (chosen : BoundedFits env (bif select then stage else .pass) (pile 0 middle deck)
      (pile 0 output deck) u cap depth) :
    let localTime := 5*(literal b n).count + t + 10
    BoundedFits env (node prelude stage b n) (pile 0 input deck) (pile 0 output deck)
      (localTime + u + 10)
      (max cap (base + max (input.count+localTime) (middle.count+2)))
      (max depth (localTime+1)) := by
  intro localTime
  let data := max cap (base + max (input.count+localTime) (middle.count+2))
  let stack := max depth (localTime+1)
  have code := ((Task.fits_prepare 0 (literal b n) env (pile 0 input deck)).join
    (fits_pack (literal b n) input deck 0 env)).join pre
  have head := BoundedFits.of_fits (code.mono (show _ ≤ localTime by dsimp [localTime]; omega))
    (cap:=data) (depth:=localTime) (fun i => by
      have h := (hd.pile 0 input) i
      dsimp only [data]
      omega) le_rfl
  have tailRun := chosen.mono (cap':=data) (depth':=stack) le_rfl (le_max_left ..) (le_max_left ..)
  have decoded := BoundedFits.decodeBit tailRun
    (cap:=data) (depth:=stack) ((hd.pile 0 (.fork (.atom select) middle)).mono (by
      dsimp only [data,Tree.count]; omega)) (by dsimp only [stack]; omega)
  exact (head.join decoded (by dsimp [stack]; omega)).mono (by omega) le_rfl le_rfl

end InterchangeROMFrame

end NearSquareRoot
end Computability
end OAI
