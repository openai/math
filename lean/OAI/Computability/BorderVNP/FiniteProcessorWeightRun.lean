import OAI.Computability.BorderVNP.FiniteProcessorWeightPrivate
import OAI.Computability.BorderVNP.TeamLink

/-! # Exact field-valued private executions inside the physical validator

The compiled private routine is installed at the actual block, loop and callback
labels and the actual named work ports of the processor. Its original instruction
count and choice string are retained.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamPrivateTape TeamPrivateFragment
variable {Q Γ : Type} {p r k a m g : ℕ} {F : Type*} [Field F] [Fintype F]

/-- The private compiler ports, installed at the physical processor. -/
def ports : TeamPrivateInput.NativePort m g → TeamSite.Layout.Port r k (m*g) :=
  TeamSite.Layout.site ∘ TeamSite.privateTape

omit [Field F] [Fintype F] in
/-- Distinct work tapes remain distinct after every nested installation. -/
theorem ports_injective : Function.Injective (ports (r := r) (k := k) (m := m) (g := g)) :=
  TeamSite.Layout.site_injective.comp TeamSite.privateTape_injective

/-- Actual processor control of a private field execution, with all outer continuation
information and its current field accumulator. -/
def installed {P : TeamOpcode.Program p r k a} (last : Bool) (sg : Option Bool) (j : Fin a) (pc : Fin p)
    (s : FieldStack.ProductState (TeamPrivateCompiler.Control Q m g) F) :
    FieldStack.ProductState (Processor.Label P Q m g) F :=
  (.block (.loop last (.privateCall sg j pc s.1)),s.2)

private theorem installed_rows (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (w : Returns Q Γ F m a) (last : Bool) (sg : Option Bool) (j : Fin a) (pc : Fin p)
    (q : FieldStack.ProductState (TeamPrivateCompiler.Control Q m g) F)
    (hc : ((privateCode (lib j) (w j)) q).returns = false) :
    code P lib w (installed last sg j pc q) =
      ((privateCode (lib j) (w j)) q).rename ports (installed last sg j pc) := by
  rcases q with ⟨q,acc⟩
  cases q with
  | result out => simp [privateCode,FieldStack.productCode,TeamPrivateCompiler.code,StackOp.returns] at hc
  | load z =>
    simp only [code,FieldStack.productCode,installed,factor,Processor.code,Endpoint.code,Loop.code,
      Macro.rows,privateCode]
    cases TeamPrivateCompiler.code (lib j).alphabet (lib j).digit (lib j).inputTape (lib j).table (lib j).start (.load z) <;> rfl
  | run z =>
    simp only [code,FieldStack.productCode,installed,factor,Processor.code,Endpoint.code,Loop.code,
      Macro.rows,privateCode]
    cases TeamPrivateCompiler.code (lib j).alphabet (lib j).digit (lib j).inputTape (lib j).table (lib j).start (.run z) <;> rfl

/-- A native private path, on the actual received raw words, is replayed by the
full field processor. The accumulator records precisely the correcting factor for
that source return, and every external stack outside the call bank is preserved. -/
theorem installed_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a)
    (last : Bool) (sg : Option Bool) (j : Fin a) (pc : Fin p) (raw : List Bool)
    {n choices out u} (run : Run (trackTable (lib j).alphabet (lib j).table) n (lib j).start
      (tracks (lib j).alphabet (input (lib j).alphabet.blank (lib j).digit (lib j).inputTape raw)) choices out u)
    (fuel : ℕ) (hf : n < fuel) (acc : F) (suffix : List Bool)
    (base : Stacks (TeamSite.Layout.Port r k (m*g))) (hb : base ∘ ports = TeamPrivateInput.initial raw) :
    let ret := FieldSelect.nativeReturn (lib j).table (lib j).alphabet.blank (w j) fuel (lib j).start
      (input (lib j).alphabet.blank (lib j).digit (lib j).inputTape raw) choices
    StackRuns (replay (code P lib w)) (TeamPrivateInput.steps g raw+(n*(2*(m*g)+2)+1+TeamPrivateCleanup.steps (bank u)))
      (installed last sg j pc (.load .start,Fintype.equivFin F acc),choices++suffix) base
      (installed last sg j pc (.result out,Fintype.equivFin F (acc*adjustment out ret)),suffix)
      (installStacks ports base (fun _ => [])) := by
  intro ret
  have h := private_run (lib j) (w j) raw run fuel hf acc suffix
  have lifted := TeamLink.replay_lift h (code P lib w) ports ports_injective (installed last sg j pc)
    base (installed_rows P lib w last sg j pc)
  rwa [installStacks_eq ports_injective base (TeamPrivateInput.initial raw) (congrFun hb)] at lifted

/-- At the genuine callback return the original loop updates its accumulated sign
and the field accumulator carries the exact source correction to the reset state. -/
theorem return_step (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a)
    (last : Bool) (sg : Option Bool) (j : Fin a) (pc : Fin p) (out : Option Bool) (acc : F)
    (suffix : List Bool) (base : Stacks (TeamSite.Layout.Port r k (m*g))) :
    StackRuns (replay (code P lib w)) 1
      (installed last sg j pc (.result out,Fintype.equivFin F acc),suffix) base
      ((.block (.loop last (Loop.resume (Loop.times sg out) pc)),Fintype.equivFin F acc),suffix) base := by
  apply StackRuns.cons _ (StackRuns.nil ..)
  exact .goto (by simp [replay,code,FieldStack.productCode,installed,Processor.code,Endpoint.code,
    Loop.code,factor,privateFactor,StackOp.rename])

end FieldProcessor

end BorderVNP
end Computability
end OAI
