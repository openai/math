import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeStep
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeTrace
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileTie
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileBase

/-! # Generating and closing the recursive command for each selected plan -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile.Node

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode KernelPass
open GeneratorSyntax CommonRegisters Filter

/-- The tied program on arbitrary well-formed, representable invocations, for
every solution of its recurrence. -/
def AllTrace {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)
    (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s) (cmd : Cmd) : Prop :=
  let vm := spec hw p scan arena cost
  ∃ C : ℕ, ∀ T S, vm.Recurrence p.calls C T S → ∀ x env park b, DeckCap b park →
    BoundedFits env cmd (pile 0 (vm.query x) park) (pile 0 (vm.reply x) park)
      (T (vm.world x)) (b+S (vm.world x)) (S (vm.world x))

/-- Generate the signed-record interpreter from the actual plan command.
The descriptor degree and register bound are independent of the template.
The emitted command is selected before its run's resource bounds and results. -/
theorem compile {J : Type} [Primcodable J] (dims : J → ℕ × ℕ) (dimsC : Computable dims)
    (emit : J → Cmd) (emitC : Effective ltr emit) (M : ℕ) (reg : ∀ j, Within M (emit j)) :
    ∃ (tagged : J → Cmd) (R D : ℕ), 1 ≤ D ∧ 0 < R ∧
      Effective ltr tagged ∧ Effective ltr (fun j => entry.join (tagged j)) ∧
      (∀ j, Within R (entry.join (tagged j))) ∧
      ∀ j (hw : 0 < (dims j).2) (p : Plan ((dims j).1+1) (dims j).2 (dims j).2)
        (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s),
        (∀ s, allowance ((dims j).1+1) D s ≤ arena s) → Dispatch.Body hw p scan arena cost (emit j) →
        AllTrace hw p scan arena cost (tagged j) ∧ NamedTrace hw p scan arena cost (tagged j) := by
  obtain ⟨prep,restore,K,f,hp,hr,hf,hK,hframes⟩ := compileFrames
  obtain ⟨R,pos,RK,RM,baseFit,entryFit⟩ := ((eventually_ge_atTop 1).and
    ((eventually_ge_atTop K).and ((eventually_ge_atTop M).and (terminal_registers.and entry_registers)))).exists
  let step j := ((prep (dims j)).join (emit j)).join (restore (dims j))
  let tagged j := Prog.tie (decodeBit terminal.command (step j))
  have prepC : Effective ltr (fun j => prep (dims j)) := hp.comp dimsC
  have restoreC : Effective ltr (fun j => restore (dims j)) := hr.comp dimsC
  have stepC : Effective ltr step := (prepC.join emitC).join restoreC
  have taggedC : Effective ltr tagged := effective_tied terminal_effective stepC
  have fit (j : J) : Within R (step j) :=
    ⟨⟨RegisterSelect.within_mono RK _ (hK _).1,RegisterSelect.within_mono RM _ (reg j)⟩,
      RegisterSelect.within_mono RK _ (hK _).2⟩
  let D := max terminal.degree f
  refine ⟨tagged,R,D,hf.trans (le_max_right ..),pos,taggedC,entry_effective.join taggedC,
    fun j => ⟨entryFit,tied_within pos baseFit (fit j)⟩,?_⟩
  intro j hw p scan arena cost capacity body
  have one := terminal_closed hw p scan arena cost
    (fun s => (allowance_mono (le_max_left terminal.degree f) s).trans (capacity s))
  have next := successor hw p scan arena cost _ _ _ (hframes (dims j).1 (dims j).2)
    (fun s => (allowance_mono (le_max_right terminal.degree f) s).trans (capacity s)) body
  exact ⟨(spec hw p scan arena cost).tieNamed terminal.command (step j) one next,
    namedTrace hw p scan arena cost terminal.command (step j) one next⟩

end PhysicalWalshCompile.Node

end NearSquareRoot
end Computability
end OAI
