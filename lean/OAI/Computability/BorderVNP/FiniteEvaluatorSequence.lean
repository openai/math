import OAI.Computability.BorderVNP.FiniteEvaluatorLink
import OAI.Computability.BorderVNP.DiagonalNativeSequence

/-! # Composing finite-field returns of the real emitted program

The two field products on the right are read from the standalone program
counters. The product on the left is read from the assembled program counters
after each private instruction has been relocated.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamRAM FieldProcessor
open scoped BigOperators

variable {w m g : ℕ} {Q Γ : Type} {F : Type*} [Field F]

/-- The self-linkage labels of one concrete finite table. -/
def label (c : Code) (i : ℕ) : Fin (c.slots+1) := ⟨min i c.slots, by omega⟩

/-- Every opcode of a standalone source block occupies its actual emitted row. -/
theorem selfContains (c : Code) : Contains c.row (label c) 0 c.slots c := by
  intro i _ hi
  have hlt : i<c.slots := by omega
  simp [label,Code.row,min_eq_left hlt.le,hlt]
  rfl

/-- All genuine returns of a linked fragment retain the same resolved private IDs
and ordered events as execution starting at its own program counter zero. -/
theorem linked_trace {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {c s mem es t mt}
    (run : Runs pub mac c s mem es t mt) (main : Code) (lab : ℕ → Fin (main.slots+1)) {start finish}
    (H : Contains main.row lab start finish c) :
    trace main.program pub mac ⟨lab start,s⟩ es = trace c.program pub mac ⟨0,s⟩ es := by
  obtain ⟨xs,hx⟩ := spelling run
  have own := hx.linked c (label c) 0 c.slots (selfContains c)
  rw [show label c 0=0 by ext; simp [label]] at own
  exact (hx.linked main lab start finish H).trans own.symm

variable (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ)

/-- Field product over the actual standalone instruction fetches of a fragment. -/
noncomputable def weight (c : Code) (s : Bank w) (es : List (TeamRAM.Event w)) : F :=
  pathProduct c.program pub lib ret fuel ⟨0,s⟩ es

/-- The exact field weight of a fragment survives linkage into an enclosing machine. -/
theorem linked_weight {c s mem es t mt} (run : Runs pub (TeamSiteEvents.macros lib fuel) c s mem es t mt)
    (main : Code) (lab : ℕ → Fin (main.slots+1)) {start finish} (H : Contains main.row lab start finish c) :
    pathProduct main.program pub lib ret fuel ⟨lab start,s⟩ es = weight pub lib ret fuel c s es := by
  rw [trace_value lib ret fuel (linkedPrefix run H),linked_trace run main lab H]
  exact (trace_value lib ret fuel (DiagonalResidueRAM.at_last run)).symm

/-- Genuine consecutive fragments multiply even when their private routines
have different field return functions, share the same words, or return zero. -/
theorem weight_seq {a b s mem es t mt fs z mz}
    (r : Runs pub (TeamSiteEvents.macros lib fuel) a s mem es t mt)
    (q : Runs pub (TeamSiteEvents.macros lib fuel) b t mt fs z mz) :
    weight pub lib ret fuel (.seq a b) s (es++fs) =
      weight pub lib ret fuel a s es * weight pub lib ret fuel b t fs := by
  let c := Code.seq a b
  obtain ⟨left,right⟩ := seq_intervals (selfContains c)
  have atZero : label c 0=0 := by ext; simp [label]
  rw [weight,trace_value lib ret fuel (DiagonalResidueRAM.at_last (r.seq q)),← atZero,
    trace_append (linkedPrefix r left),linked_trace r c (label c) left,linked_trace q c (label c) right,
    List.map_append,List.prod_append]
  exact congrArg₂ (· * ·) (trace_value lib ret fuel (DiagonalResidueRAM.at_last r)).symm
    (trace_value lib ret fuel (DiagonalResidueRAM.at_last q)).symm

/-- Exact dependent field-valued sum over physical return histories of a sequence.
Each second-stage return is indexed in the true bank and memory left by the first. -/
theorem sum_seq (a b : Code) (s : Bank w) (mem : Memory w)
    [Fintype (Evaluator.Returns a pub (TeamSiteEvents.macros lib fuel) s mem)]
    [∀ x : Evaluator.Returns a pub (TeamSiteEvents.macros lib fuel) s mem,
      Fintype (Evaluator.Returns b pub (TeamSiteEvents.macros lib fuel) x.val.2.1 x.val.2.2)]
    [Fintype (Evaluator.Returns (.seq a b) pub (TeamSiteEvents.macros lib fuel) s mem)] :
    (∑ x : Evaluator.Returns (.seq a b) pub (TeamSiteEvents.macros lib fuel) s mem,
      weight pub lib ret fuel (.seq a b) s x.val.1) =
    ∑ x : Evaluator.Returns a pub (TeamSiteEvents.macros lib fuel) s mem,
      ∑ y : Evaluator.Returns b pub (TeamSiteEvents.macros lib fuel) x.val.2.1 x.val.2.2,
        weight pub lib ret fuel a s x.val.1 * weight pub lib ret fuel b x.val.2.1 y.val.1 := by
  classical
  rw [← (Evaluator.seqReturnEquiv a b pub (TeamSiteEvents.macros lib fuel) s mem).sum_comp,Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => weight_seq pub lib ret fuel x.property y.property

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
