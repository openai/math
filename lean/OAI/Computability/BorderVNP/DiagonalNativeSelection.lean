import OAI.Computability.BorderVNP.DiagonalNativeUnit
import OAI.Computability.BorderVNP.TeamContractionPaths

/-! # The signed path value of the native evaluator selector

The saved broadcast bit determines one branch. The selector preserves every accepted
choice tape, final outcome and path sign, charging only its load and conditional jump.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM TeamContraction
open scoped BigOperators Classical

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem tape_eq {c : Code} {s : Bank w} {m : Memory w} (z : NativeAccepts c pub macros s m) :
    z.val.2.map TeamRAM.Event.choices = z.val.1 := (TeamRAM.execute_spec z.property).2.2

private theorem eq_of_events {c : Code} {s : Bank w} {m : Memory w}
    {a b : NativeAccepts c pub macros s m} (h : a.val.2 = b.val.2) : a = b :=
  Subtype.ext (Prod.ext ((tape_eq a).symm.trans (by rw [h, tape_eq b])) h)

/-- The body selected by the word actually read at the first position of the saved prefix. -/
def selected (f : BroadcastFrame) (eval : Code) (m : Memory w) : Code :=
  if (m f.dst).val = 0 then unit else eval

private theorem selected_fallsThrough (f : BroadcastFrame) {eval : Code} (m : Memory w)
    (he : eval.withoutAccept = true) : (selected f eval m).withoutAccept = true := by
  unfold selected
  split <;> first | decide | exact he

private theorem select_fallsThrough {eval : Code} (he : eval.withoutAccept = true) :
    (select eval).withoutAccept = true := by
  simp only [select,Code.withoutAccept,show unit.withoutAccept = true by decide,he,Bool.and_self]

/-- The actual two unsigned dispatch events followed by the original branch history. -/
def dispatchEvents (f : BroadcastFrame) (m : Memory w) (es : List (TeamRAM.Event w)) :
    List (TeamRAM.Event w) := branchRead f.dst m :: tick w :: es

private def enterSelector (f : BroadcastFrame) {eval : Code} {s : Bank w} {m : Memory w}
    (h : f.Stable (readings s)) (he : eval.withoutAccept = true)
    (z : NativeAccepts (selected f eval m) pub macros (Function.update s 10 (m f.dst)) m) :
    NativeAccepts (select eval) pub macros s m := by
  let es := dispatchEvents f m z.val.2
  refine ⟨⟨es.map TeamRAM.Event.choices,es⟩,?_⟩
  obtain ⟨⟨t,mt,r⟩,_⟩ := (Code.execute_iff_runs (selected_fallsThrough f m he)).mp z.property
  exact ((select_iff f eval s m h).mpr ⟨_,rfl,r⟩).execute

/-- The complete selector and its genuinely chosen branch have the same accepting paths
including all private choice blocks. Only two initial deterministic events are added. -/
noncomputable def selectorEquiv (f : BroadcastFrame) {eval : Code} {s : Bank w} {m : Memory w}
    (h : f.Stable (readings s)) (he : eval.withoutAccept = true) :
    NativeAccepts (selected f eval m) pub macros (Function.update s 10 (m f.dst)) m ≃
      NativeAccepts (select eval) pub macros s m := by
  refine Equiv.ofBijective (enterSelector f h he) ⟨?_,?_⟩
  · intro a b eq
    apply eq_of_events
    have same : dispatchEvents f m a.val.2 = dispatchEvents f m b.val.2 :=
      congrArg (fun z => z.val.2) eq
    simpa only [dispatchEvents,List.cons.injEq,true_and] using same
  · intro z
    obtain ⟨⟨t,mt,r⟩,_⟩ := (Code.execute_iff_runs (select_fallsThrough he)).mp z.property
    obtain ⟨fs,eq,next⟩ := (select_iff f eval s m h).mp r
    exact ⟨⟨⟨_,fs⟩,next.execute⟩,eq_of_events eq.symm⟩

/-- The event-list projection of the dispatch bijection. -/
theorem selectorEquiv_events (f : BroadcastFrame) {eval : Code} {s : Bank w} {m : Memory w}
    (h : f.Stable (readings s)) (he : eval.withoutAccept = true)
    (z : NativeAccepts (selected f eval m) pub macros (Function.update s 10 (m f.dst)) m) :
    ((selectorEquiv f h he) z).val.2 = dispatchEvents f m z.val.2 := rfl

/-- Dispatch preserves all per-path signs even if the selected branch contains private calls. -/
theorem selector_signed (f : BroadcastFrame) {eval : Code} {s : Bank w} {m : Memory w}
    (h : f.Stable (readings s)) (he : eval.withoutAccept = true)
    [Fintype (NativeAccepts (selected f eval m) pub macros (Function.update s 10 (m f.dst)) m)]
    [Fintype (NativeAccepts (select eval) pub macros s m)] :
    (∑ z : NativeAccepts (select eval) pub macros s m, pathWeight z.val.2) =
      ∑ z : NativeAccepts (selected f eval m) pub macros (Function.update s 10 (m f.dst)) m, pathWeight z.val.2 := by
  rw [← (selectorEquiv f h he).sum_comp (fun z => pathWeight z.val.2)]
  apply Finset.sum_congr rfl
  intro z _
  rw [selectorEquiv_events]
  simp [dispatchEvents,pathWeight,branchRead,tick,TeamRAM.Sign.value]

/-- Every actually accepted unit history has path weight one. -/
theorem unit_weight {s : Bank w} {m : Memory w} (z : NativeAccepts unit pub macros s m) :
    pathWeight z.val.2 = 1 := by
  obtain ⟨⟨_,_,r⟩,_⟩ := (Code.execute_iff_runs (c := unit) (by decide)).mp z.property
  have plus := (unit_trace r).2
  generalize he : z.val.2 = es at plus ⊢
  clear he
  induction es with
  | nil => rfl
  | cons a es ih =>
    change (a.sign.value * pathWeight es) = 1
    rw [plus a (by simp)]
    exact (one_mul _).trans (ih (fun e h => plus e (by simp [h])))

/-- The total signed unit contribution is the Boolean indicator of the physical test. -/
theorem unit_signed {s : Bank w} {m : Memory w} {bound : ℕ} {test : Prop} [Decidable test]
    (h : NativeLinkCheck pub macros unit s m bound test) [Fintype (NativeAccepts unit pub macros s m)] :
    (∑ z : NativeAccepts unit pub macros s m, pathWeight z.val.2) = if test then 1 else 0 := by
  simp only [unit_weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [← Nat.card_eq_fintype_card,native_check_card h (by decide) (by decide)]
  split <;> rfl

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
