import OAI.Computability.BorderVNP.FiniteEvaluatorCells
import OAI.Computability.BorderVNP.DiagonalNativeBudgetValue
import OAI.Computability.BorderVNP.FiniteDiagonalUnitTraceSelected

/-! # The bounded field path sum of a prepared cell evaluator

The continuation starts in its real post-broadcast memory. Its clock excludes
the wide startup, broadcast, and the two selector instructions. The finite
dictionary counts every returning path of the code, including zero field weights.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA RoutingISA.Pins TeamContraction FiniteDiagonal
open scoped BigOperators Classical
open private Fork Fork.bit Fork.event forkSpelling from OAI.Computability.BorderVNP.FiniteEvaluatorLink

variable {w m g : ℕ} {Q Γ : Type} {F : Type*} [Field F]
variable (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : FieldProcessor.Returns Q Γ F m 8) (fuel : ℕ)

/-- The field path sum on an arbitrary incoming RAM image, at its actual three
resource limits. Every field return is read from the fetched private opcode. -/
noncomputable def boundedWeight (c : Code) (s : Bank w) (mem : Memory w) (ticks burst clock : ℕ) : F :=
  letI := Fintype.ofFinite (Evaluator.BoundedReturns c pub (TeamSiteEvents.macros lib fuel) s mem ticks burst clock)
  ∑ z : Evaluator.BoundedReturns c pub (TeamSiteEvents.macros lib fuel) s mem ticks burst clock, weight pub lib ret fuel c s z.val.val.1

/-- An exact finite history dictionary reindexes the true bounded path sum when
every one of its histories fits all three charged cutoffs. -/
theorem boundedWeight_eq_history_sum {c : Code} {s : Bank w} {mem : Memory w} {ticks burst clock : ℕ}
    (paths : Finset (List (TeamRAM.Event w))) (falls : c.withoutAccept = true)
    (accept : ∀ bs es, TeamRAM.execute (c.program.fetch pub (TeamSiteEvents.macros lib fuel)) ⟨0,s⟩ mem bs = some es ↔
      es ∈ paths ∧ es.map TeamRAM.Event.choices = bs)
    (limits : ∀ es ∈ paths, Within ticks burst clock es) :
    boundedWeight pub lib ret fuel c s mem ticks burst clock = ∑ es ∈ paths, weight pub lib ret fuel c s es := by
  let mac : TeamOpcode.Macros w 8 := TeamSiteEvents.macros lib fuel
  let Z := Evaluator.BoundedReturns c pub mac s mem ticks burst clock
  let := Fintype.ofFinite Z
  let events (z : Z) : ↥paths := ⟨z.val.val.1,((accept _ _).mp z.val.property.execute).1⟩
  have bij : Function.Bijective events := by
    constructor
    · intro x y e
      have eq := congrArg Subtype.val e
      obtain ⟨es,t,mt⟩ := x.val.property.eq_of_shared_events y.val.property (congrArg (· ++ []) eq)
      exact Subtype.ext (Subtype.ext (Prod.ext es (Prod.ext t mt)))
    · intro es
      obtain ⟨⟨t,mt,run⟩,_⟩ := (Code.execute_iff_runs falls).mp ((accept _ _).mpr ⟨es.property,rfl⟩)
      exact ⟨⟨⟨(es.val,t,mt),run⟩,limits _ es.property⟩,rfl⟩
  let E := Equiv.ofBijective events bij
  exact (E.sum_comp fun es => weight pub lib ret fuel c s es.val).trans (Finset.sum_coe_sort ..)

private theorem weight_one {c s mem es z mz} (run : Runs pub (TeamSiteEvents.macros lib fuel) c s mem es z mz)
    (det : c.deterministic = true) (unsigned : c.unsigned = true) : weight pub lib ret fuel c s es = 1 :=
  pathProduct_ordinary_positive _ _ _ _ _ _ _ (TeamRAM.execute_spec run.execute).1
    (ordinary_of_deterministic run det) (fun e he => (run.unsigned_events unsigned e he).2)

private theorem weight_right {yes no : Code} {x y : Reg} {s mem es z mz}
    (h : s x ≠ s y) (run : Runs pub (TeamSiteEvents.macros lib fuel) no s mem es z mz) :
    weight pub lib ret fuel (.ifEq x y yes no) s (tick w::es) = weight pub lib ret fuel no s es := by
  let c := Code.ifEq x y yes no
  obtain ⟨xs,hx⟩ := spelling run
  have cond : Fork.bit s (Fork.eq x y) = false := by simp [Fork.bit,h]
  have branch := forkSpelling (Fork.eq x y) yes no (s := s) (by simpa only [cond, Bool.false_eq_true,ite_false] using hx)
  have marked := branch.linked c (label c) 0 c.slots (selfContains c)
  have body := hx.linked no (label no) 0 no.slots (selfContains no)
  have first (a : Code) : label a 0 = 0 := by ext; simp [label]
  rw [first] at marked body
  simp only [Fork.event] at marked
  have full : Runs pub (TeamSiteEvents.macros lib fuel) c s mem (tick w::es) z mz := Runs.ifEq (by simpa only [h,ite_false] using run)
  change FieldProcessor.pathProduct c.program _ _ _ _ _ _ = FieldProcessor.pathProduct no.program _ _ _ _ _ _
  rw [trace_value lib ret fuel (DiagonalResidueRAM.at_last full),trace_value lib ret fuel (DiagonalResidueRAM.at_last run),marked,body]
  simp [value,tick,TeamRAM.Sign.value]

private theorem selector_weight (f : BroadcastFrame) {c s mem es z mz} (stable : f.Stable (readings s))
    (positive : (mem f.dst).val ≠ 0)
    (body : Runs pub (TeamSiteEvents.macros lib fuel) c (Function.update s 10 (mem f.dst)) mem es z mz) :
    weight pub lib ret fuel (Evaluator.select c) s (Evaluator.dispatchEvents f mem es) =
      weight pub lib ret fuel c (Function.update s 10 (mem f.dst)) es := by
  let b := Function.update s 10 (mem f.dst)
  have guard : b 10 ≠ b 0 := by
    intro e
    have h := congrArg Fin.val e
    simp only [b,Function.update_self,Function.update_of_ne (by decide : (0 : Reg) ≠ 10)] at h
    exact positive (h.trans stable.1)
  have load := Runs.load pub (TeamSiteEvents.macros lib fuel) 10 9 s mem
  rw [show (s 9).val = f.dst from stable.2.2.2.2.2.2.2.2.2.1] at load
  have branch : Runs pub (TeamSiteEvents.macros lib fuel) (.ifEq 10 0 Evaluator.unit c) b mem (tick w::es) z mz :=
    Runs.ifEq (by simpa only [guard,ite_false] using body)
  exact (weight_seq pub lib ret fuel load branch).trans (by
    rw [weight_one pub lib ret fuel load rfl rfl,one_mul,weight_right pub lib ret fuel guard body])

/-- Bijection between the true field-weighted wide-boot paths and the bounded
body returns on the positive branch. It preserves the chronological tape after
the fixed prefix, and reads every field return at its relocated opcode. -/
theorem positive_weightedBodyEquiv (c : Code) {L : Pins.Layout} (fields : ProcessorFields L) (f : BroadcastFrame)
    (s : Bank w) {pre post after hs b mb} (startup : Runs pub (TeamSiteEvents.macros lib fuel) wideStartup s
      (Evaluator.processorMemory fields w) pre post after)
    (header : Runs pub (TeamSiteEvents.macros lib fuel) readBroadcast post after hs b mb)
    (stable : f.Stable (readings b)) (positive : (mb f.dst).val ≠ 0) (falls : c.withoutAccept = true)
    (ticks burst clock : ℕ) (fit : pre.length+hs.length+2 ≤ ticks) :
    let M := Evaluator.processorMachine (dispatchTable wideStartup c) pub (TeamSiteEvents.macros lib fuel) s fields
    ∃ E : Evaluator.BoundedReturns c pub (TeamSiteEvents.macros lib fuel) (Function.update b 10 (mb f.dst)) mb
        (ticks-(pre.length+hs.length+2)) burst clock ≃ NativePath M ticks burst clock,
      ∀ x, (E x).val = Evaluator.dispatchPrefix f mb pre hs ++ x.val.val.1 ∧
        weight pub lib ret fuel (dispatchTable wideStartup c) s (E x).val =
          weight pub lib ret fuel c (Function.update b 10 (mb f.dst)) x.val.val.1 := by
  intro M
  obtain ⟨E,events⟩ := charged_positiveBodyEquiv fields f startup header stable positive falls ticks burst clock fit
  refine ⟨E,fun x => ⟨events x,?_⟩⟩
  have body := x.val.property
  have branch : Runs pub (TeamSiteEvents.macros lib fuel) (Evaluator.select c) b mb
      (Evaluator.dispatchEvents f mb x.val.val.1) x.val.val.2.1 x.val.val.2.2 :=
    (Evaluator.select_iff f c b mb stable).mpr ⟨_,rfl,by simpa only [positive,ite_false] using body⟩
  have path := events x
  rw [path]
  have rearrange : Evaluator.dispatchPrefix f mb pre hs ++ x.val.val.1 = pre ++ (hs ++ Evaluator.dispatchEvents f mb x.val.val.1) := by
    simp [Evaluator.dispatchPrefix,Evaluator.dispatchEvents,List.append_assoc]
  rw [rearrange,dispatchTable,weight_seq pub lib ret fuel startup (header.seq branch),weight_seq pub lib ret fuel header branch,
    weight_one pub lib ret fuel startup (by decide) (by decide),weight_one pub lib ret fuel header (by decide) (by decide),one_mul,one_mul]
  exact selector_weight pub lib ret fuel f stable positive body

/-- On the positive tag, the actual wide-boot table and its bounded continuation
have identical field sums. The remaining clock subtracts precisely the two
real prefix lengths and two dispatch instructions. -/
theorem positive_native_sum (c : Code) {L : Pins.Layout} (fields : ProcessorFields L) (f : BroadcastFrame)
    (s : Bank w) {pre post after hs b mb} (startup : Runs pub (TeamSiteEvents.macros lib fuel) wideStartup s
      (Evaluator.processorMemory fields w) pre post after)
    (header : Runs pub (TeamSiteEvents.macros lib fuel) readBroadcast post after hs b mb)
    (stable : f.Stable (readings b)) (positive : (mb f.dst).val ≠ 0) (falls : c.withoutAccept = true)
    (ticks burst clock : ℕ) (fit : pre.length+hs.length+2 ≤ ticks) :
    let M := Evaluator.processorMachine (dispatchTable wideStartup c) pub (TeamSiteEvents.macros lib fuel) s fields
    letI := Fintype.ofFinite (NativePath M ticks burst clock)
    (∑ p : NativePath M ticks burst clock, weight pub lib ret fuel (dispatchTable wideStartup c) s p.val) =
      boundedWeight pub lib ret fuel c (Function.update b 10 (mb f.dst)) mb (ticks-(pre.length+hs.length+2)) burst clock := by
  intro M
  let := Fintype.ofFinite (NativePath M ticks burst clock)
  let := Fintype.ofFinite (Evaluator.BoundedReturns c pub (TeamSiteEvents.macros lib fuel) (Function.update b 10 (mb f.dst))
    mb (ticks-(pre.length+hs.length+2)) burst clock)
  obtain ⟨E,events⟩ := positive_weightedBodyEquiv pub lib ret fuel c fields f s startup header stable positive falls ticks burst clock fit
  unfold boundedWeight
  rw [← E.sum_comp (fun z => weight pub lib ret fuel (dispatchTable wideStartup c) s z.val)]
  apply Finset.sum_congr rfl
  intro x _
  exact (events x).2

namespace Cells

variable [Fintype F] (X : Inputs F)

/-- A prepared field-cell image evaluates its actual sparse validators and reports
in the bounded-return model on that memory. No initialized-header assumption is
needed for this continuation. -/
theorem bounded_prepared (s : Bank w) (mem : Memory w) (n ticks burst clock : ℕ)
    (h : Prepared X pub mem n) (time : X.validatorCost pub mem + X.scalarCost ≤ ticks)
    (words : TeamScales.width n (1/2) ≤ burst) (choices : n^25 ≤ clock) :
    let f := CellDispatch.Frame.ofMemory pub mem
    boundedWeight pub (library F) (terminals F) (CompactMachine.nativeClock n) code s mem ticks burst clock =
      ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod := by
  obtain ⟨paths,accept,limits,val⟩ := prepared_value X pub s mem n h
  apply Eq.trans (boundedWeight_eq_history_sum pub _ _ _ paths (by decide) accept _) val
  intro es he
  have q := limits es he
  exact ⟨q.cost.trans time,fun e hh => (q.length e hh).trans words,fun e hh => (q.choices e hh).trans choices⟩

/-- The full bounded field sum of wide startup, positive-tag dispatch and the
prepared cell evaluator. Both scalar and signed opcodes execute in the physical
program after loading the broadcast word. -/
theorem wide_prepared (n : ℕ) {L : Pins.Layout} (fields : ProcessorFields L) (f : BroadcastFrame)
    (s : Bank w) {pre post after hs b mb}
    (startup : Runs pub (TeamSiteEvents.macros (library F) (CompactMachine.nativeClock n)) wideStartup s
      (Evaluator.processorMemory fields w) pre post after)
    (header : Runs pub (TeamSiteEvents.macros (library F) (CompactMachine.nativeClock n)) readBroadcast post after hs b mb)
    (stable : f.Stable (readings b)) (positive : (mb f.dst).val ≠ 0)
    (ticks burst clock : ℕ) (h : Prepared X pub mb n)
    (time : pre.length+hs.length+2 + (X.validatorCost pub mb+X.scalarCost) ≤ ticks)
    (words : TeamScales.width n (1/2) ≤ burst) (choices : n^25 ≤ clock) :
    let M := Evaluator.processorMachine (dispatchTable wideStartup code) pub
      (TeamSiteEvents.macros (library F) (CompactMachine.nativeClock n)) s fields
    letI := Fintype.ofFinite (NativePath M ticks burst clock)
    let d := CellDispatch.Frame.ofMemory pub mb
    (∑ p : NativePath M ticks burst clock,
      weight pub (library F) (terminals F) (CompactMachine.nativeClock n) (dispatchTable wideStartup code) s p.val) =
      ((((d.ownedRows mb 0 d.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod :=
  (positive_native_sum pub _ _ _ code fields f s startup header stable positive (by decide) _ _ _ (by omega)).trans
    (bounded_prepared pub X _ mb n _ _ _ h (by omega) words choices)

end Cells
end FiniteEvaluator

end BorderVNP
end Computability
end OAI
