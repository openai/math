import OAI.Computability.VPVNP.PairNativeFrameGeometry
import OAI.Computability.VPVNP.PrimedCounterRenameRun
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-! # Relocating the terminal frame's header reads and address computation -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM

variable {r w : ℕ}

/-- Copy the caller's header address and role offset into the work bank, then execute the six
header reads and compute the frame geometry. -/
def prelude (degree : ℕ) (reg : R ↪ Fin r) (savedHeader savedRole : Fin r) : Flow r 11 :=
  .seq (.seq (.line (.copy (reg 0) savedHeader)) (.line (.copy (reg 1) savedRole)))
    (PrimedCounter.renameFlow reg id (.seq reads (arithmetic degree)))

/-- Event trace of frame preparation through the arithmetic exit, including both entry copies
and the six external header probes. -/
def preludeEvents (degree : ℕ) (header : Word w) (m : Memory w) : List (Event w) :=
  [.tick,.tick] ++ (readEvents header m ++ List.replicate (degree+18) .tick)

theorem tick_cost (n : ℕ) :
    countProbes (List.replicate n (.tick : Event w)) = 0 ∧ choiceBits (List.replicate n (.tick : Event w)) = [] := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa only [List.replicate_succ,countProbes,choiceBits] using ih

theorem prelude_cost (degree : ℕ) (header : Word w) (m : Memory w) :
    (preludeEvents degree header m).length = degree+114 ∧
      countProbes (preludeEvents degree header m) = 6 ∧ choiceBits (preludeEvents degree header m) = [] := by
  obtain ⟨l,p,b⟩ := reads_cost header m
  obtain ⟨tp,tb⟩ := tick_cost (w := w) (degree+18)
  refine ⟨?_,?_,?_⟩
  · simp [preludeEvents,l]; omega
  · change countProbes (readEvents header m ++ List.replicate (degree+18) .tick) = _
    rw [countProbes_append,p,tp]
  · change choiceBits (readEvents header m ++ List.replicate (degree+18) .tick) = _
    rw [Flow.choiceBits_append,b,tb]; rfl

theorem prelude_run (degree : ℕ) (reg : R ↪ Fin r) (savedHeader savedRole : Fin r)
    (free : savedRole ≠ reg 0) (pub : Fin 11 → Word w) (st : Word w) (m : Memory w) (rs : Regs w r) :
    ∃ out, Flow.Exec pub st (prelude degree reg savedHeader savedRole) rs m
      (preludeEvents degree (rs savedHeader) m) out m ∧
      Ready reg pub degree (rs savedHeader) (rs savedRole) m out ∧
      ∀ j, j ∉ Set.range reg → out j = rs j := by
  let t := Function.update rs (reg 0) (rs savedHeader)
  let u := Function.update t (reg 1) (rs savedRole)
  have ht : t savedRole = rs savedRole := Function.update_of_ne free ..
  have copy0 : Flow.Exec pub st (.line (.copy (reg 0) savedHeader)) rs m [.tick] t m := .line rfl
  have copy1 : Flow.Exec pub st (.line (.copy (reg 1) savedRole)) t m [.tick] u m := by
    apply Flow.Exec.line; simp only [Op.effect,ht,u]
  let small := u ∘ reg
  have h0 : small 0 = rs savedHeader := by simp [small,u,t]
  have h1 : small 1 = rs savedRole := Function.update_self ..
  let s := loaded (small 0) m small
  have run := (reads_run pub st m small).seq (arithmetic_run pub st m s degree rfl)
  obtain ⟨out,body,ins,outside⟩ := PrimedCounter.liftExec reg id pub run u rfl
  have head := (copy0.seq copy1).seq body
  refine ⟨out,?_,?_,?_⟩
  · simpa only [prelude,preludeEvents,List.cons_append,List.nil_append,h0] using head
  · have q := arithmetic_ready degree pub (small 0) m small
    rw [←h0,←h1]
    exact ⟨(congrFun ins 2).trans q.graph,(congrFun ins 18).trans q.cursor,
      (congrFun ins 15).trans q.unit,fun i => (congrFun ins (fieldReg i)).trans (q.field i)⟩
  · intro j hj
    have hn (i : R) : j ≠ reg i := fun eq => hj ⟨i,eq.symm⟩
    rw [outside j hj]
    simp only [u,t,Function.update_of_ne (hn 0),Function.update_of_ne (hn 1)]

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
