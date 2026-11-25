import OAI.ThreeFlat.Diagonal.TraceMass
import OAI.Hierarchy.TaggedShorterControlHistory
import OAI.Hierarchy.TaggedShorterHistoryNative

namespace OAI
/-! # Unique binary history of an installed descriptor controller -/

noncomputable section
namespace Hierarchy.TaggedShorterControlHistory
open ThreeFlat Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open scoped Classical

variable {w p r k S f u t : ℕ}

private theorem read_render (hw : 3≤w+1) (hp : p≤2^(w+1))
    (xs : List (Row (w+1) (Snapshot w p r))) (length : xs.length=f) :
    let atTime : Fin f → Row (w+1) (Snapshot w p r) := fun i => xs.get (i.cast length.symm)
    List.ofFn (readCpu hw hp (writeCpu hw hp atTime))=xs := by
  subst f
  simp

/-- A native deterministic execution with one reported terminal state
decodes one bit history, and its observed words are exactly its real image. -/
theorem unique_for_report (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (S f : ℕ) (addr : Fin u → Word (w+1)) (header : ℕ → Word (w+1)) (R : Report (w+1))
    (native : RAM.reports (exposed M) f ((exposed M).start (wide st)) (initialMemory S header) = [R]) :
    let image := fun i => after (initialMemory S header) R.events (addr i).val
    ∃ raw : TaggedShorterClock.Pin w r f → Bool,
    ∀ bytes out, Valid M hw hp st S addr header bytes out ↔ bytes=raw ∧ out=image := by
  let P := exposed M
  let c := P.start (wide st)
  let mem := initialMemory S header
  have singleton : RAM.reports P f c mem=[R] := native
  have memR : R ∈ RAM.reports P f c mem := by rw [singleton]; exact List.mem_singleton.mpr rfl
  obtain ⟨rs,⟨hlen,hl,hr,hc⟩,uniq⟩ :=
    (existsUnique_rows_iff P f c mem R).mpr memR
  let xs := fun i : Fin f => rs.get (i.cast hlen.symm)
  let raw := Function.uncurry (writeCpu hw hp xs)
  have hx : List.ofFn xs=rs := by
    simpa only [read_write_cpu] using read_render hw hp rs hlen
  refine ⟨raw,?_⟩
  intro bytes out
  constructor
  · rintro ⟨fixed,localOK,readOK,outputs⟩
    let ys := readCpu hw hp (Function.curry bytes)
    let log := List.ofFn ys
    have admitted : report log ∈ RAM.reports P f c mem := by
      refine (RAM.mem_reports_iff ..).mpr ⟨?_,readOK⟩
      simpa [log] using (local_spec localOK).1
    have same : report log=R := by simpa only [singleton,List.mem_singleton] using admitted
    have matched : log=rs := uniq log ⟨by simp [log],localOK,same,readOK⟩
    have sameRows : ys=xs := List.ofFn_injective (matched.trans hx.symm)
    constructor
    · change bytes=Function.uncurry (writeCpu hw hp xs)
      rw [←sameRows,fixed]
      rfl
    · funext i
      exact (outputs i).trans (congrArg (fun l : Report (w+1) => after mem l.events (addr i).val) same)
  · rintro ⟨rfl,rfl⟩
    change Valid M hw hp st S addr header (Function.uncurry (writeCpu hw hp xs)) _
    simp only [Valid,Function.curry_uncurry,read_write_cpu,hx]
    exact ⟨trivial,hl,hc,fun i=>congrArg (fun l : Report (w+1) => after mem l.events (addr i).val) hr.symm⟩

/-- For a compiled native machine, no alternative bit history can agree
with the CPU and sorted readings. Output RAM reads share one assignment. -/
theorem unique_native (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (S f : ℕ) (addr : Fin u → Word w) (header : ℕ → Word w) (hs : S≤2^w)
    (done : Config w p r) (out : Memory w) (result : Option (Word w))
    (inside : t<f)
    (ran : RAM.advance M.program t (M.program.start st) (initialMemory S header)=some (done,out))
    (halt : M.program.step done=.finish result) :
    ∃ raw : TaggedShorterClock.Pin w r f → Bool, ∀ bytes observed,
      Valid M hw hp st S (wide ∘ addr) (wide ∘ header) bytes observed ↔
        bytes=raw ∧ observed=fun i => wide (out (addr i).val) := by
  have initial : Matches (initialMemory S (wide ∘ header)) (initialMemory S header) (M.program.start st).privateMem := by
    have image : inputBank (initialMemory S header) = initialMemory S (wide ∘ header) :=
      TraceRows.inputBank_initialMemory S header hs
    rw [← image]
    exact matches_inputBank _
  obtain ⟨img,adv,agrees⟩ := TaggedShorterHistory.advance_exposed M initial ran
  obtain ⟨es,len,rep,only⟩ := TaggedShorterHistory.advance_report (exposed M) adv
  have resultReport := only (f-t-1) (result.map wide) (TaggedShorterHistory.finish_exposed M done result halt)
  rw [show t+(f-t-1)+1=f by omega] at resultReport
  have start : snapshot (M.program.start st)=(exposed M).start (wide st) := by simp [exposed,Machine.program,snapshot]
  rw [start] at resultReport
  have unique := unique_for_report M hw hp st S f (wide ∘ addr) (wide ∘ header) ⟨es,result.map wide⟩ resultReport
  have output : (fun i => after (initialMemory S (wide ∘ header)) es ((wide ∘ addr) i).val) =
      (fun i => wide (out (addr i).val)) := by
    funext i
    exact (congrFun rep (addr i).val).trans (agrees.external (addr i))
  simpa only [output] using unique

end Hierarchy.TaggedShorterControlHistory

end
end OAI
