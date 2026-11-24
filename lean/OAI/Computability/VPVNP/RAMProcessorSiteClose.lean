import OAI.Computability.VPVNP.RAMProcessorSiteEntry
import OAI.Computability.VPVNP.RAMProcessorGraphProbeEmit

/-!
# Exact-use validation and closing the physical bucket

The last test consumes no further guesses. A nonempty suffix or an incorrect
outgoing cut reaches the rejecting graph row. On success the graph pads the
record array to its public size and exposes its serialized bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM PrivateRAM RAMSerialization

variable {w p r k : ℕ}

/-- Accept the report list when all choices were consumed and advancing the incoming cut
matches the target. At a site without a target, the advanced cut must be halted. -/
def checkResult (s : Snapshot w p r k) (rs : List (Report w)) (tail : List Bool) :
    Option (List (Report w)) :=
  if tail = [] then
    match s.tests.target with
    | some c => if c = s.tests.cut.advance rs then some rs else none
    | none => if (s.tests.cut.advance rs).state = none then some rs else none
  else none

private theorem checkResult_eq {s u : Snapshot w p r k} {old new : List (WordRecord w)}
    {rs : List (Report w)} {tail : List Bool} (h : Progress s u old new rs tail) :
    checkResult s rs tail = if SiteTests.finalCheck.eval u.tests = .finish then some rs else none := by
  classical
  rw [SiteTests.final_eval]
  change checkResult s rs tail = if (if u.choices = [] ∧
    (match u.tests.target with | some c => c = u.tests.cut | none => u.tests.cut.state = none)
    then SiteTests.Exit.finish else SiteTests.Exit.reject) = SiteTests.Exit.finish then some rs else none
  rw [h.bits, h.target, h.cut]
  unfold checkResult
  cases s.tests.target <;> split_ifs <;> simp_all

/-- Physical execution specification for a completed site. Native failure reaches a rejecting
row, and native success reaches the done label with the exact report history, exhausted
choices and padded record block. -/
def ClosedRun (T : Template p r k) (hw : 2 ≤ w) (s : Snapshot w p r k)
    (old : List (WordRecord w)) (l : Label p r) (t : ℕ) (native : Option (List (Report w))) : Prop :=
  match native with
  | none => RejectRun (table T) t (atLabel T l) s.bank
  | some rs => ∃ u ys, Progress s u old ys rs [] ∧
      StackRuns (table T) t (atLabel T l) s.bank (atLabel T .done)
        (u.afterClose hw s.publicH ys).bank

/-- Upper bound on stack steps for the final cut and choice checks, padding to four times the
public site allowance and exposing the five-word records as bits. -/
def closeWork (w H : ℕ) := 40*w+42+(4*H)*(25*w+12)+1+(2*(4*H*5*w)+1)

private theorem finalize {T : Template p r k} (hw : 2 ≤ w) {s : Snapshot w p r k}
    {old : List (WordRecord w)} {l : Label p r} {t : ℕ} {native : Option (List (Report w) × List Bool)}
    (hr : LoopRun T (fun u ys => RecordBuffer.Holds hw s.publicH ys u.records) l .finalCheck s old t native) :
    ∃ n ≤ t+closeWork w s.publicH,
      ClosedRun T hw s old l n (native.bind fun (rs, tail) => checkResult s rs tail) := by
  cases native with
  | none => exact ⟨t, Nat.le_add_right .., hr⟩
  | some z =>
    obtain ⟨rs, tail⟩ := z
    obtain ⟨u, ys, hh, hp, run⟩ := hr
    simp only [Option.bind_some]
    rw [checkResult_eq hp]
    obtain ⟨b, hb, hfinal⟩ := finalCheck_run T u
    by_cases he : SiteTests.finalCheck.eval u.tests = .finish
    · rw [ite_eq_left he] at hfinal ⊢
      have hout := close_run T u hw hh
      have htail : tail = [] := by
        by_contra hbad
        have hn : u.tests.choices ≠ [] := fun hz => hbad (hp.bits.symm.trans hz)
        rw [SiteTests.final_eval] at he
        simp [hn] at he
      subst tail
      have hlen := Nat.mul_le_mul_right (25*w+12) (Nat.sub_le (4*s.publicH) ys.length)
      refine ⟨_, ?_, u, ys, hp, (run.trans hfinal).trans hout⟩
      unfold closeWork
      omega
    · rw [ite_eq_right he] at hfinal ⊢
      exact ⟨_, by unfold closeWork; omega, _, _, run.trans hfinal, reject_row T⟩

/-- Physical execution from the already initialized record buffer through
the unique terminal row of the graph, including exact incoming/outgoing
cuts, the native site/call caps, and an arbitrary private choice stream. -/
theorem checkEntry_close {T : Template p r k} {ready : Bool → BoundaryInvariant w p r k}
    {work : ℕ} (call : StartRuns T ready work) (hw : 2 ≤ w)
    (hbuf : ∀ first u ys, ready first u ys → RecordBuffer.Holds hw u.publicH ys u.records)
    (s : Snapshot w p r k) (old : List (WordRecord w)) (hs : ready true s old) (S v : ℕ)
    (hl : s.lower.val = v*s.publicH) (hb : s.boundary.val = (v+1)*s.publicH)
    (hc : s.cap.val = S*s.publicH) (hleft : s.siteLeft = 2*s.publicH-1) :
    ∃ n ≤ siteWork w s.publicH work+closeWork w s.publicH,
      ClosedRun T hw s old .checkEntry n
        (validateSite (T.instantiate w s.pub).program s.publicFuel S s.publicH v s.tests.cut s.tests.target s.choices) := by
  obtain ⟨t, ht, run⟩ := checkEntry_loop call hbuf s old hs S v hl hb hc hleft
  have hr : LoopRun T (fun u ys => RecordBuffer.Holds hw s.publicH ys u.records) .checkEntry .finalCheck s old t
      (runSite (T.instantiate w s.pub).program s.publicFuel S s.publicH v s.tests.cut s.choices) := by
    generalize ho : runSite (T.instantiate w s.pub).program s.publicFuel S s.publicH v s.tests.cut s.choices = z at run ⊢
    cases z with
    | none => exact run
    | some z =>
      obtain ⟨rs,tail⟩ := z
      obtain ⟨u,ys,hh,hp,hr⟩ := run
      exact ⟨u,ys,hp.H ▸ hh,hp,hr⟩
  obtain ⟨n,hn,hfinish⟩ := finalize hw hr
  exact ⟨n, by omega, hfinish⟩

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
