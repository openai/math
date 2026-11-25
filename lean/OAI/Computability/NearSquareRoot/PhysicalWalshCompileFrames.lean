import OAI.Computability.NearSquareRoot.PhysicalWalshCompileLane
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileFrameCode
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileFrameValues

/-! # Effective commands for opening and closing each rectangular node bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompile

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode PhysicalWalshContext
open GeneratorSyntax CommonRegisters Filter

private abbrev Flat := List Dusk.Pair
private abbrev Bank := List Flat

/-- The pair of exact physical traces used around a recursive tensor program. -/
def Framing (a W d : ℕ) (prep restore : Cmd) : Prop := ∀ (hW : 0 < W) (I : Type) (s : I → Shape),
    (∀ i, 0 < (s i).level) → (∀ i, W^(s i).level ∣ (s i).pref) →
    let V := allowance (a+1) d ∘ s
    let layout := routeLayout (coords a W) Shape.w (Header.wire (a+1))
    (∀ x : (i : I) → Data (s i), ClosedRuns prep V V (fun i => buffer (a+1) (s i) (x i))
      (fun i => send (packet layout (s i) (lane (a+1) W (s i) (x i))))) ∧
    (∀ y : (i : I) → Fin W → Data (s i), ClosedRuns restore V V (fun i => send (packet layout (s i) (y i)))
      (fun i => buffer (a+1) (s i) (unlane (a+1) hW (s i) (y i))))

private def save (p : Bank × FrameCode.Saved) := (p.2,p.1)
private def strip (p : FrameCode.Saved × Bank) := (p.1.2,p.2)
private def finish (p : Flat × FrameCode.Saved) := (p.2.2,p.1)

/-- The full frame emitters have a joint computability proof, one data-register
ceiling, and one descriptor degree across every template width and arity. -/
theorem compileFrames : ∃ (prep restore : ℕ × ℕ → Cmd) (R d : ℕ), Effective ltr prep ∧ Effective ltr restore ∧
    1 ≤ d ∧ (∀ k, Within R (prep k) ∧ Within R (restore k)) ∧ ∀ a W, Framing a W d (prep (a,W)) (restore (a,W)) := by
  obtain ⟨header,N,d,eh,hd,wh,hframe⟩ := FrameHeader.compiled
  obtain ⟨ca,hca⟩ := FrameCode.arrange_easy Flat
  obtain ⟨cb,hcb⟩ := FrameCode.arrange_easy Bank
  obtain ⟨sv,hsv⟩ := (show Easy save from Easy.snd.pair Easy.fst)
  obtain ⟨st,hst⟩ := (show Easy strip from (Easy.fst.compose Easy.snd).pair Easy.snd)
  obtain ⟨fn,hfn⟩ := (show Easy finish from (Easy.snd.compose Easy.snd).pair Easy.fst)
  obtain ⟨R,rpos,hr,wa,wb,ws,wt,wf,⟨sp,es,hsp⟩,me,em,hme⟩ := (show ∀ᶠ R : ℕ in atTop,
    0 < R ∧ N ≤ R ∧ Within R ca ∧ Within R cb ∧ Within R sv ∧ Within R st ∧ Within R fn ∧
    KernelEffectiveFamily.Family R (ChildLanes.split (A := Dusk.Pair)) ∧
    KernelEffectiveFamily.Family R (ChildLanes.merge (A := Dusk.Pair)) from by
    filter_upwards [eventually_ge_atTop 1,eventually_ge_atTop N,RegisterSelect.within_eventually ca,
      RegisterSelect.within_eventually cb,RegisterSelect.within_eventually sv,RegisterSelect.within_eventually st,
      RegisterSelect.within_eventually fn,Lanes.split_family (A := Dusk.Pair),Lanes.merge_family (A := Dusk.Pair)] with R h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
    exact ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉⟩).exists
  let prep (k : ℕ × ℕ) := FrameCode.make (header k) ca (sp k.2) sv
  let restore (k : ℕ × ℕ) := st.join (FrameCode.make (header k) cb (me k.2) fn)
  refine ⟨prep,restore,R,d,FrameCode.effective ca sv eh (es.comp Computable.snd),
    (effective_const ltr st).join (FrameCode.effective cb fn eh (em.comp Computable.snd)),hd,?_,?_⟩
  · intro k
    have wh' := RegisterSelect.within_mono hr _ (wh k)
    exact ⟨FrameCode.within rpos wh' wa (hsp k.2).1 ws,wt,FrameCode.within rpos wh' wb (hme k.2).1 wf⟩
  intro a W hW I s positive divides V layout
  let wire := Header.wire (a+1) ∘ s
  let key (i : I) : FrameCode.Saved := (PhysicalWalshGrid.header (coords a W) Shape.w (s i),wire i)
  let cuts := FrameHeader.rulers a W ∘ s
  obtain ⟨C,h⟩ := hframe a W
  have bound : Small V (fun i => send (cuts i,key i)) := ⟨C,fun i => (h (s i) (positive i)).2⟩
  have generate : Scan (header (a,W)) V (send ∘ wire) (fun i => send (cuts i,key i)) :=
    ⟨bound.right.right, C,fun i => (h (s i) (positive i)).1⟩
  constructor
  · intro x
    let row (i : I) := flat (a+1) (s i) (x i)
    have small : Small V (send ∘ row) := ⟨8,fun i => FrameValues.flat_size _ _ _ _⟩
    have run := (FrameCode.scan generate hca (hsp W).2 hsv small).closed
    change ClosedRuns _ _ _ _ (fun i => send (key i,FrameValues.bank a W (s i) (lane (a+1) W (s i) (x i))))
    simpa only [prep,buffer,wire,save,cuts,row,Function.comp_def,FrameValues.split_eq a W _ (positive _) (divides _)] using run
  · intro y
    let bank (i : I) := FrameValues.bank a W (s i) (y i)
    have small : Small V (send ∘ bank) := ⟨10,fun i => FrameValues.bank_size _ _ _ _ (positive i) (divides i) _⟩
    have pre := Scan.linear hst (fun i => (key i,bank i)) (bound.right.fork small)
    have run := (pre.seq (FrameCode.scan generate hcb (hme W).2 hfn small)).closed
    change ClosedRuns _ _ _ (fun i => send (key i,bank i)) (fun i => send (wire i,flat (a+1) (s i) (unlane (a+1) hW (s i) (y i))))
    simpa only [restore,wire,finish,cuts,key,bank,Function.comp_def,FrameValues.merge_eq a W hW _ (positive _) (divides _)] using run

end PhysicalWalshCompile

end NearSquareRoot
end Computability
end OAI
