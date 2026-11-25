import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.Recovery.MinorInline
import OAI.Optimization.LinearProgramming.Geometry.LabelMarked
import OAI.Optimization.LinearProgramming.Geometry.BorderServiceRuns
import OAI.Optimization.LinearProgramming.Recovery.PriceEnvironment

/-! A complete price request, including every physical adaptive minor call and the
first restart, executed as an ordinary RAM fragment. Only the minor service ROM and
the geometric instruction stream occur in its code. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace OracleInline

open RAM RAM.Callable Contract OracleSpec
open _root_.OAI.Optimization.LinearProgramming.Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.OracleSegments
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Geometry.MinorInstall

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

def geometricCall (p : Program) : Fragment :=
  fragment (geometricLabelProcedure.emit 0 ++ [.core (.halt 0)]) (minorHandler p)

/-- An additive allowance per actual price request, independent of the incoming
memory width. The price and input-basis bounds are computed from their own data. -/
def geometricIncrement (r s n e g : ℕ) : ℕ := geometricLabelWidth r n e g 0+(r+s+n+4)

def geometricCallTime (r s n nativeClock : ℕ) : ℕ :=
  LabelRAM.time r n (batchTime r n) * max 4 (serviceClock r s n nativeClock)

theorem geometricWidth_le (r s n e g H : ℕ) :
    geometricLabelWidth r n e g H ≤ H+geometricIncrement r s n e g := by
  unfold geometricIncrement geometricLabelWidth LabelRAM.width
  omega

theorem cache_safe (S : Service D E) {old : History ℚ} {native : Memory ℚ} (live : cache S old native)
    (ready : RowRAM.Within S.height S.ready.memory) {W : ℕ} (width : S.height ≤ W) :
    native.AllData (fun z=>ratBits z ≤ W) := by
  obtain ⟨st,rfl,recorded⟩:=live
  exact fun a=>(recorded.height ready a).trans width

theorem geometricCall_run (S : Service D E) (q : PriceGame.Query n) (m : Memory ℚ)
    (old : History ℚ) (x : LabelInput.Buffers r s n) (hdr : LabelInput.Header x D E q.prices q.index m)
    (e H : ℕ) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n)
    (safe : RowRAM.Within H m) (mat : ∀ i j,ratBits (D i j) ≤ e)
    (prices : ∀ j,ratBits (q.prices j) ≤ e) (height : S.height ≤ H)
    (ready : RowRAM.Within S.height S.ready.memory) {native : Memory ℚ} (live : cache S old native) :
    let W:=H+geometricIncrement r s n e S.outputBits
    ∃ t final next,cache S final next ∧ (geometricCall S.program).Run (fun z=>ratBits z ≤ W)
      (Odd.memory native m) (geometricCallTime r s n S.clock) (Odd.memory next t) ∧
      (∀ a,64 ≤ a → a < x.layout.triples → t.data a=m.data a) ∧ LabelRAM.HeaderPreserved m t ∧
      (answersMatch S.oracle old → answersMatch S.oracle final) ∧ LabelRAM.Result (keyPacket D E) D q old t final := by
  let W:=H+geometricIncrement r s n e S.outputBits
  have bound:=geometricWidth_le r s n e S.outputBits H
  have serviceHeight : S.height ≤ W := height.trans (Nat.le_add_right _ _)
  have wordHeight : r+s+n+4 ≤ W := by dsimp [W,geometricIncrement]; omega
  obtain ⟨t,final,k,clock,marks,frame,hdr',ans⟩ :=
    geometricLabelProcedure_marked D E q S.oracle m old x hdr e S.outputBits H hD hrn safe mat prices S.responds
  have all : MarkedRuns (namedMinor D E) geometricLabelProcedure S.oracle (RowRAM.Within W) m old k t final :=
    marks.weaken (fun _ hs a=>(hs a).trans bound)
  have run:=all.halted 0
  obtain ⟨next,live',_,exec⟩:=minor_program_runs S W serviceHeight wordHeight ready _ (RowRAM.Within W)
    (fun _ h=>h) m native old (cache_safe S live ready serviceHeight) live run rfl
  refine ⟨t,final,next,live',?_,frame,hdr',answersMatch_run run.forget.plain,ans⟩
  exact exec.mono (Nat.mul_le_mul_right _ (by omega))

/-- Same call directly from the public relative layout. Header construction consists
only of true address operations and preserves every geometric scalar input. -/
def geometricCallFromInputs (p : Program) : Fragment :=
  .seq (Odd.leaf LabelInput.prepareHeader) (geometricCall p)

theorem geometricCallFromInputs_run (S : Service D E) (q : PriceGame.Query n) (m : Memory ℚ)
    (old : History ℚ) (x : LabelInput.Buffers r s n) (input : LabelInput.Inputs x D E q.prices q.index m)
    (e H : ℕ) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n) (safe : RowRAM.Within H m)
    (mat : ∀ i j,ratBits (D i j) ≤ e) (prices : ∀ j,ratBits (q.prices j) ≤ e) (height : S.height ≤ H)
    (ready : RowRAM.Within S.height S.ready.memory) {native : Memory ℚ} (live : cache S old native) :
    let W:=H+geometricIncrement r s n e S.outputBits
    ∃ t final next,cache S final next ∧ (geometricCallFromInputs S.program).Run (fun z=>ratBits z ≤ W)
      (Odd.memory native m) (4*(5000*(r+n+1)^3)+geometricCallTime r s n S.clock) (Odd.memory next t) ∧
      (∀ a,64 ≤ a → a < x.layout.triples → t.data a=m.data a) ∧ PriceLayout.Matrices x D E t ∧ (answersMatch S.oracle old → answersMatch S.oracle final) ∧
      LabelRAM.Result (keyPacket D E) D q old t final := by
  let W:=H+geometricIncrement r s n e S.outputBits
  have hW : H ≤ W := Nat.le_add_right _ _
  obtain ⟨u,c,hc,prep,hdr,ud,_⟩:=LabelInput.prepareHeader_spec (fun v=>ratBits v ≤ H) m safe x D E q.prices q.index input
  have width : RowRAM.Within H u := fun a=>by rw [ud]; exact safe a
  obtain ⟨t,final,next,kept,call,frame,stable,history,ans⟩:=geometricCall_run S q u old x hdr e H hD hrn width mat prices height ready live
  have setup:=Odd.leaf_run (fun v=>ratBits v ≤ W) native (cache_safe S live ready (height.trans hW))
    (PowerRAM.weaken prep (fun _ h a=>(h a).trans hW))
  have matrices := (PriceLayout.fromHeader hdr).retain stable (fun a ha hp=>frame a (by have := x.dualHigh; omega)
    (by change a < x.free; have := x.priceEnd; omega))
  refine ⟨t,final,next,kept,(setup.seq call).mono (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hc) _),?_,matrices,history,ans⟩
  intro a ha hb
  exact (frame a ha hb).trans (congrFun ud a)

end OracleInline
end Recovery
end LinearProgramming
end Optimization
end OAI
