import OAI.Optimization.LinearProgramming.Recovery.GeometricCall
import OAI.Optimization.LinearProgramming.Recovery.PriceReturn
import OAI.Optimization.LinearProgramming.RAM.SafeRun
import OAI.Optimization.LinearProgramming.Geometry.VMPacketCopy

/-! The native callback for one canonical learner packet, from its scalar bits to
its literal Boolean or restart at the actual physical boundary. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG

open RAM RAM.Callable Contract OracleSpec BitRAM Geometry
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

def numericPrice (p : Program) : Fragment :=
  .seq (Odd.leaf PriceLayout.parseAndPrepare) (geometricCallFromInputs p)

def numericPriceTime (r s n serviceCost length : ℕ) : ℕ :=
  4*(NativePrice.packetTime n length+11)+(4*(5000*(r+n+1)^3)+geometricCallTime r s n serviceCost)

/-- This is a finite ordinary instruction stream once the fixed minor ROM is supplied. -/
def priceHandler (p : Program) : Fragment :=
  .seq VMPacketCopy.fragment (.seq (numericCall (numericPrice p)) publish)

def priceHandlerTime (r s n serviceCost len : ℕ) : ℕ :=
  (20*len+14)+(2*(numericPriceTime r s n serviceCost len+1)+2+18)

theorem numericPrice_run (S : Service D E) (x : LabelInput.Buffers r s n) (q : PriceGame.Query n)
    (old : History ℚ) (g minor : Memory ℚ) (environment : PriceLayout.Matrices x D E g)
    (word : ScalarPacket g 256 (priceQuery q.index q.prices)) (len : g.index 37=(priceQuery q.index q.prices).length)
    (base : g.index 43=256) (room : 256+(priceQuery q.index q.prices).length ≤ x.dual)
    (H e : ℕ) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n) (safe : RowRAM.Within H g)
    (argument : (priceQuery q.index q.prices).length+3 ≤ H) (encoded : (priceQuery q.index q.prices).length+3 ≤ e)
    (matrix : ∀ i j,ratBits (D i j) ≤ e) (height : S.height ≤ H)
    (ready : RowRAM.Within S.height S.ready.memory) (live : cache S old minor) :
    let W:=H+geometricIncrement r s n e S.outputBits
    ∃ t final next,cache S final next ∧ PriceLayout.Matrices x D E t ∧
      (numericPrice S.program).Run (fun z=>ratBits z ≤ W) (Odd.memory minor g)
        (numericPriceTime r s n S.clock (priceQuery q.index q.prices).length) (Odd.memory next t) ∧
      (answersMatch S.oracle old → answersMatch S.oracle final) ∧ LabelRAM.Result (keyPacket D E) D q old t final := by
  let W:=H+geometricIncrement r s n e S.outputBits
  have hW : H ≤ W:=Nat.le_add_right _ _
  have good:=NativePrice.values_packet q.index q.prices H argument
  obtain ⟨u,k,hk,parsed,inputs⟩:=PriceLayout.parseAndPrepare_run (fun z=>ratBits z ≤ H) x D E q.index q.prices
    g environment safe word len base room good
  have prices : ∀j,ratBits (q.prices j) ≤ e := by
    intro j
    simpa using (NativePrice.values_packet q.index q.prices e encoded).price j
  have typed : LabelInput.Inputs x D E q.prices q.index u := by simpa using inputs
  obtain ⟨t,final,next,kept,computed,_,matrices,legal,result⟩:=geometricCallFromInputs_run S q u old x typed
    e H hD hrn parsed.safe_end matrix prices height ready live
  have pre:=Odd.leaf_run (fun z=>ratBits z ≤ W) minor (cache_safe S live ready (height.trans hW))
    (parsed.weaken (fun _ hs j=>(hs j).trans hW))
  exact ⟨t,final,next,kept,matrices,(pre.seq computed).mono (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hk) _),legal,result⟩

/-- The caller frame after crossing the input packet and returning the actual price
label. All its original heap/address values beyond the small scratch prefix are kept
except for the three explicitly installed receive/status headers. -/
inductive Returned (vm geom : Memory ℚ) : Memory ℚ→Prop where
  | answer (temp : Memory ℚ) (indices : ∀j,5 ≤ j → temp.index j=vm.index j)
      (flag : geom.index 139=0) : Returned vm geom (answerMemory (temp.putIndex 1 0) (geom.data 19))
  | restart (temp : Memory ℚ) (indices : ∀j,5 ≤ j → temp.index j=vm.index j)
      (flag : geom.index 139=1) : Returned vm geom (restartMemory (temp.putIndex 1 0))

private theorem copied_scalars {K : Type} [Zero K] [One K] {P : K→Prop} {w : Word} {g v g' v' : Memory K}
    (out : VMPacketCopy.Output w g v g' v') (old : g.AllData P) (zero : P 0) (one : P 1) : g'.AllData P := by
  intro j
  by_cases inside : 256 ≤ j ∧ j < 256+w.length
  · let k:=j-256
    have hk : k < w.length := by dsimp [k]; omega
    have addr : 256+k=j := by dsimp [k]; omega
    have bit:=out.packet k hk
    rw [addr] at bit
    rw [bit]
    cases w[k] <;> assumption
  · rw [out.geomData j (by omega)]
    exact old j

theorem priceHandler_run (S : Service D E) (x : LabelInput.Buffers r s n) (q : PriceGame.Query n)
    (old : History ℚ) (minor geom vm : Memory ℚ) (environment : PriceLayout.Matrices x D E geom)
    (word : ScalarPacket vm (vm.index 43) (priceQuery q.index q.prices))
    (len : vm.index 37=(priceQuery q.index q.prices).length) (base : 3 ≤ vm.index 43)
    (room : 256+(priceQuery q.index q.prices).length ≤ x.dual)
    (H e W : ℕ) (hD : LinearIndependent ℚ D.row) (hrn : r ≤ n) (geomSafe : RowRAM.Within H geom)
    (vmSafe : RowRAM.Within W vm) (envelope : H+geometricIncrement r s n e S.outputBits ≤ W)
    (arg : (priceQuery q.index q.prices).length+3 ≤ H)
    (encoded : (priceQuery q.index q.prices).length+3 ≤ e) (matrix : ∀ i j,ratBits (D i j) ≤ e)
    (height : S.height ≤ H) (ready : RowRAM.Within S.height S.ready.memory) (live : cache S old minor) :
    ∃ t final next v,cache S final next ∧ PriceLayout.Matrices x D E t ∧
      RowRAM.Within (H+geometricIncrement r s n e S.outputBits) t ∧
      (priceHandler S.program).Run (fun z=>ratBits z ≤ W) (Odd.memory (Odd.memory minor geom) vm)
        (priceHandlerTime r s n S.clock (priceQuery q.index q.prices).length) (Odd.memory (Odd.memory next t) v) ∧
      Returned vm t v ∧ (answersMatch S.oracle old → answersMatch S.oracle final) ∧
      LabelRAM.Result (keyPacket D E) D q old t final := by
  let localWidth:=H+geometricIncrement r s n e S.outputBits
  have hW : H ≤ W:=(Nat.le_add_right H _).trans envelope
  obtain ⟨g,u,copy,out,_,us⟩:=VMPacketCopy.fragment_spec (fun z=>ratBits z ≤ W) minor geom vm
    (priceQuery q.index q.prices) (cache_safe S live ready (height.trans hW)) (fun j=>(geomSafe j).trans hW) vmSafe len base word
  have small:=NativePrice.values_packet q.index q.prices H arg
  have gs:=copied_scalars (P := fun z : ℚ => ratBits z ≤ H) out geomSafe (by simpa using small.counter 0 (by omega)) (by simpa using small.counter 1 (by omega))
  have mat:=environment.retain (fun j hj _ _ _ _=>out.geomIndex j (by omega) (by omega))
    (fun j hj _=>out.geomData j (Or.inr (room.trans hj)))
  obtain ⟨t,final,next,kept,matrices,numeric,legal,result⟩:=numericPrice_run S x q old g minor mat
    out.packet out.length out.base room H e hD hrn gs arg encoded matrix height ready live
  have inlined:=numericCall_run (numeric.weakenData (fun _ hs=>hs.trans envelope)) u us
  have nextSafe : next.AllData (fun z=>ratBits z ≤ localWidth) := fun j=>by
    simpa only [Odd.data_even] using numeric.safe_end (2*j)
  have tSafe : t.AllData (fun z=>ratBits z ≤ localWidth) := fun j=>by
    simpa only [Odd.data_slot] using numeric.safe_end (Odd.slot j)
  have nextMax : next.AllData (fun z=>ratBits z ≤ W) := fun j=>(nextSafe j).trans envelope
  have tMax : t.AllData (fun z=>ratBits z ≤ W) := fun j=>(tSafe j).trans envelope
  have flag : t.index 139=0 ∨ t.index 139=1 := by cases result <;> tauto
  rcases flag with ok|restart
  · have resp:=publish_answer next t (u.putIndex 1 0) nextMax tMax us ok
    exact ⟨t,final,next,_,kept,matrices,tSafe,copy.seq (inlined.seq resp),.answer u out.vmIndex ok,legal,result⟩
  · have resp:=publish_restart next t (u.putIndex 1 0) nextMax tMax us restart
    exact ⟨t,final,next,_,kept,matrices,tSafe,copy.seq (inlined.seq (resp.mono (by decide : 10 ≤ 18))),
      .restart u out.vmIndex restart,legal,result⟩

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
