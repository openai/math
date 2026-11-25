import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialFinishMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedbackRefines

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open Trial Wire TrialExecution

private theorem mapRange {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem <;> simp

private theorem packetGains_eq {N l : ℕ} (experts : List PackedExpert) (p : Prepared) (bits : List Bool)
    (width : p.baseline.length = N*2^l) :
    packetGains (experts,p,bits) = if p.isProbe then List.ofFn (fun e : Fin experts.length =>
      ∑ i : Fin (N*2^l), atD (atD p.allocation e.val) i.val * labelSign (atD experts e.val).positive * labelSign (atD bits i.val))
    else List.replicate experts.length 0 := by
  rw [packetGains,mapRange]
  cases flag : p.isProbe
  · simp [expertGain,flag]
  · simp only [ite_true]
    apply congrArg List.ofFn
    funext e
    simp only [expertGain,flag,ite_true,rowGain,width,mapRange,List.sum_ofFn,gainCell]

theorem boundedChildReturn_eq {N l : ℕ} (i : NodeInput) (hi : i.level = l) (experts : List PackedExpert)
    (p : Prepared) (o : PackedRound) (bits : List Bool) (y : Prices N l) (x : Prices N (l+1))
    (hp : p.baseline = packTable N l y) (ho : o.prices = packTable N (l+1) x) :
    boundedChildReturn experts p o bits = finishPacketSized N experts.length experts i p o bits := by
  subst l
  have hy : lookupTable N i.level (packTable N i.level y) = y := funext (fun _ => lookupTable_pack ..)
  have hx : lookupTable N (i.level+1) (packTable N (i.level+1) x) = x := funext (fun _ => lookupTable_pack ..)
  have width : p.baseline.length = N*2^i.level := by rw [hp,length_packTable]
  apply Completed.mk.injEq .. |>.mpr
  refine ⟨rfl,?_,?_,rfl⟩
  · change medianRow p.baseline o.prices = mapped N i p o
    simp only [mapped,hp,ho,medianRow_pack,hy,hx]
  · exact packetGains_eq experts p bits width

theorem boundedTrialFinish_eq {N l ne : ℕ} (R : ℕ) (h : History N) (w : Weights ne)
    (experts : List PackedExpert) (xs : List Completed) (prep : Prepared) (child : PackedRound) (tape : List Bool)
    (y : Prices N l) (x : Prices N (l+1)) (hp : prep.baseline = packTable N l y)
    (hc : child.prices = packTable N (l+1) x) :
    boundedTrialFinish (N,R,experts) (codeInput l h w) xs prep child tape =
      completeSized feedbackPrefix N experts.length experts (codeInput l h w) xs prep child tape := by
  have ret := boundedChildReturn_eq (N:=N) (l:=l) (codeInput l h w) rfl experts prep child
  have sizeEq : boundedChildReturn experts prep child =
      finishPacketSized N experts.length experts (codeInput l h w) prep child := by
    funext bits
    exact ret bits y x hp hc
  have fb := boundedFeedback_refines h y x tape
  rw [← hp,← hc] at fb
  simp only [boundedTrialFinish,completeSized,codeInput,sizeEq,fb]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
