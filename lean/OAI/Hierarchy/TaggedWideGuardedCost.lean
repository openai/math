import OAI.Hierarchy.TaggedWideGuardedBoard
import OAI.Hierarchy.TaggedWidePortBill

namespace OAI
/-! # Exact sharing of clock storage across both physical native verifiers -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing TaggedPrune
open scoped Classical BigOperators

theorem Gate.pin_card (A : Gate) : Fintype.card A.Pin=Fintype.card A.Head+Fintype.card A.Hidden := by
  simp only [Pin,Head,Hidden,TaggedShorterControlHistory.Pin,TaggedShorterChronoArray.Input,
    TaggedShorterClock.Pin,TaggedShorterChronoRow.In,Seen,Fintype.card_sum]
  omega

variable {F : Type*} [Field F] {n k h w M : ℕ} {D : Type} [Fintype D]
variable (r : NativeRouting F k h w M) (A B : Gate)
local notation "E" => OpenPins h w r.catalyst
local notation "Q" => Fin r.selectors
local notation "V" => SitePins E Q D B

/-- This is the literal right-hand side for the static board of
`guarded_board`. Each verifier's memory-trace and guessed output bits
are included in its CPU charge. The independent control socket legs,
shared physical data, and honest raw selector tape are counted separately. -/
theorem guarded_cost (b : Fin n → CutFormat F V) (cap : Fin n→ℕ)
    (head₀ : A.Head → (E⊕Q)⊕Bool) (head₁ : B.Head → (E⊕Q)⊕Bool)
    (flag : Fin A.u) (site : BitNetwork F (Fintype.card V))
    (board : StaticBoard F k h w M (fun i=>(b i).bank (cap i)) (WideHost.dualControlSizes h A.m B.m))
    (cost : let t := WideHost.dualControlSizes h A.m B.m
      let p := localPart A B head₀ head₁ flag site
      board.cost ≤ p.cells+p.internal+((∑i,(b i).cost)+∑ j,28*pins (t j) (t j))+
        (r.selectors+Fintype.card (Shared D A B))+(Fintype.card E+
        ((∑i,((b i).modules*2)*pins (b i).height (b i).width)+∑j,pins (t j) (t j)))) :
    board.cost ≤ ((A.hardware (F:=F)).cells+(A.hardware (F:=F)).internal+Fintype.card A.Pin)+
      ((B.hardware (F:=F)).cells+(B.hardware (F:=F)).internal+Fintype.card B.Pin)+
      (A.W+1)+(site.cells+site.internal)+(∑i,(b i).cost)+
      29*(pins h h+28*pins A.m A.m+28*pins B.m B.m)+
      (r.selectors+Fintype.card D)+Fintype.card E+(∑i,((b i).modules*2)*pins (b i).height (b i).width) := by
  dsimp only at cost
  rw [localPart_fee] at cost
  have sharing : Fintype.card (Shared D A B) =
      Fintype.card D + (Fintype.card A.Hidden + Fintype.card B.Hidden) := by
    simp only [Shared, Fintype.card_sum]
  have controls := control_socket_fee h A B
  dsimp only at controls
  have leftPins := A.pin_card
  have rightPins := B.pin_card
  omega

end Hierarchy.Tagged.WideControlJoin

end
end OAI
