import OAI.Hierarchy.TaggedWideGuardedCost
import OAI.Hierarchy.TaggedWidePhysicalBill

namespace OAI
/-! # The component charges read directly from the guarded native board -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing TaggedPrune
open scoped Classical BigOperators

variable {F : Type*} [Field F] {n k h w M : ℕ} {D : Type} [Fintype D]
variable (r : NativeRouting F k h w M) (A B : Gate)
local notation "E" => OpenPins h w r.catalyst
local notation "Q" => Fin r.selectors
local notation "V" => SitePins E Q D B

def nativeCharges (b : Fin n→CutFormat F V) (site : BitNetwork F (Fintype.card V)) :
    WidePhysicalBill.Charges n where
  rows := fun side=>if side then B.S+(B.f+B.u) else A.S+(A.f+A.u)
  cpu := fun side=>if side then
    (B.hardware (F:=F)).cells+(B.hardware (F:=F)).internal+Fintype.card B.Pin else
    (A.hardware (F:=F)).cells+(A.hardware (F:=F)).internal+Fintype.card A.Pin
  flagWord := A.W+1
  site := site.cells+site.internal
  selectors := r.selectors
  workspace := Fintype.card D
  external := Fintype.card E
  cuts := fun i=>(b i).cost
  sockets := fun i=>((b i).modules*2)*pins (b i).height (b i).width

/-- The boards produced by the physical guarded constructor have precisely
the component upper bound consumed by the uniform width estimate. -/
theorem guarded_native_bill (b : Fin n→CutFormat F V) (cap : Fin n→ℕ)
    (head₀ : A.Head→(E⊕Q)⊕Bool) (head₁ : B.Head→(E⊕Q)⊕Bool)
    (flag : Fin A.u) (site : BitNetwork F (Fintype.card V))
    (board : StaticBoard F k h w M (fun i=>(b i).bank (cap i)) (WideHost.dualControlSizes h A.m B.m))
    (m₀ : A.m=controlHeight h (A.S+(A.f+A.u))) (m₁ : B.m=controlHeight h (B.S+(B.f+B.u)))
    (cost : let t := WideHost.dualControlSizes h A.m B.m
      let p := localPart A B head₀ head₁ flag site
      board.cost≤p.cells+p.internal+((∑i,(b i).cost)+∑ j,28*pins (t j) (t j))+
        (r.selectors+Fintype.card (Shared D A B))+(Fintype.card E+
        ((∑i,((b i).modules*2)*pins (b i).height (b i).width)+∑j,pins (t j) (t j)))) :
    board.cost≤(nativeCharges r A B b site).total h := by
  simpa only [nativeCharges,WidePhysicalBill.Charges.total,Bool.false_eq_true,ite_false,ite_true,←m₀,←m₁]
    using guarded_cost r A B b cap head₀ head₁ flag site board cost

end Hierarchy.Tagged.WideControlJoin

end
end OAI
