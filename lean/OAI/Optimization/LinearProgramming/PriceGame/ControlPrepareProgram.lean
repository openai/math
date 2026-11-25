import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareTables
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareFrame
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareReadout

/-! A single finite binary-stack program connects both numerical branches of
the recursive trial's prepare operation to a word-level market clearer. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire Market.InitializeMachine

abbrev ClearingRequest := List ℚ × (ℕ × RationalStatic)
abbrev clearingCode := prodCode qlist (prodCode unaryCode rationalStaticCode)
abbrev clearingResultCode := prodCode qlist qlist

def frameGoods (x : PrepFrame) : List ℕ := goods x.1.1 x.2.1.level
noncomputable def frameGoodsP : Procedure prepFrameCode nlist frameGoods :=
  goodsP.comp (prepNP.pair prepLevelP)

def clearingRequest (x : PrepFrame) : ClearingRequest :=
  let gs := frameGoods x
  (prepLocalRow x, gs.length+1, bidTables (x.1.2.2,x.1.1,x.2.1.level,x.2.1.history,gs))

noncomputable def clearingRequestP : Procedure prepFrameCode clearingCode clearingRequest := by
  let gs := frameGoodsP
  let ctx := (unaryToBits.comp prepNP).pair (prepLevelP.pair (prepHistoryP.pair gs))
  let table := bidTablesP.comp (prepRosterP.pair ctx)
  let count := unarySuccessor.comp ((rowSizeP Nat.bits 0).comp gs)
  exact prepLocalRowP.pair (count.pair table)

def prepareUsing (clearer : ClearingRequest → List ℚ × List ℚ) (x : PrepFrame) : Prepared :=
  let gs := frameGoods x
  let ds := prepDeepRow x
  if x.2.2.length < x.1.2.1 then
    let out := clearer (clearingRequest x)
    ⟨true,out.1,recoverRows (x.1.2.2.length,gs,out.2),ds⟩
  else ⟨false,prefixMedians (gs,x.1.2.1,x.2.2),[],ds⟩

private noncomputable def packetP {A : Type} {ea : A → List Bool} (tag : Bool)
    {price : A → List ℚ} {alloc : A → List (List ℚ)} {deep : A → List ℚ}
    (pr : Procedure ea qlist price) (al : Procedure ea (listCode qlist) alloc)
    (dp : Procedure ea qlist deep) : Procedure ea preparedCode
      (fun x => (⟨tag,price x,alloc x,deep x⟩ : Prepared)) :=
  ((constant ea boolCode tag).pair (pr.pair (al.pair dp))).result (by intro; rfl)

/-- The market parameter supplies its binary program and polynomial runtime proof. -/
noncomputable def prepareUsingP {clearer : ClearingRequest → List ℚ × List ℚ}
    (clearP : Procedure clearingCode clearingResultCode clearer) :
    Procedure prepFrameCode preparedCode (prepareUsing clearer) := by
  let phase := binaryLt.comp (((listLength completedCode default).comp prepCallsP).pair prepRP)
  let result := clearP.comp clearingRequestP
  let prices := (first qlist qlist).comp result
  let flat := (second qlist qlist).comp result
  let alloc := recoverRowsP.comp (prepCountP.pair (frameGoodsP.pair flat))
  let probe := packetP true prices alloc prepDeepRowP
  let med := prefixMediansP.comp (frameGoodsP.pair (prepRP.pair prepCallsP))
  let finalPacket := packetP false med (constant prepFrameCode (listCode qlist) []) prepDeepRowP
  exact (conditional phase probe finalPacket).congrFun (by
    intro p
    simp [prepareUsing, Function.comp_def])

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
