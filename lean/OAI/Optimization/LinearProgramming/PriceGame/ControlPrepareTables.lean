import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareBids
import OAI.Optimization.LinearProgramming.PriceGame.MarketInitializeMachine
import OAI.Optimization.LinearProgramming.PriceGame.ChargingColdRanges
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepWire

/-! Bounded generation of the actual expert-by-option bid and acceptance tables. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire
open Market.InitializeMachine
open Learning.GenerationCost Market.GridMachine

abbrev goodsInputCode := prodCode unaryCode Nat.bits

def goods (N k : ℕ) : List ℕ :=
  (List.range (Cold.addressBound N)).filter (fun i => decide (i >>> k < N))

theorem goods_eq_range (N k : ℕ) (h : N*2^k ≤ 2*(N*N)) :
    goods N k = List.range (N*2^k) := by
  unfold goods
  simp only [Nat.shiftRight_eq_div_pow,Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
  rw [Cold.filter_range_lt, Cold.addressBound, Nat.min_eq_right h]

noncomputable def goodsP : Procedure goodsInputCode nlist (fun p => goods p.1 p.2) := by
  let N := first unaryCode Nat.bits
  let k := second unaryCode Nat.bits
  let nn := unaryMul.comp (N.pair N)
  let cap := unaryMul.comp ((constant goodsInputCode unaryCode 2).pair nn)
  let env := prodCode Nat.bits Nat.bits
  let data := first env Nat.bits
  let n := (first Nat.bits Nat.bits).comp data
  let l := (second Nat.bits Nat.bits).comp data
  let j := second env Nat.bits
  let valid := binaryLt.comp ((Learning.BitMachine.rootAddressP.comp (j.pair l)).pair n)
  let filter := Learning.BitMachine.filterWithP 0 valid
  exact filter.comp ((addressRangeP.comp cap).pair ((unaryToBits.comp N).pair k))

/-- Runtime bid data: binary dimension, level, ancestral prices and actual real-good addresses. -/
abbrev BidTableContext := ℕ × ℕ × List (List ℚ) × List ℕ
abbrev tableContextCode : BidTableContext → List Bool := prodCode Nat.bits (prodCode Nat.bits
  (prodCode marketHistoryCode nlist))
abbrev oneBidsCode := prodCode tableContextCode packedExpertCode

private noncomputable abbrev tabCtxP := first tableContextCode packedExpertCode
private noncomputable abbrev tabEP := second tableContextCode packedExpertCode
private noncomputable abbrev tabNP := (first Nat.bits (prodCode Nat.bits
  (prodCode marketHistoryCode nlist))).comp tabCtxP
private noncomputable abbrev tabTailP := (second Nat.bits (prodCode Nat.bits
  (prodCode marketHistoryCode nlist))).comp tabCtxP
private noncomputable abbrev tabLP := (first Nat.bits (prodCode marketHistoryCode nlist)).comp tabTailP
private noncomputable abbrev tabOtherP := (second Nat.bits (prodCode marketHistoryCode nlist)).comp tabTailP
private noncomputable abbrev tabHP := (first marketHistoryCode nlist).comp tabOtherP
private noncomputable abbrev tabGoodsP := (second marketHistoryCode nlist).comp tabOtherP

def availabilityRow (x : BidTableContext × PackedExpert) : List Bool :=
  true :: x.1.2.2.2.map (acceptsRaw x.1.2.1 x.2)

def bidRow (x : BidTableContext × PackedExpert) : List ℚ :=
  0 :: x.1.2.2.2.map (bidRaw x.1.1 x.1.2.1 x.1.2.2.1 x.2)

noncomputable def availabilityRowP : Procedure oneBidsCode blist availabilityRow := by
  let row := first oneBidsCode Nat.bits
  let i := second oneBidsCode Nat.bits
  let cell := acceptsRawP.comp ((tabLP.comp row).pair ((tabEP.comp row).pair i))
  let real := (mapWithContext 0 false cell).comp (tabGoodsP.pair (identity oneBidsCode))
  exact (listCons boolCode).comp ((constant oneBidsCode boolCode true).pair real)

noncomputable def bidRowP : Procedure oneBidsCode qlist bidRow := by
  let row := first oneBidsCode Nat.bits
  let i := second oneBidsCode Nat.bits
  let ctx := tabNP.pair (tabHP.pair tabEP)
  let cell := bidRawP.comp (((tabLP.comp row).pair i).pair (ctx.comp row))
  let real := (mapWithContext 0 (0:ℚ) cell).comp (tabGoodsP.pair (identity oneBidsCode))
  exact (listCons ratCode).comp ((constant oneBidsCode ratCode (0:ℚ)).pair real)

def bidTables (z : List PackedExpert × BidTableContext) : RationalStatic :=
  (z.1.map PackedExpert.positive, (z.1.map (fun e => availabilityRow (z.2,e))).flatten,
    (z.1.map (fun e => bidRow (z.2,e))).flatten)

noncomputable def bidTablesP : Procedure (prodCode (listCode packedExpertCode) tableContextCode)
    rationalStaticCode bidTables := by
  let signs := (listMap default false Learning.BitMachine.expertPositiveP).comp
    (first (listCode packedExpertCode) tableContextCode)
  let flags := (flattenP boolCode false).comp (mapWithContext default [] availabilityRowP)
  let bids := (flattenP ratCode (0:ℚ)).comp (mapWithContext default [] bidRowP)
  exact signs.pair (flags.pair bids)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
