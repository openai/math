import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareProgram
import OAI.Optimization.LinearProgramming.PriceGame.MarketInitializeBridge
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrepareTableSpec

/-! Agreement of bounded preparation with the encoded recursive trial. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open Trial Wire TrialExecution
open Market Market.InitializeMachine Market.FlowMachine

variable {m g : ℕ}

/-- The dense signed rational market and its weight vector in their runtime field order. -/
def packedRequest (I : Augment.Input m g) (L : Fin m → ℚ) : ClearingRequest :=
  (List.ofFn L, (typed I 1 L).2)

def packedClearing (I : Augment.Input m g) (L : Fin m → ℚ) : List ℚ × List ℚ :=
  let v := computeAtCommonWeightUnit I.positive L I.available I.intercept
  (List.ofFn v.1, packedCells v.2)

def frameMarket (x : PrepFrame) (g : ℕ) : Augment.Input x.1.2.2.length g :=
  ⟨fun e => (atD x.1.2.2 e.val).positive,
   fun e i => acceptsRaw x.2.1.level (atD x.1.2.2 e.val) i.val,
   fun e i => bidRaw x.1.1 x.2.1.level x.2.1.history (atD x.1.2.2 e.val) i.val⟩

def frameL (x : PrepFrame) (e : Fin x.1.2.2.length) : ℚ := prepLocalCell x e.val

theorem request_agrees (x : PrepFrame) (hw : x.1.1*2^x.2.1.level ≤ 2*(x.1.1*x.1.1)) :
    clearingRequest x = packedRequest (frameMarket x (x.1.1*2^x.2.1.level)) (frameL x) := by
  let g := x.1.1*2^x.2.1.level
  have hg : frameGoods x = List.range g := goods_eq_range _ _ hw
  change (prepLocalRow x, (frameGoods x).length+1, bidTables
    (x.1.2.2,x.1.1,x.2.1.level,x.2.1.history,frameGoods x)) = _
  rw [hg,List.length_range]
  apply Prod.ext
  · exact PrepareTable.map_range x.1.2.2.length (prepLocalCell x)
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact PrepareTable.map_roster x.1.2.2 PackedExpert.positive
      · apply Prod.ext
        · exact PrepareTable.roster_cells x.1.2.2 g
            (fun e o => o.elim true (fun i => acceptsRaw x.2.1.level e i.val))
            (fun _ => true) (acceptsRaw x.2.1.level) (fun _ => rfl) (fun _ _ => rfl)
        · exact PrepareTable.roster_cells x.1.2.2 g
            (Market.bid (fun e (i : Fin g) => bidRaw x.1.1 x.2.1.level x.2.1.history e i.val))
            (fun _ => 0) (bidRaw x.1.1 x.2.1.level x.2.1.history)
            (fun _ => rfl) (fun _ _ => rfl)

theorem recoverRows_agrees (f : Fin m → Option (Fin g) → ℚ) :
    recoverRows (m,List.range g,packedCells f) = List.ofFn (fun e => List.ofFn fun i => f e (some i)) := by
  change (List.range m).map (fun e => (List.range g).map (fun i =>
    atD (packedCells f) (e*((List.range g).length+1)+(i+1)))) = _
  rw [List.length_range]
  exact PrepareTable.real_cells f

/-- The two size conditions are the actual input-width and child-score invariants.
The clearing premise is the compiler's semantic contract on each dense market. -/
theorem prepareUsing_agrees {clearer : ClearingRequest → List ℚ × List ℚ}
    (hc : ∀ {a b : ℕ} (I : Augment.Input a b) (L : Fin a → ℚ),
      clearer (packedRequest I L) = packedClearing I L)
    (x : PrepFrame) (hw : x.1.1*2^x.2.1.level ≤ 2*(x.1.1*x.1.1))
    (hs : ∀ i < x.1.2.2.length, scoreTotal x.2.2 i ≤ scoreBudget x.1.1) :
    prepareUsing clearer x = preparePacketSized x.1.1 x.1.2.1 x.1.2.2.length x.1.2.2 x.2.1 x.2.2 := by
  let g := x.1.1*2^x.2.1.level
  have hg : frameGoods x = List.range g := goods_eq_range _ _ hw
  by_cases hp : x.2.2.length < x.1.2.1
  · simp only [prepareUsing,preparePacketSized,hp,ite_true,prepDeepRow_eq x hs,request_agrees x hw,
       hc,packedClearing,hg,recoverRows_agrees]
    rfl
  · simp only [prepareUsing,preparePacketSized,hp,ite_false,prepDeepRow_eq x hs,hg]
    rw [prefixMedians_eq _ _ _ (Nat.le_of_not_gt hp)]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
