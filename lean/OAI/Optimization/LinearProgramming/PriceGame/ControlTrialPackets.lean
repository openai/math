import OAI.Optimization.LinearProgramming.PriceGame.ControlData
import OAI.Optimization.LinearProgramming.PriceGame.TrialExecution

/-! Concrete numeric phase operations for the resumable trial machine. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass Moment TrialExecution

structure NodeInput where
  level : ℕ
  history : List (List ℚ)
  weights : List ℚ
deriving DecidableEq, Repr, Inhabited

structure Prepared where
  isProbe : Bool
  baseline : List ℚ
  allocation : List (List ℚ)
  deepWeights : List ℚ
deriving DecidableEq, Repr, Inhabited

structure Completed where
  baseline : List ℚ
  mapped : List ℚ
  gains : List ℚ
  child : PackedRound
deriving DecidableEq, Repr, Inhabited

def atD {α : Type*} [Inhabited α] (xs : List α) (i : ℕ) : α := xs[i]?.getD default

@[simp] theorem atD_ofFn {α : Type*} [Inhabited α] {n : ℕ} (f : Fin n → α) (i : Fin n) :
    atD (List.ofFn f) i.val = f i := by simp [atD,i.isLt]

def codeInput {N ne : ℕ} (l : ℕ) (history : History N) (weights : Weights ne) : NodeInput :=
  ⟨l, packHistory l history, List.ofFn weights⟩

def codeOutput {N ne r l : ℕ} (out : Output N ne r l) : PackedRound :=
  ⟨packTable N l out.prices, out.scores.toList, out.log.map packProbe⟩

def codeCall {N ne r l : ℕ} (c : Call N ne r l) : Completed :=
  ⟨packTable N l c.data.baseline, packTable N l c.data.mapped, c.data.gain.toList, codeOutput c.child⟩

def codeProbe {N ne l : ℕ} {experts : Fin ne → Expert N} {history : History N}
    {L : Weights ne} (answer : MarketAnswer experts l history L) (dw : Weights ne) : Prepared :=
  ⟨true, packTable N l answer.prices,
    List.ofFn (fun e : Fin ne => packTable N l (fun i => answer.fractions e (some i))), List.ofFn dw⟩

def codeFinal {N ne l : ℕ} (y : Prices N l) (dw : Weights ne) : Prepared :=
  ⟨false, packTable N l y, [], List.ofFn dw⟩

def leafPacket (N R ne : ℕ) (input : NodeInput) : PackedRound :=
  ⟨packTable N input.level (fun i => if weight N input.level true i ≤ 1 then (R:ℚ)+1 else -((R:ℚ)+1)),
    List.replicate ne 0, []⟩

theorem leafPacket_spec {N ne : ℕ} (r R l : ℕ) (history : History N) (w : Weights ne) :
    leafPacket N R ne (codeInput l history w) = codeOutput (leafOutput (N:=N) r R l w).val := by
  rfl

/-- Decode a raw address only for inspecting its original coordinate. -/
def origin (N l i : ℕ) : ℕ :=
  if hi : i < N*2^l then (rootVertex N l ((vertexEquivFin N l).symm ⟨i,hi⟩)).val else 0

def shiftRaw (N : ℕ) (H : List (List ℚ)) (e : PackedExpert) : ℚ :=
  match e.pivot with
  | none => 0
  | some (l,j) => atD e.raw (origin N l j) - States.signed e.positive (atD (atD H l) j)

def acceptsRaw (l : ℕ) (e : PackedExpert) (j : ℕ) : Bool := e.level == l && e.tuple.contains j

def bidRaw (N l : ℕ) (H : List (List ℚ)) (e : PackedExpert) (j : ℕ) : ℚ :=
  atD e.raw (origin N l j) - shiftRaw N H e

def localWeightRaw (xs : List Completed) (e : ℕ) (w : ℚ) : ℚ :=
  w * ∏ t ∈ Finset.range xs.length, (1 + etaQ * atD (atD xs t).gains e)

def deepWeightRaw (xs : List Completed) (e : ℕ) (w : ℚ) : ℚ :=
  w * (2 : ℚ) ^ (∑ t ∈ Finset.range xs.length, atD (atD xs t).child.scores e)

def medianRows (r g : ℕ) (rows : List (List ℚ)) : List ℚ :=
  List.ofFn fun i : Fin g => median (fun j : Fin r => atD (atD rows j.val) i.val)

def deepWeightsSized (ne : ℕ) (experts : List PackedExpert) (input : NodeInput)
    (xs : List Completed) : List ℚ :=
  List.ofFn fun e : Fin ne => deepWeightRaw xs e.val
    (if (atD experts e.val).level = input.level then 0 else atD input.weights e.val)

/-- Use the very same common-denominator transshipment clearing as the recursive reference. -/
def preparePacketSized (N r ne : ℕ) (experts : List PackedExpert) (input : NodeInput)
    (xs : List Completed) : Prepared :=
  let l := input.level
  let g := N*2^l
  let ds := deepWeightsSized ne experts input xs
  if xs.length < r then
    let L := fun e : Fin ne => localWeightRaw xs e.val
      (if (atD experts e.val).level = l then atD input.weights e.val else 0)
    let market := computeAtCommonWeightUnit (fun e => (atD experts e.val).positive) L
      (fun e (i : Fin g) => acceptsRaw l (atD experts e.val) i.val)
      (fun e i => bidRaw N l input.history (atD experts e.val) i.val)
    ⟨true, List.ofFn market.1, List.ofFn (fun e => List.ofFn (fun i => market.2 e (some i))), ds⟩
  else ⟨false, medianRows r g (xs.map Completed.baseline), [], ds⟩

def descend (input : NodeInput) (prep : Prepared) : NodeInput :=
  ⟨input.level+1, input.history++[prep.baseline], prep.deepWeights⟩

/-- Translate all the child prices back using a median at each parent coordinate. -/
def mapped (N : ℕ) (input : NodeInput) (prep : Prepared) (child : PackedRound) : List ℚ :=
  packTable N input.level (States.parentPrices (lookupTable N input.level prep.baseline)
    (lookupTable N (input.level+1) child.prices))

def finishPacketSized (N ne : ℕ) (experts : List PackedExpert) (input : NodeInput) (prep : Prepared)
    (child : PackedRound) (labels : List Bool) : Completed :=
  let gains := if prep.isProbe then
    List.ofFn fun e : Fin ne => ∑ i : Fin (N*2^input.level),
      atD (atD prep.allocation e.val) i.val * labelSign (atD experts e.val).positive * labelSign (atD labels i.val)
    else List.replicate ne 0
  ⟨prep.baseline, mapped N input prep child, gains, child⟩

/-- Packed feedback uses chronological replies local to one call. Its result is the full
Boolean row, or the first unfilled designated query. The scan is statically supplied. -/
abbrev FeedbackScan := ℕ → ℕ → List (List ℚ) → List ℚ → List ℚ → List Bool → List Bool ⊕ PackedQuery

def completeSized (scan : FeedbackScan) (N ne : ℕ) (experts : List PackedExpert) (input : NodeInput)
    (_ : List Completed) (prep : Prepared) (child : PackedRound) (tape : List Bool) :
    Completed ⊕ PackedQuery :=
  if prep.isProbe then
    (scan N input.level input.history prep.baseline child.prices tape).map
      (finishPacketSized N ne experts input prep child) id
  else .inl (finishPacketSized N ne experts input prep child [])

def assemblePacketSized (N r ne : ℕ) (experts : List PackedExpert) (input : NodeInput)
    (xs : List Completed) : PackedRound :=
  let row (j : Fin (2*r)) := atD xs j.val
  let prices := packTable N input.level (fun i => median fun j : Fin r =>
    lookupTable N input.level (row (finalIndex j)).mapped i)
  let scores := List.ofFn fun e : Fin ne =>
    if (atD experts e.val).level = input.level then
      rationalScore scaleQ sigmaQ (meanQ r (fun t =>
        probeAt (fun j : Fin r => fun z : Fin ne => atD (row (probeIndex j)).gains z.val) t e))
    else rationalScore scaleQ sigmaQ (meanQ (2*r) (fun t =>
        (probeAt (fun j : Fin (2*r) => fun z : Fin ne => atD (row j).child.scores z.val) t e : ℕ)))
  let log := (List.ofFn (fun j : Fin (2*r) => if j.val < r then
    ⟨input.level,(row j).baseline,input.history⟩ :: (row j).child.log else (row j).child.log)).flatten
  ⟨prices,scores,log⟩

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
