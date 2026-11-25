import OAI.Computability.QuantumFactoring.BitStackGCD
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackListLength
import OAI.Computability.QuantumFactoring.BitStackTabulate
import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedback

/-! A finite pure Boolean-stack procedure that consumes a prefix of answers to a
prepared row of feedback items and stops at the first unanswered genuine query. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure

abbrev RequestItem := Bool ⊕ List Bool
abbrev ScanState := List Bool ⊕ (List Bool × List Bool)

def itemCode : RequestItem → List Bool := sumCode boolCode id
def answerListCode : List Bool → List Bool := listCode boolCode
def scanCode : ScanState → List Bool := sumCode id (prodCode answerListCode answerListCode)

private noncomputable def leftP {A B : Type} (ea : A → List Bool) (eb : B → List Bool) :
    Procedure ea (sumCode ea eb) (Sum.inl : A → A ⊕ B) :=
  (prepend ea [false]).result (by intro a; rfl)

private noncomputable def rightP {A B : Type} (ea : A → List Bool) (eb : B → List Bool) :
    Procedure eb (sumCode ea eb) (Sum.inr : B → A ⊕ B) :=
  (prepend eb [true]).result (by intro b; rfl)

private noncomputable def getLeftP {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (d : A) :
    Procedure (sumCode ea eb) ea (Sum.elim id (fun _ => d)) :=
  casesSum (identity ea) (constant eb ea d)
private noncomputable def getRightP {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (d : B) :
    Procedure (sumCode ea eb) eb (Sum.elim (fun _ => d) id) :=
  casesSum (constant ea eb d) (identity eb)
private noncomputable def isLeftP {A B : Type} (ea : A → List Bool) (eb : B → List Bool) :
    Procedure (sumCode ea eb) boolCode (Sum.elim (fun _ => true) (fun _ => false)) :=
  casesSum (constant ea boolCode true) (constant eb boolCode false)

/-- Left retains the first unresolved word; right stores remaining input and reversed
collected labels. An already suspended state ignores all later list entries. -/
def scanFeedbackStep : RequestItem × ScanState → ScanState
  | (_, .inl w) => .inl w
  | (.inl b, .inr (left, acc)) => .inr (left, b :: acc)
  | (.inr w, .inr ([],_)) => .inl w
  | (.inr _, .inr (b :: bs,acc)) => .inr (bs,b::acc)

noncomputable def scanFeedbackStepP : Procedure (prodCode itemCode scanCode) scanCode scanFeedbackStep := by
  let rc := prodCode answerListCode answerListCode
  let i := first itemCode scanCode
  let st := second itemCode scanCode
  let active := (getRightP id rc ([],[])).comp st
  let left := (first answerListCode answerListCode).comp active
  let acc := (second answerListCode answerListCode).comp active
  let bit := (getLeftP boolCode id false).comp i
  let word := (getRightP boolCode id []).comp i
  let append (f : _ → Bool) (b : Procedure (prodCode itemCode scanCode) boolCode f) :=
    (listCons boolCode).comp (b.pair acc)
  let k := (rightP id rc).comp (left.pair (append _ bit))
  let req := (leftP id rc).comp word
  let read := (listHead boolCode false).comp left
  let useReply := (rightP id rc).comp (((listTail boolCode).comp left).pair (append _ read))
  let chooseReq := conditional ((listEmpty boolCode).comp left) req useReply
  let activeStep := conditional ((isLeftP boolCode id).comp i) k chooseReq
  exact (conditional ((isLeftP id rc).comp st) st activeStep).congrFun (by
    rintro ⟨item,state⟩
    cases state with
    | inl => rfl
    | inr data =>
      obtain ⟨left,acc⟩ := data
      cases item with
      | inl => rfl
      | inr => cases left <;> rfl)

private theorem boolList_size (xs : List Bool) : (answerListCode xs).length = 4*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (listCode boolCode (x::xs)).length = _
    rw [listCode_length_cons]
    change 2*1+2+(answerListCode xs).length = _
    rw [ih, List.length_cons]
    omega

private theorem stepSize (item : RequestItem) (s : ScanState) :
    (scanCode (scanFeedbackStep (item,s))).length ≤ (scanCode s).length + 2*(itemCode item).length+4 := by
  cases s with
  | inl w => change w.length + 1 ≤ _; simp [scanCode, sumCode]; omega
  | inr data =>
    rcases data with ⟨bits,acc⟩
    cases item with
    | inl b => simp [scanFeedbackStep, scanCode, sumCode, prodCode, pairBits_length, boolList_size]; omega
    | inr w =>
      cases bits <;> simp [scanFeedbackStep, scanCode, itemCode, sumCode, prodCode,
        pairBits_length, boolList_size] <;> omega

private theorem scanSize (items : List RequestItem) (s : ScanState) :
    (scanCode (items.foldl (fun s i => scanFeedbackStep (i,s)) s)).length ≤
      (scanCode s).length + 2*(listCode itemCode items).length := by
  induction items generalizing s with
  | nil => simp
  | cons a as ih =>
    have hs := ih (scanFeedbackStep (a,s))
    have ha := stepSize a s
    rw [List.foldl_cons, listCode_length_cons]
    omega

def scanFeedback (v : List RequestItem × List Bool) : ScanState :=
  v.1.foldl (fun s i => scanFeedbackStep (i,s)) (.inr (v.2,[]))

noncomputable def scanFeedbackP : Procedure (prodCode (listCode itemCode) answerListCode) scanCode scanFeedback := by
  let fold := foldList (Sum.inl false : RequestItem) scanFeedbackStepP (2*Polynomial.X+1) (by
    intro xs s k
    change (scanCode ((xs.take k).foldl (fun s i => scanFeedbackStep (i,s)) s)).length ≤ _
    have hb := scanSize (xs.take k) s
    have hc := listCode_length_take_le itemCode k xs
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_one]
    omega)
  let domain := prodCode (listCode itemCode) answerListCode
  let items := first (listCode itemCode) answerListCode
  let bits := second (listCode itemCode) answerListCode
  let rc := prodCode answerListCode answerListCode
  let init := (rightP id rc).comp (bits.pair (constant domain answerListCode []))
  exact (fold.comp (items.pair init)).congrFun (by intro v; rfl)

/-- Map public packed requests to their actual bytes. -/
def packedWord (q : PackedQuery) : List Bool :=
  OracleSpec.encodeNat q.index ++ q.prices.flatMap OracleSpec.encodeRat

def itemWord : FeedbackItem → RequestItem
  | .known b => .inl b
  | .request q => .inr (packedWord q)

private theorem pending_fold (xs : List RequestItem) (w : List Bool) :
    xs.foldl (fun s i => scanFeedbackStep (i,s)) (.inl w) = .inl w := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem scanFeedback_refines (items : List FeedbackItem) (bs acc : List Bool) :
    ((items.map itemWord).foldl (fun s i => scanFeedbackStep (i,s)) (.inr (bs,acc))) =
      match consumeItems items bs with
      | .inl (ys,rest) => .inr (rest, ys.reverse ++ acc)
      | .inr q => .inl (packedWord q) := by
  induction items generalizing bs acc with
  | nil => simp [consumeItems]
  | cons i items ih =>
    cases i with
    | known b =>
      change (items.map itemWord).foldl (fun s i => scanFeedbackStep (i,s)) (.inr (bs,b::acc)) = _
      rw [ih bs (b::acc)]
      simp only [consumeItems, takeFeedback]
      cases consumeItems items bs with
      | inl p => rcases p with ⟨ys,rs⟩; simp
      | inr q => rfl
    | request q =>
      cases bs with
      | nil => exact pending_fold (items.map itemWord) (packedWord q)
      | cons b bs =>
        change (items.map itemWord).foldl (fun s i => scanFeedbackStep (i,s)) (.inr (bs,b::acc)) = _
        rw [ih bs (b::acc)]
        simp only [consumeItems, takeFeedback]
        cases consumeItems items bs with
        | inl p => rcases p with ⟨ys,rs⟩; simp
        | inr q => rfl

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
