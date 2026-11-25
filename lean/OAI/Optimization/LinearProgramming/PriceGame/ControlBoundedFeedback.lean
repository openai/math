import OAI.Optimization.LinearProgramming.PriceGame.ControlFeedbackMachine

/-! A typed request payload for the physically executable feedback controller. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure

def requestEncoding (emit : RowState → List Bool) (q : PackedQuery) : List Bool := emit (q.index,q.prices)

def encodedItem (emit : RowState → List Bool) : FeedbackItem → RequestItem
  | .known b => .inl b
  | .request q => .inr (requestEncoding emit q)


/-- Numerical coordinate read before the scan consumes its first unanswered request. -/
def numericItem (z : ItemContext) (i : ℕ) : FeedbackItem :=
  let y := (z.2.1.drop i).headD 0
  let d := (z.2.2.drop i).headD 0
  if y < d then .known true else if d < y then .known false
  else
    let q := collapse (z.1,i,z.2.2)
    .request ⟨q.2,q.1⟩

def numericItems (s : FeedbackInput) : List FeedbackItem :=
  (List.range s.2.1.length).map (numericItem (s.1,s.2.1,medianRow s.2.1 s.2.2.1))

def boundedFeedback (s : FeedbackInput) : List Bool ⊕ PackedQuery :=
  (consumeItems (numericItems s) s.2.2.2).map Prod.fst id

theorem rawItem_eq (emit : RowState → List Bool) (z : ItemContext) (i : ℕ) :
    rawItem emit z i = encodedItem emit (numericItem z i) := by
  let y := (z.2.1.drop i).headD 0
  let d := (z.2.2.drop i).headD 0
  let q := collapse (z.1,i,z.2.2)
  change (if y < d then Sum.inl true else if d < y then .inl false else .inr (emit q)) =
    encodedItem emit (if y < d then .known true else if d < y then .known false else .request ⟨q.2,q.1⟩)
  split_ifs <;> rfl

theorem preparedItems_eq (emit : RowState → List Bool) (s : FeedbackInput) :
    preparedItems emit s = (numericItems s).map (encodedItem emit) := by
  simp only [preparedItems,numericItems,List.map_map]
  apply List.map_congr_left
  intro i _
  exact rawItem_eq emit _ i

theorem scan_encoded (emit : RowState → List Bool) (xs : List FeedbackItem) (bs acc : List Bool) :
    (xs.map (encodedItem emit)).foldl (fun s i => scanFeedbackStep (i,s)) (.inr (bs,acc)) =
      match consumeItems xs bs with
      | .inl (ys,rest) => .inr (rest,ys.reverse ++ acc)
      | .inr q => .inl (requestEncoding emit q) := by
  induction xs generalizing bs acc with
  | nil => simp [consumeItems]
  | cons item xs ih =>
    cases item with
    | known b =>
      change (xs.map (encodedItem emit)).foldl (fun s i => scanFeedbackStep (i,s)) (.inr (bs,b::acc)) = _
      rw [ih bs (b::acc)]
      simp only [consumeItems,takeFeedback]
      cases consumeItems xs bs with
      | inl v => rcases v with ⟨ys,rest⟩; simp
      | inr q => rfl
    | request q =>
      cases bs with
      | nil =>
        have stay (items : List RequestItem) (w : List Bool) :
            items.foldl (fun s i => scanFeedbackStep (i,s)) (.inl w) = .inl w := by
          induction items with | nil => rfl | cons a as ih => exact ih
        exact stay _ _
      | cons b bs =>
        change (xs.map (encodedItem emit)).foldl (fun s i => scanFeedbackStep (i,s)) (.inr (bs,b::acc)) = _
        rw [ih bs (b::acc)]
        simp only [consumeItems,takeFeedback]
        cases consumeItems xs bs with
        | inl v => rcases v with ⟨ys,rest⟩; simp
        | inr q => rfl


theorem rawFeedback_eq (emit : RowState → List Bool) (s : FeedbackInput) :
    rawFeedback emit s = (boundedFeedback s).map id (requestEncoding emit) := by
  simp only [rawFeedback,preparedItems_eq,scanFeedback,scan_encoded,boundedFeedback]
  cases consumeItems (numericItems s) s.2.2.2 with
  | inr q => rfl
  | inl v => obtain ⟨xs,tail⟩ := v; simp [finishState]

noncomputable def boundedFeedbackP :
    Procedure feedbackCode (sumCode answerListCode Wire.packedQueryCode) boundedFeedback :=
  feedbackPackedP.result (by
    intro s
    rw [rawFeedback_eq]
    cases boundedFeedback s <;> rfl)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
