import OAI.Optimization.LinearProgramming.PriceGame.ControlData
import OAI.Optimization.LinearProgramming.PriceGame.ControlPrefix
import OAI.Optimization.LinearProgramming.PriceGame.StatesFeedback

/-! Pure first-order price-vector frames for the public PCG controller. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open States States.Mass

def pathFromRows (N : ℕ) (rows : List (List ℚ)) :
    (l : ℕ) → Path (Fin N) (Vertex N l)
  | 0 => .root
  | l + 1 => .extend (pathFromRows N rows l) (lookupTable N l (rows[l]?.getD [])) (vertexDecidableEq N l)

theorem packTable_zero {α : Type*} (N : ℕ) (f : Fin N → α) :
    packTable N 0 f = List.ofFn f := by
  apply List.ext_getElem
  · rw [List.length_ofFn]; exact (length_packTable N 0 f).trans (by simp)
  · intro i hi hj
    simp only [packTable, List.getElem_ofFn]
    apply congrArg f
    exact Fin.ext rfl

/-- Form a parent row by a linear scan of the public baseline and child rows. -/
def upRow (N l : ℕ) (baseline child : List ℚ) (q : Vertex N (l+1)) : List ℚ :=
  packTable N l (override (lookupTable N l baseline) (lookupTable N (l+1) child) q)

private theorem upRow_pack (N l : ℕ) (baseline : List ℚ) (x : Vertex N (l+1) → ℚ)
    (q : Vertex N (l+1)) :
    upRow N l baseline (packTable N (l+1) x) q =
      packTable N l (override (lookupTable N l baseline) x q) := by
  have funEq : lookupTable N (l+1) (packTable N (l+1) x) = x :=
    funext fun i => lookupTable_pack _ _ _ _
  rw [upRow, funEq]

/-- Every frame is a list of encoded prices and an ordinary natural index. Only the
previous baseline row is inspected at each iteration. The extra branch is used on
malformed designations in an arbitrary binary state. -/
def rootQueryRows (N : ℕ) : (l : ℕ) → List (List ℚ) → List ℚ → ℕ → PackedQuery
  | 0, _, x, q => ⟨x,q⟩
  | l+1, hist, x, q =>
    if hq : q < N*2^(l+1) then
      let v := (vertexEquivFin N (l+1)).symm ⟨q,hq⟩
      rootQueryRows N l hist (upRow N l (hist[l]?.getD []) x v) (vertexEquivFin N l v.1).val
    else ⟨[],0⟩

theorem rootQueryRows_refines (N l : ℕ) (hist : List (List ℚ)) (x : Vertex N l → ℚ) (i : Vertex N l) :
    rootQueryRows N l hist (packTable N l x) (vertexEquivFin N l i).val =
      packQuery (designatedQuery (pathFromRows N hist l) x i) := by
  induction l with
  | zero =>
    change PackedQuery.mk (packTable N 0 x) (vertexEquivFin N 0 i).val = ⟨List.ofFn x,i.val⟩
    exact congrArg (fun row => PackedQuery.mk row i.val) (packTable_zero N x)
  | succ l ih =>
    have hi : (vertexEquivFin N (l+1)).symm
        ⟨(vertexEquivFin N (l+1) i).val, (vertexEquivFin N (l+1) i).isLt⟩ = i :=
      (vertexEquivFin N (l+1)).symm_apply_apply i
    simp only [rootQueryRows, dite_eq_left (vertexEquivFin N (l+1) i).isLt, hi, upRow_pack]
    exact ih (override (lookupTable N l (hist[l]?.getD [])) x i) i.1

/-- First-order result of preparing one coordinate's feedback. -/
inductive FeedbackItem where
  | known (b : Bool)
  | request (q : PackedQuery)
deriving DecidableEq, Repr, Inhabited

def feedbackItem (N l : ℕ) (hist : List (List ℚ)) (baseline child : List ℚ)
    (i : Vertex N l) : FeedbackItem :=
  let y := lookupTable N l baseline
  let x := lookupTable N (l+1) child
  let d := parentPrices y x
  if y i < d i then .known true else if d i < y i then .known false
  else .request (rootQueryRows N l hist (packTable N l d) (vertexEquivFin N l i).val)

def takeFeedback (item : FeedbackItem) (bits : List Bool) : Sum (Bool × List Bool) PackedQuery :=
  match item with
  | .known a => .inl (a, bits)
  | .request q => match bits with
    | [] => .inr q
    | b :: bs => .inl (b, bs)

def packedObservation {N : ℕ} {α : Type*} :
    Sum (α × List Bool) (Query N) → Sum (α × List Bool) PackedQuery :=
  Sum.map id packQuery

theorem feedbackItem_refines (N l : ℕ) (hist : List (List ℚ)) (baseline child : List ℚ)
    (i : Vertex N l) (bits : List Bool) :
    packedObservation (observe (Computation.ofTree (feedbackAt (pathFromRows N hist l)
      (lookupTable N l baseline) (lookupTable N (l+1) child) i)) bits) =
      takeFeedback (feedbackItem N l hist baseline child i) bits := by
  simp only [feedbackAt, feedbackItem]
  split_ifs
  · rfl
  · rfl
  · cases bits with
    | nil =>
      change Sum.inr (packQuery _) = Sum.inr (rootQueryRows N l hist _ _)
      rw [rootQueryRows_refines]
    | cons b bs => rfl

/-- Consume the numeric reply prefix until it runs out at a tie, or return the
complete vector together with the unused suffix. -/
def consumeItems : List FeedbackItem → List Bool → Sum (List Bool × List Bool) PackedQuery
  | [], bs => .inl ([],bs)
  | item :: items, bs => match takeFeedback item bs with
    | .inr q => .inr q
    | .inl (b, tail) => (consumeItems items tail).map (fun v => (b :: v.1, v.2)) id

private theorem consumeItems_refines {N : ℕ} {I : Type*}
    (f : I → Computation N Bool) (item : I → FeedbackItem)
    (h : ∀ i bs, packedObservation (observe (f i) bs) = takeFeedback (item i) bs)
    (xs : List I) (bs : List Bool) :
    packedObservation (observe (Computation.traverse f xs) bs) = consumeItems (xs.map item) bs := by
  induction xs generalizing bs with
  | nil => rfl
  | cons x xs ih =>
    simp only [Computation.traverse, observe_bind, List.map_cons, consumeItems, ← h]
    cases hx : observe (f x) bs with
    | inr q => rfl
    | inl v =>
      obtain ⟨b,tail⟩ := v
      simp only [packedObservation, Sum.map_inl, id_eq]
      rw [observe_map, ← ih tail]
      cases observe (Computation.traverse f xs) tail <;> rfl

/-- Feedback phase of a compiled trial. Its interface and its result are first-order data.
On suspension the caller appends one new answer to the local tape and calls again. -/
def feedbackPrefix (N l : ℕ) (hist : List (List ℚ)) (baseline child : List ℚ)
    (bits : List Bool) : Sum (List Bool) PackedQuery :=
  let coords := allVertices N l
  let items := coords.map (feedbackItem N l hist baseline child)
  (consumeItems items bits).map (fun v => packTable N l (lookupFeedback coords v.1)) id

/-- The first-order feedback interpreter returns the exact next query, or the
numerically packed complete result of the original proof-producing computation. -/
theorem feedbackPrefix_refines (N l : ℕ) (hist : List (List ℚ)) (baseline child : List ℚ)
    (bits : List Bool) :
    (observe (feedbackAll (pathFromRows N hist l) (lookupTable N l baseline)
      (lookupTable N (l+1) child)) bits).map (fun v => packTable N l v.1) packQuery =
      feedbackPrefix N l hist baseline child bits := by
  unfold feedbackAll feedbackVector feedbackList feedbackPrefix
  rw [observe_map]
  dsimp only
  have hh := consumeItems_refines _ _ (feedbackItem_refines N l hist baseline child) (allVertices N l) bits
  erw [← hh]
  cases observe (Computation.traverse _ _) bits <;> rfl

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
