import OAI.Computability.NearSquareRoot.InterchangeROMAddressLanes
import OAI.Computability.NearSquareRoot.InterchangeROMAffineLag
import OAI.Computability.NearSquareRoot.InterchangeROMColorLabels

/-! # Stable masked rows for the two native affine instructions

The masks consumed by the color-routing loop are the output of the physical
binary inspector on two projected field words. A width uses its own field for
both projections. A shear uses the earlier control and the later address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic IntegerMultiplication.Bits IntegerMultiplication.Carry
  InterchangeAffineMask InterchangeROMColors

variable {X : Type} {s : Series X} {P G S : Tape} {p f : ℕ} [NeZero p]

private def labels (s : Series X) (key tag : X → Class ℕ) (v w : X → Tree) (A B : Row ℕ)
    (lane : ∀ k, Ribbon.read k (blob s key v) = Ribbon.read k (blob s tag w))
    (cover : ∀ x, tag x ∈ colors A B) : Labeled (Class ℕ) where
  source := blob s key v
  target := blob s tag w
  lengths := (Series.card ..).trans (Series.card ..).symm
  lanes := lane
  colors := colors A B
  distinct := colors_nodup A B
  covers z hz := by
    obtain ⟨x,rfl⟩ := (Series.elements ..).mp hz
    exact cover x

noncomputable def slotRows (e : Slot s P (line p f) S) (a : Span p) (v : X → Tree) :
    Labeled (Class ℕ) :=
  let coeff := widthRows a.neg a.top.count a.down.count
  let h := width_certified a f
  let key := sourceKey (p^f) coeff.1 coeff.2 0 (widthAction a f)
  let tag := destKey (p^f) coeff.1 coeff.2 0 (widthAction a f)
  labels s (key ∘ e.read) (tag ∘ e.read) v (v ∘ (e.tune (widthAction a f)).symm) coeff.1 coeff.2
    (slot_lanes e h.lanes v) (fun x => h.covered (e.read x))

noncomputable def axisRows (e : Axis s P (line p f) G (line p f) S) (a : Pinpoint p) (v : X → Tree) :
    Labeled (Class ℕ) :=
  let coeff := pinRows a
  let h := gather_certified (f:=f) a
  let key (t : Block p f) := sourceKey (p^f) coeff.1 coeff.2 (number t) (gatherAction a t)
  let tag (t : Block p f) := destKey (p^f) coeff.1 coeff.2 (number t) (gatherAction a t)
  labels s (fun x => key (e.pair x).1 (e.pair x).2) (fun x => tag (e.pair x).1 (e.pair x).2)
    v (v ∘ (e.tune (slideOver (gatherAction a))).symm) coeff.1 coeff.2
    (axis_lanes e (fun t => (h t).lanes) v) (fun x => (h (e.pair x).1).covered (e.pair x).2)

@[simp] theorem slotRows_colors (e : Slot s P (line p f) S) (a : Span p) (v : X → Tree) :
    let q := widthRows a.neg a.top.count a.down.count
    (slotRows e a v).colors = colors q.1 q.2 := rfl

@[simp] theorem axisRows_colors (e : Axis s P (line p f) G (line p f) S) (a : Pinpoint p)
    (v : X → Tree) : (axisRows e a v).colors = colors (pinRows a).1 (pinRows a).2 := rfl

@[simp] theorem slotRows_source (e : Slot s P (line p f) S) (a : Span p) (v : X → Tree) :
    (slotRows e a v).source.map Prod.snd = s.tab v := Series.map_tab ..

@[simp] theorem slotRows_target (e : Slot s P (line p f) S) (a : Span p) (v : X → Tree) :
    (slotRows e a v).target.map Prod.snd = s.tab (v ∘ (e.tune (widthAction a f)).symm) :=
  Series.map_tab ..

@[simp] theorem axisRows_source (e : Axis s P (line p f) G (line p f) S) (a : Pinpoint p)
    (v : X → Tree) : (axisRows e a v).source.map Prod.snd = s.tab v := Series.map_tab ..

@[simp] theorem axisRows_target (e : Axis s P (line p f) G (line p f) S) (a : Pinpoint p)
    (v : X → Tree) : (axisRows e a v).target.map Prod.snd = s.tab (v ∘ (e.tune (slideOver (gatherAction a))).symm) :=
  Series.map_tab ..

/-- Both physical faces of one high-carry class, in their original row order. -/
def maskRows (s : Series X) (M : ℕ) (A B : Row ℕ) (k : Class ℕ) (c y : X → Word) :=
  (s.tab (fun x => inspect (literal M A B k,c x,y x)),
   s.tab (fun x => inspect (literal M B A k.swap,c x,y x)))

private theorem labels_masks (key tag : X → Class ℕ) (v w : X → Tree) (A B : Row ℕ)
    (lane : ∀ k, Ribbon.read k (blob s key v) = Ribbon.read k (blob s tag w))
    (cover : ∀ x, tag x ∈ colors A B) (k : Class ℕ) (M : ℕ) (c y : X → Word)
    (src : ∀ x, inspect (literal M A B k,c x,y x) = decide (key x = k))
    (dst : ∀ x, inspect (literal M B A k.swap,c x,y x) = decide (tag x = k)) :
    (labels s key tag v w A B lane cover).masks k = maskRows s M A B k c y := by
  simp only [Labeled.masks,labels,blob,maskRows,Series.map_tab,src,dst]
  rfl

theorem slotRows_masks (e : Slot s P (line p f) S) (a : Span p) (v : X → Tree) (k : Class ℕ) :
    let q := widthRows a.neg a.top.count a.down.count
    let z := fun x => born (number (e.read x))
    (slotRows e a v).masks k = maskRows s (p^f) q.1 q.2 k z z := by
  apply labels_masks _ _ _ _ _ _ (slot_lanes e (width_certified a f).lanes v)
    (fun x => (width_certified a f).covered (e.read x))
  · intro x
    let z := e.read x
    let h := width_certifiedAt a f (number z) (number_lt z).le
    exact (h.source z k _ _ (birthValue _) (birthValue _)).trans
      (congrArg (fun key => decide (key=k)) (width_sourceKey a f (number z) z))
  · intro x
    let z := e.read x
    let h := width_certifiedAt a f (number z) (number_lt z).le
    exact (h.dest z k _ _ (birthValue _) (birthValue _)).trans
      (congrArg (fun key => decide (key=k)) (width_destKey a f (number z) z))

theorem axisRows_masks (e : Axis s P (line p f) G (line p f) S) (a : Pinpoint p) (v : X → Tree)
    (k : Class ℕ) :
    let q := pinRows a
    (axisRows e a v).masks k = maskRows s (p^f) q.1 q.2 k
      (fun x => born (number (e.pair x).1)) (fun x => born (number (e.pair x).2)) := by
  apply labels_masks _ _ _ _ _ _ (axis_lanes e (fun t => (gather_certified a t).lanes) v)
    (fun x => (gather_certified a (e.pair x).1).covered (e.pair x).2)
  · intro x
    exact (gather_certified a (e.pair x).1).source (e.pair x).2 k _ _ (birthValue _) (birthValue _)
  · intro x
    exact (gather_certified a (e.pair x).1).dest (e.pair x).2 k _ _ (birthValue _) (birthValue _)

/-- The optional initial physical mirror combines with the strictly increasing
carry-lane permutation to give the full signed width. -/
noncomputable def signedSource (neg : Bool) (e : Slot s P (line p f) S) (v : X → Tree) : X → Tree :=
  if neg then v ∘ (e.tune mirror).symm else v

theorem slotRows_signed (e : Slot s P (line p f) S) (a : Span p) (v : X → Tree) :
    (slotRows e a (signedSource a.neg e v)).target.map Prod.snd = s.tab (v ∘ (e.tune (sweep a f)).symm) := by
  rw [slotRows_target]
  cases neg : a.neg with
  | false => simp only [signedSource,widthAction,neg,Bool.false_eq_true,ite_false]
  | true =>
    congr 1
    funext x
    simp only [signedSource,neg,ite_true,widthAction,Function.comp_apply]
    change v (e.alter (e.alter x _) (mirror.symm (e.read (e.alter x _)))) = _
    rw [e.fetch,e.later,Equiv.symm_trans_apply,restored (mirror.symm _),Equiv.apply_symm_apply]
    rfl

section Layout

variable {J : Type} [DecidableEq J] {n : ℕ} (ord : J ≃ Fin n) (P G S : Tape)
variable (v : Keys P G S J (Block p f) → Tree)

theorem slotRows_layout (slot : Spot J) (a : Span p) (k : Class ℕ) :
    let z := fun (x : Keys P G S J (Block p f)) => born (number (ask x slot))
    let q := widthRows a.neg a.top.count a.down.count
    (slotRows (oneStop ord slot) a v).masks k =
      maskRows (arrays ord (line p f) P G S) (p^f) q.1 q.2 k z z := by
  rw [slotRows_masks]
  have h (x : Keys P G S J (Block p f)) := (one_use ord slot x (ask x slot)).1
  simp only [h]

theorem axisRows_layout (early late : Spot J) (legal : Lag.early (ranking ord) early late)
    (a : Pinpoint p) (k : Class ℕ) :
    let q := pinRows a
    (axisRows (twoStops ord early late legal) a v).masks k =
      maskRows (arrays ord (line p f) P G S) (p^f) q.1 q.2 k
        (fun x => born (number (ask x early))) (fun x => born (number (ask x late))) := by
  rw [axisRows_masks]
  have h (x : Keys P G S J (Block p f)) := (two_use ord early late legal x (ask x early) (ask x late)).1
  simp only [h]

end Layout

end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
