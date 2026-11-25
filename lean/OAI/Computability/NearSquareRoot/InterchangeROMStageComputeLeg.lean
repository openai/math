import OAI.Computability.NearSquareRoot.InterchangeROMStageComputeBanks

/-! # Effective chart selection for all six physical movement banks -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame

variable {X : Type} [Primcodable X] {g : X → Frame} {v b j : X → ℕ}

private theorem labelPR (hv : Primrec v) : Primrec fun x => label (v x) :=
  (Primrec.const 0).pair ((Primrec.const 0).pair (hv.pair (Primrec.const 0)))

private theorem endpointPR (hv : Primrec v) (hb : Primrec b) : Primrec fun x => endpoint (v x) (b x) :=
  (Primrec.const 1).pair ((Primrec.const 0).pair (hv.pair hb))

private theorem rectanglePR (hj : Primrec j) (hb : Primrec b) : Primrec fun x => rectangle (j x) (b x) :=
  (Primrec.const 3).pair (hj.pair ((Primrec.const 0).pair hb))

private theorem rankRowPR (hj : Primrec j) (hv : Primrec v) : Primrec fun x => rankRow (j x) (v x) :=
  (Primrec.const 5).pair (hj.pair (hv.pair (Primrec.const 0)))

theorem primrec_labelChart (hg : Primrec g) (s : Bool) (hj : Primrec j) (hv : Primrec v) :
    Primrec fun x => labelChart (g x) s (j x) (v x) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const s.toNat) (primrec_queries hg)) hj) (primrec_labels hg)) hv

private theorem offsetPR (hg : Primrec g) :
    Primrec fun x => 2*queries (g x)*labels (g x) :=
  Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) (primrec_queries hg)) (primrec_labels hg)

theorem primrec_commonChart (hg : Primrec g) (hj : Primrec j) (hb : Primrec b) :
    Primrec fun x => commonChart (g x) (j x) (b x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (offsetPR hg)
    (Primrec.nat_mul.comp hj (primrec_boxes hg))) hb

private theorem reserveOffsetPR (hg : Primrec g) :
    Primrec fun x => 2*queries (g x)*labels (g x) + queries (g x)*boxes (g x) :=
  Primrec.nat_add.comp (offsetPR hg) (Primrec.nat_mul.comp (primrec_queries hg) (primrec_boxes hg))

theorem primrec_reserveChart (hg : Primrec g) (s : Bool) (hv : Primrec v) (hb : Primrec b) :
    Primrec fun x => reserveChart (g x) s (v x) (b x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (reserveOffsetPR hg)
    (Primrec.nat_mul.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const s.toNat) (primrec_labels hg)) hv) (primrec_boxes hg))) hb

theorem primrec_localChart (hg : Primrec g) (s : Bool) (hj : Primrec j) (hv : Primrec v) (hb : Primrec b) :
    Primrec fun x => localChart (g x) s (j x) (v x) (b x) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (reserveOffsetPR hg)
    (Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 2) (primrec_labels hg)) (primrec_boxes hg)))
    (Primrec.nat_mul.comp (primrec_labelChart hg s hj hv) (primrec_boxes hg))) hb

private def guardRole (tag : ℕ) (out : Role) (action : Role × Move) : Role × Move :=
  if out.1 = tag then action else (out,none)

private def rankAction (g : Frame) (side : Bool) (j v b : ℕ) : Role × Move :=
  let w := (minor g (!side))[v]?.getD 0
  if b=0 then
    (if side then rankRow j v else label w, some (side,labelChart g side j w))
  else (if side then rankRow j v else rectangle j (b-1),some (side,commonChart g j (b-1)))

private def literalLeg (g : Frame) (stage : ℕ) (out : Role) : Role × Move :=
  let j := out.2.1
  let v := out.2.2.1
  let b := out.2.2.2
  match stage with
  | 0 => guardRole 1 out (label v,some (false,reserveChart g false v b))
  | 1 => guardRole 2 out (endpoint v b,some (false,localChart g false j v b))
  | 3 => guardRole 4 out (rankAction g false j v b)
  | 5 => guardRole 4 out (rankAction g true j v b)
  | 7 => guardRole 2 out (rectangle j b,some (true,localChart g true j v b))
  | 9 => guardRole 1 out (endpoint v b,some (true,reserveChart g true v b))
  | _ => (out,none)

private theorem literalLeg_eq (g : Frame) (n : ℕ) (out : Role) :
    literalLeg g n out = leg g n out := by
  rcases out with ⟨tag,j,v,b⟩
  rcases n with _|_|_|_|_|_|_|_|_|_|n <;>
    rcases tag with _|_|_|_|_|tag <;> cases b <;> rfl

private theorem guardPR {out : X → Role} {a : X → Role × Move}
    (tag : ℕ) (ho : Primrec out) (ha : Primrec a) :
    Primrec fun x => guardRole tag (out x) (a x) :=
  Primrec.ite (Primrec.eq.comp (Primrec.fst.comp ho) (Primrec.const tag)) ha
    (ho.pair (Primrec.const none))

private theorem pairPR {r : X → Role} {i : X → ℕ} (s : Bool) (hr : Primrec r) (hi : Primrec i) :
    Primrec fun x => (r x, some (s,i x)) :=
  hr.pair (Primrec.option_some.comp ((Primrec.const s).pair hi))

private theorem rankActionPR (hg : Primrec g) (s : Bool) (hj : Primrec j) (hv : Primrec v) (hb : Primrec b) :
    Primrec fun x => rankAction (g x) s (j x) (v x) (b x) := by
  let w := fun x => (minor (g x) (!s))[v x]?.getD 0
  have hw : Primrec w := Primrec.option_getD.comp (Primrec.list_getElem?.comp (primrec_minor hg (!s)) hv) (Primrec.const 0)
  have h₀ : Primrec fun x => if s then rankRow (j x) (v x) else label (w x) := by
    cases s <;> first | exact rankRowPR hj hv | exact labelPR hw
  have hb' : Primrec fun x => b x - 1 := Primrec.nat_sub.comp hb (Primrec.const 1)
  have h₁ : Primrec fun x => if s then rankRow (j x) (v x) else rectangle (j x) (b x-1) := by
    cases s <;> first | exact rankRowPR hj hv | exact rectanglePR hj hb'
  exact Primrec.ite (Primrec.eq.comp hb (Primrec.const 0))
    (pairPR s h₀ (primrec_labelChart hg s hj hw)) (pairPR s h₁ (primrec_commonChart hg hj hb'))

/-- The serialized movement role computes its oriented chart index, including the
singleton and incident alternatives of selected inverse-minor terms. -/
theorem primrec_leg {out : X → Role} (hg : Primrec g) (n : ℕ) (ho : Primrec out) :
    Primrec fun x => leg (g x) n (out x) := by
  have hj := Primrec.fst.comp (Primrec.snd.comp ho)
  have hv := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ho))
  have hb := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ho))
  suffices h : Primrec fun x => literalLeg (g x) n (out x) from h.of_eq fun _ => literalLeg_eq ..
  rcases n with _|_|_|_|_|_|_|_|_|_|n
  · exact guardPR 1 ho (pairPR false (labelPR hv) (primrec_reserveChart hg false hv hb))
  · exact guardPR 2 ho (pairPR false (endpointPR hv hb) (primrec_localChart hg false hj hv hb))
  · exact ho.pair (Primrec.const none)
  · exact guardPR 4 ho (rankActionPR hg false hj hv hb)
  · exact ho.pair (Primrec.const none)
  · exact guardPR 4 ho (rankActionPR hg true hj hv hb)
  · exact ho.pair (Primrec.const none)
  · exact guardPR 2 ho (pairPR true (rectanglePR hj hb) (primrec_localChart hg true hj hv hb))
  · exact ho.pair (Primrec.const none)
  · exact guardPR 1 ho (pairPR true (endpointPR hv hb) (primrec_reserveChart hg true hv hb))
  · exact ho.pair (Primrec.const none)

end InterchangeROMStage.Frame

end NearSquareRoot
end Computability
end OAI
