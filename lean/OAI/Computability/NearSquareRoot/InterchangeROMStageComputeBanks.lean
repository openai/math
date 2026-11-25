import OAI.Computability.NearSquareRoot.InterchangeROMStageRoles
import Mathlib.Computability.Primrec.List

/-! # Primitive-recursive enumeration of the banks in a rectangle stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame

variable {X : Type} [Primcodable X] {g : X → Frame}

theorem primrec_queries (hg : Primrec g) : Primrec fun x => queries (g x) := Primrec.fst.comp hg
theorem primrec_labels (hg : Primrec g) : Primrec fun x => labels (g x) := Primrec.fst.comp (Primrec.snd.comp hg)
theorem primrec_boxes (hg : Primrec g) : Primrec fun x => boxes (g x) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hg))
theorem primrec_mask (hg : Primrec g) : Primrec fun x => mask (g x) := Primrec.fst.comp
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hg)))

theorem primrec_minor (hg : Primrec g) (s : Bool) : Primrec fun x => minor (g x) s := by
  have t := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hg)))
  cases s with
  | false => exact Primrec.snd.comp t
  | true => exact Primrec.fst.comp t

theorem primrec_incident {v b : X → ℕ} (hg : Primrec g) (s : Bool) (hv : Primrec v)
    (hb : Primrec b) : Primrec fun x => incident (g x) s (v x) (b x) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (primrec_mask hg)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const s.toNat) (primrec_boxes hg)) hb) (primrec_labels hg)) hv))
    (Primrec.const false)

private theorem filterPR {A : Type} [Primcodable A] {l : X → List A} {p : X → A → Bool}
    (hl : Primrec l) (hp : Primrec₂ p) : Primrec fun x => (l x).filter (p x) := by
  let step (x : X) (a : A × List A) := bif p x a.1 then a.1 :: a.2 else a.2
  have hs : Primrec₂ step := (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)).to₂
  apply (Primrec.list_foldr hl (Primrec.const []) hs).of_eq
  intro x
  induction l x with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons,step,ih,List.filter_cons]
    cases p x a <;> simp

theorem primrec_localBoxes {v : X → ℕ} (hg : Primrec g) (s : Bool) (hv : Primrec v) :
    Primrec fun x => localBoxes (g x) s (v x) :=
  filterPR (Primrec.list_range.comp (primrec_boxes hg))
    (primrec_incident (hg.comp Primrec.fst) s (hv.comp Primrec.fst) Primrec.snd).to₂

private theorem labelsPR (hg : Primrec g) : Primrec fun x => labelsBank (g x) :=
  Primrec.list_map (Primrec.list_range.comp (primrec_labels hg))
    ((Primrec.const 0).pair ((Primrec.const 0).pair (Primrec.snd.pair (Primrec.const 0)))).to₂

private theorem endpointsPR (hg : Primrec g) (s : Bool) : Primrec fun x => endpoints (g x) s := by
  apply Primrec.list_flatMap (Primrec.list_range.comp (primrec_labels hg))
  unfold Primrec₂
  dsimp only
  apply Primrec.list_map (primrec_localBoxes (hg.comp Primrec.fst) s Primrec.snd)
  exact ((Primrec.const 1).pair ((Primrec.const 0).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂

private theorem queryEndpointsPR (hg : Primrec g) (s : Bool) : Primrec fun x => queryEndpoints (g x) s := by
  apply Primrec.list_flatMap (Primrec.list_range.comp (primrec_queries hg))
  unfold Primrec₂
  dsimp only
  apply Primrec.list_map (endpointsPR (hg.comp Primrec.fst) s)
  have eb : Primrec fun x : (X × ℕ) × Role => x.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact ((Primrec.const 2).pair ((Primrec.snd.comp Primrec.fst).pair eb)).to₂

private theorem productPR {n m : X → ℕ} (hn : Primrec n) (hm : Primrec m)
    {f : ℕ → ℕ → Role} (hf : Primrec₂ f) : Primrec fun x => product (n x) (m x) f := by
  apply Primrec.list_flatMap (Primrec.list_range.comp hn)
  unfold Primrec₂
  dsimp only
  apply Primrec.list_map (Primrec.list_range.comp (hm.comp Primrec.fst))
  exact (hf.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

private theorem boxesBankPR (hg : Primrec g) : Primrec fun x => boxesBank (g x) :=
  productPR (primrec_queries hg) (primrec_boxes hg)
    ((Primrec.const 3).pair (Primrec.fst.pair ((Primrec.const 0).pair Primrec.snd))).to₂

private theorem rankBankPR (hg : Primrec g) : Primrec fun x => rankBank (g x) :=
  productPR (primrec_queries hg) (Primrec.list_length.comp (primrec_minor hg true))
    ((Primrec.const 5).pair (Primrec.fst.pair (Primrec.snd.pair (Primrec.const 0)))).to₂

private theorem queryBankPR (hg : Primrec g) : Primrec fun x => queryBank (g x) :=
  productPR (primrec_queries hg) (primrec_labels hg)
    ((Primrec.const 6).pair (Primrec.fst.pair (Primrec.snd.pair (Primrec.const 0)))).to₂

private theorem termsPR (hg : Primrec g) (s : Bool) : Primrec fun x => terms (g x) s := by
  apply Primrec.list_flatMap (Primrec.list_range.comp (primrec_queries hg))
  unfold Primrec₂
  dsimp only
  apply Primrec.list_flatMap (Primrec.list_range.comp (Primrec.list_length.comp (primrec_minor (hg.comp Primrec.fst) s)))
  unfold Primrec₂
  dsimp only
  let F := (X × ℕ) × ℕ
  have hfield : Primrec fun a : F => g a.1.1 := hg.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec fun a : F => a.1.2 := Primrec.snd.comp Primrec.fst
  have hi : Primrec fun a : F => a.2 := Primrec.snd
  apply Primrec.list_cons.comp ((Primrec.const 4).pair (hj.pair (hi.pair (Primrec.const 0))))
  apply Primrec.list_map (primrec_localBoxes hfield s
    (Primrec.option_getD.comp (Primrec.list_getElem?.comp (primrec_minor hfield s) hi) (Primrec.const 0)))
  exact ((Primrec.const 4).pair ((hj.comp Primrec.fst).pair
    ((hi.comp Primrec.fst).pair (Primrec.succ.comp Primrec.snd)))).to₂

/-- Instantiate any one of the intermediate bank layouts, including its
incidence filtering and rank-term enumeration. -/
theorem primrec_bank (hg : Primrec g) : ∀ n, Primrec fun x => bank (g x) n
  | 0 => labelsPR hg
  | 1 => Primrec.list_append.comp (labelsPR hg) (endpointsPR hg false)
  | 2 => Primrec.list_append.comp (labelsPR hg) (queryEndpointsPR hg false)
  | 3 => Primrec.list_append.comp (labelsPR hg) (boxesBankPR hg)
  | 4 => Primrec.list_append.comp (Primrec.list_append.comp (labelsPR hg) (boxesBankPR hg)) (termsPR hg true)
  | 5 => Primrec.list_append.comp (Primrec.list_append.comp (labelsPR hg) (boxesBankPR hg)) (rankBankPR hg)
  | 6 => Primrec.list_append.comp (Primrec.list_append.comp (labelsPR hg) (boxesBankPR hg)) (termsPR hg false)
  | 7 => Primrec.list_append.comp (Primrec.list_append.comp (labelsPR hg) (queryBankPR hg)) (boxesBankPR hg)
  | 8 => Primrec.list_append.comp (Primrec.list_append.comp (labelsPR hg) (queryBankPR hg)) (queryEndpointsPR hg true)
  | 9 | 10 => Primrec.list_append.comp (labelsPR hg) (endpointsPR hg true)
  | _+11 => labelsPR hg

end InterchangeROMStage.Frame

end NearSquareRoot
end Computability
end OAI
