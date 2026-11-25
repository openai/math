import OAI.Geometry.Hirsch.LiftTrip

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Compression

def offset (width l : ℕ) := if width ∣ l then 0 else if width ∣ l+1 then 2 else 1

def code (width base l : ℕ) := 3*(l/width%base)+offset width l

theorem adjacent (width base l : ℕ) (hw : 3 ≤ width) (same : (l+1)/width/base = l/width/base) :
    (offset width l = 1 ∧ offset width (l+1) = 1) ∨ code width base l + 1 = code width base (l+1) := by
  have avoid : ∀ x y, 0 < y → y < width → width ∣ x → ¬width ∣ x+y := by
    intro x y hp hs hx he
    have hd : width ∣ y := by simpa using Nat.dvd_sub he hx
    exact hs.not_ge (Nat.le_of_dvd hp hd)
  by_cases hb : width ∣ l+1
  · have hn : ¬width ∣ l := fun hh => avoid l 1 (by omega) (by omega) hh hb
    have h₁ := Nat.mod_add_div ((l+1)/width) base
    have h₂ := Nat.mod_add_div (l/width) base
    rw [same] at h₁
    have h₃ := Nat.succ_div_of_dvd hb
    right; simp only [code,offset,ite_eq_left hb,ite_eq_right hn]; omega
  have h := Nat.succ_div_of_not_dvd hb
  by_cases ha : width ∣ l
  · have hn : ¬width ∣ l+1+1 := avoid l 2 (by omega) (by omega) ha
    right; simp [code,offset,h,hb,ha,hn]
  by_cases hc : width ∣ l+1+1
  · right; simp [code,offset,h,hb,ha,hc]
  · left; simp [offset,ha,hb,hc]

end Compression

namespace World

open Compression

variable {X : Type} {n : ℕ} (w : World X n) (width base : ℕ)

abbrev Compressed (X : Type) := X ⊕ (X × Bool)

def index (x : X) := w.block width x % base

def height : Compressed X → ℕ
  | .inl x => code width base (w.layer x)
  | .inr (x,d) => 3*w.index width base x + if d then 2 else 0

def rankPlus : Compressed X → ℕ
  | .inl x => w.rank x+1
  | .inr _ => 0

def awake : Compressed X → Prop
  | .inl x => ¬w.Blank width x ∨ w.live x ∧ ¬w.Blank (width*base) x
  | .inr _ => False

def finish (d : Bool) (x : X) : Compressed X :=
  if w.Blank width x then .inl x else if _h : w.live x then finish d (w.step x d) else .inr (x,d)
termination_by w.rank x
decreasing_by exact w.decrease _ _h _

def dest (i : Compressed X) (d : Bool) : Compressed X :=
  match i with
  | .inl x => if w.Blank width x then .inl (w.step x d) else w.finish width d x
  | .inr _ => i

theorem height_real (x : X) : w.height width base (.inl x) =
    3*w.index width base x + offset width (w.layer x) := rfl

theorem offset_mid (x : X) : offset width (w.layer x) = 1 ↔ ¬w.Blank width x := by
  unfold offset Blank; split_ifs <;> simp_all

theorem offset_small (x : X) : offset width (w.layer x) < 3 := by unfold offset; split_ifs <;> omega

theorem adj {x : X} (hw : 3 ≤ width) (hl : w.live x) (d : Bool)
    (hs : w.block (width*base) (w.step x d) = w.block (width*base) x)
    (hb : w.Blank width x ∨ w.Blank width (w.step x d)) :
    if d then w.height width base (.inl (w.step x d)) = w.height width base (.inl x)+1
    else w.height width base (.inl (w.step x d))+1 = w.height width base (.inl x) := by
  have hn : ¬(offset width (w.layer x) = 1 ∧ offset width (w.layer (w.step x d)) = 1) := by
    rw [w.offset_mid,w.offset_mid]; tauto
  simp only [block,← Nat.div_div_eq_div_mul] at hs
  cases d
  · have he := w.west _ hl
    have hh := adjacent width base (w.layer (w.step x false)) hw (by rw [he]; exact hs.symm)
    rw [he] at hh; exact hh.resolve_left (fun h => hn h.symm)
  · have he := w.east _ hl
    have hh := adjacent width base (w.layer x) hw (by rw [← he]; exact hs)
    rw [← he] at hh; exact (hh.resolve_left hn).symm

theorem finished (hw : 3 ≤ width) (d : Bool) : ∀ x, ¬w.Blank width x →
    w.height width base (w.finish width d x) = 3*w.index width base x + (if d then 2 else 0) ∧
      w.rankPlus (w.finish width d x) < w.rank x+1 := by
  apply w.induct
  intro x ih hn
  rw [finish,ite_eq_right hn]
  split
  swap
  · exact ⟨rfl,Nat.zero_lt_succ _⟩
  rename_i hl
  have hs := w.same_step hl hn d
  have hindex : w.index width base (w.step x d) = w.index width base x := congrArg (· % base) hs
  have hdec := w.decrease _ hl d
  by_cases hb : w.Blank width (w.step x d)
  · rw [finish,ite_eq_left hb]
    have h := w.adj width base hw hl d (by simp only [parent,hs]) (.inr hb)
    rw [w.height_real width base x,(w.offset_mid width x).mpr hn] at h
    refine ⟨?_,Nat.succ_lt_succ hdec⟩
    cases d <;> simp only [Bool.false_eq_true,↓reduceIte] at * <;> omega
  obtain ⟨he,ht⟩ := ih hl d hb
  exact ⟨by rw [he,hindex],ht.trans (Nat.succ_lt_succ hdec)⟩

theorem destination (hw : 3 ≤ width) (i : Compressed X) (hl : w.awake width base i) (d : Bool) :
    (if d then w.height width base (w.dest width i d) = w.height width base i + 1
      else w.height width base (w.dest width i d)+1 = w.height width base i) ∧
    w.rankPlus (w.dest width i d) < w.rankPlus i := by
  rcases i with x | t
  swap
  · exact hl.elim
  by_cases hb : w.Blank width x
  · obtain ⟨hl,hn⟩ := hl.resolve_left (not_not.mpr hb)
    rw [dest,ite_eq_left hb]
    exact ⟨w.adj width base hw hl d (w.same_step hl hn d) (.inl hb),Nat.succ_lt_succ (w.decrease _ hl d)⟩
  rw [dest,ite_eq_right hb]
  obtain ⟨he,ht⟩ := w.finished width base hw d x hb
  refine ⟨?_,ht⟩
  rw [he,w.height_real,(w.offset_mid width x).mpr hb]
  cases d <;> simp

def board (hw : 3 ≤ width) (hb : 0 < base) : Board (Compressed X) base where
  layer := w.height width base
  live := w.awake width base
  rank := w.rankPlus
  step := w.dest width
  bound := by
    rintro (x | ⟨x,d⟩)
    · rw [height_real]; have := w.offset_small width x; have : w.index width base x < base := Nat.mod_lt _ hb; omega
    · have : w.index width base x < base := Nat.mod_lt _ hb
      simp only [height]; split <;> omega
  west i hl := (w.destination width base hw i hl false).1
  east i hl := (w.destination width base hw i hl true).1
  decrease i hl d := (w.destination width base hw i hl d).2

end World
end OAI.Geometry.Hirsch.Layer
