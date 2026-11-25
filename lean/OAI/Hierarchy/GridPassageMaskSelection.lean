import OAI.Hierarchy.GridPassageRAMReadback

namespace OAI
/-! # Exact cells removed by a width-dependent mark correction -/

namespace Hierarchy.GridPassageRAMMask
open GridLens GridPassageRAMRow
open scoped Classical

variable {k n E B : ℕ}
variable (direction : Fin E → Fin k) (row : Fin E → Fin k → Fin (n+1))
    (touch : Fin E → Option (Fin (n+1))) (width : Fin k → ℕ)

/-- A padded rank names a mark only when it is both present and beyond the direction's width. -/
def removeAt (mark : ℕ) (x : Fin k → Fin (n+1)) (j : Fin k) (r : Fin B) : Option ℕ :=
  let s := untouchedRails direction row touch x j
  if h : width j ≤ r.val ∧ r.val < s.card then
    let e := s.orderEmbOfFin rfl ⟨r.val,h.2⟩
    some (mark+cursor e.val (x j))
  else none

theorem removeAt_ge {mark : ℕ} {x : Fin k → Fin (n+1)} {j : Fin k} {r : Fin B} {a : ℕ}
    (hit : removeAt direction row touch width mark x j r = some a) : mark ≤ a := by
  simp only [removeAt] at hit
  split at hit
  · have same := Option.some.inj hit
    rw [←same]
    exact Nat.le_add_right _ _
  · cases hit

private theorem rank_full {t : ℕ} (s : Finset (Fin t)) (i : Fin s.card) :
    (s.filter (· < s.orderEmbOfFin rfl i)).card = i.val :=
  GridPassageRank.rank_orderEmbOfCardLe s le_rfl i

private theorem cursor_injective {e f : Fin E} {s t : Fin (n+1)} (eqn : cursor e.val s = cursor f.val t) :
    e = f ∧ s = t := by
  have same : finProdFinEquiv (e,s) = finProdFinEquiv (f,t) := Fin.ext (by
    change s.val+(n+1)*e.val = t.val+(n+1)*f.val
    simpa only [cursor,Nat.add_comm,Nat.mul_comm] using eqn)
  have pairs := finProdFinEquiv.injective same
  exact ⟨congrArg Prod.fst pairs,congrArg Prod.snd pairs⟩

/-- A genuine mark is cleared precisely when its untouched rail rank is in the surplus interval. -/
theorem exists_remove_iff (mark : ℕ) (e : Fin E) (t : Fin (n+1)) :
    (∃ (x : Fin k → Fin (n+1)) (j : Fin k) (r : Fin B),
      removeAt direction row touch width mark x j r = some (mark+cursor e.val t)) ↔
    let x := cellOnRail (direction e) (row e) t
    touch e ≠ some t ∧ width (direction e) ≤ rankIn direction row touch x (direction e) e ∧
      rankIn direction row touch x (direction e) e < B := by
  dsimp only
  constructor
  · rintro ⟨x,j,r,hit⟩
    let s := untouchedRails direction row touch x j
    have gate : width j ≤ r.val ∧ r.val < s.card := by
      by_contra wrong
      simp [removeAt,show ¬(width j≤r.val ∧ r.val<(untouchedRails direction row touch x j).card) from wrong] at hit
    let f := s.orderEmbOfFin rfl ⟨r.val,gate.2⟩
    change (if h : width j ≤ r.val ∧ r.val < s.card then some (mark + cursor (s.orderEmbOfFin rfl ⟨r.val,h.2⟩).val (x j)) else none) = _ at hit
    rw [dite_eq_left gate] at hit
    have same : cursor f.val (x j) = cursor e.val t := Nat.add_left_cancel (Option.some.inj hit)
    obtain ⟨rail,time⟩ := cursor_injective same
    have mem : f ∈ s := s.orderEmbOfFin_mem rfl _
    obtain ⟨d,foot,pass⟩ := (Finset.mem_filter.mp mem).2
    change direction f = j at d
    change cellOnRail j (row f) (x j) = x at foot
    change touch f ≠ some (x j) at pass
    have rk : rankIn direction row touch x j f = r.val := rank_full s ⟨r.val,gate.2⟩
    rw [rail] at d foot pass rk
    have cell : cellOnRail (direction e) (row e) t = x := by rw [d,←time]; exact foot
    rw [cell,d,rk,←time]
    exact ⟨pass,gate.1,r.isLt⟩
  · rintro ⟨pass,lo,hi⟩
    let j := direction e
    let x := cellOnRail j (row e) t
    let s := untouchedRails direction row touch x j
    have atj : x j = t := by simp [x]
    have he : e ∈ s := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,rfl,by rw [atj],by simpa only [atj] using pass⟩
    let rank := rankIn direction row touch x j e
    let index := (s.orderIsoOfFin rfl).symm ⟨e,he⟩
    have reconstruct : s.orderEmbOfFin rfl index = e := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨e,he⟩)
    have ranked : rank = index.val := by
      change (s.filter (· < e)).card = _
      rw [←reconstruct]
      exact rank_full s index
    have rankFit : rank < s.card := by simpa only [ranked] using index.isLt
    let r : Fin B := ⟨rank,hi⟩
    refine ⟨x,j,r,?_⟩
    change (if h : width j ≤ rank ∧ rank < s.card then some (mark + cursor (s.orderEmbOfFin rfl ⟨rank,h.2⟩).val (x j)) else none) = _
    rw [dite_eq_left ⟨lo,rankFit⟩]
    have seq : (⟨rank,rankFit⟩ : Fin s.card) = index := Fin.ext ranked
    rw [seq,reconstruct,atj]

end Hierarchy.GridPassageRAMMask

end OAI
