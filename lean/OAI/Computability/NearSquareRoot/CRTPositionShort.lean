import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Fixed positions in bounded matchings

For an involution on binary address positions, the smaller endpoints enumerate
the transpositions without repetition. Splitting those endpoints in half leaves
enough fixed positions in each factor to hold a short payload.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

variable {k : ℕ}

/-- One endpoint per nontrivial pair of an involution. -/
def lowerEnds (p : Equiv.Perm (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter fun i => i < p i

def fixedPositions (p : Equiv.Perm (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter fun i => p i = i

/-- Count both endpoints of every transposition and each fixed point once. -/
theorem matching_card (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    (fixedPositions p).card + 2 * (lowerEnds p).card = k := by
  let l := lowerEnds p
  let r := l.image p
  have lr : Disjoint l r := by
    rw [Finset.disjoint_left]
    intro x hl hr
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hr
    have a : y < p y := (Finset.mem_filter.mp hy).2
    have b : p y < p (p y) := (Finset.mem_filter.mp hl).2
    rw [hp] at b
    exact (lt_asymm a b)
  have sep : Disjoint (fixedPositions p) (l ∪ r) := by
    rw [Finset.disjoint_left]
    intro x hfix he
    have e := (Finset.mem_filter.mp hfix).2
    rcases Finset.mem_union.mp he with h | h
    · have a : x < p x := (Finset.mem_filter.mp h).2
      exact (ne_of_lt a) e.symm
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
      have a : y < p y := (Finset.mem_filter.mp hy).2
      rw [hp] at e
      exact a.ne e
  have total : fixedPositions p ∪ (l ∪ r) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x
    rcases lt_trichotomy x (p x) with e | e | e
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (by simpa [l, lowerEnds] using e))
    · exact Finset.mem_union_left _ (by simpa [fixedPositions] using e.symm)
    · apply Finset.mem_union_right _ (Finset.mem_union_right _ _)
      exact Finset.mem_image.mpr ⟨p x, by simpa [l, lowerEnds, hp x] using e, hp x⟩
  have count := congrArg Finset.card total
  rw [Finset.card_union_of_disjoint sep, Finset.card_union_of_disjoint lr,
    Finset.card_univ, Fintype.card_fin] at count
  have right : r.card = l.card := Finset.card_image_of_injective _ p.injective
  change (fixedPositions p).card + 2 * l.card = k
  omega

private def portionFun (p : Equiv.Perm (Fin k)) (s : Finset (Fin k)) (i : Fin k) : Fin k :=
  if min i (p i) ∈ s then p i else i

private theorem portion_inv (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (s : Finset (Fin k)) : Function.Involutive (portionFun p s) := by
  intro i
  have hmin : min (p i) (p (p i)) = min i (p i) := by rw [hp, min_comm]
  by_cases h : min i (p i) ∈ s
  · have e : portionFun p s i = p i := ite_eq_left h
    rw [e]
    exact (ite_eq_left (hmin ▸ h)).trans (hp i)
  · have e : portionFun p s i = i := ite_eq_right h
    rw [e, e]

/-- Restrict the involution to pairs whose smaller endpoint lies in the given set. -/
def portion (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (s : Finset (Fin k)) : Equiv.Perm (Fin k) :=
  ⟨portionFun p s, portionFun p s, portion_inv p hp s, portion_inv p hp s⟩

theorem portion_apply (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (s : Finset (Fin k)) (i : Fin k) :
    portion p hp s i = if min i (p i) ∈ s then p i else i := rfl

private theorem portion_ends (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (s : Finset (Fin k)) : lowerEnds (portion p hp s) = lowerEnds p ∩ s := by
  ext x
  simp only [lowerEnds, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  change x < portionFun p s x ↔ x < p x ∧ x ∈ s
  by_cases h : x < p x
  · by_cases hx : x ∈ s <;> simp [portionFun, min_eq_left h.le, h, hx]
  · by_cases hx : min x (p x) ∈ s <;> simp [portionFun, hx, h]

/-- Any prescribed selection of `min(m, ⌈k/4⌉)` lower endpoints,
where `m` is the number of transpositions, yields two small factors. -/
theorem short_portions (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (s : Finset (Fin k)) (hs : s ⊆ lowerEnds p)
    (hlen : s.card = min (lowerEnds p).card ((k+3)/4)) :
    let a := portion p hp s
    let b := portion p hp sᶜ
    a.trans b = p ∧ (∀ i, a i = i ∨ b i = i) ∧
      ∀ q ∈ [a, b], Function.Involutive q ∧
        (lowerEnds q).card ≤ (k+3)/4 ∧ k/2-2 ≤ (fixedPositions q).card := by
  let a := portion p hp s
  let b := portion p hp sᶜ
  have aEnds : lowerEnds a = s := (portion_ends p hp s).trans (Finset.inter_eq_right.mpr hs)
  have bEnds : lowerEnds b = lowerEnds p \ s := by
    rw [portion_ends]
    ext x
    simp
  have ca : (lowerEnds a).card ≤ (k+3)/4 := by rw [aEnds, hlen]; exact min_le_right ..
  have cb : (lowerEnds b).card ≤ (k+3)/4 := by
    rw [bEnds, Finset.card_sdiff_of_subset hs, hlen]
    have htot := matching_card p hp
    omega
  refine ⟨?_,?_,?_⟩
  · apply Equiv.ext
    intro i
    have hmin : min (p i) (p (p i)) = min i (p i) := by rw [hp, min_comm]
    change portionFun p sᶜ (portionFun p s i) = p i
    by_cases h : min i (p i) ∈ s <;> simp [portionFun, h, hmin]
  · intro i
    change portionFun p s i = i ∨ portionFun p sᶜ i = i
    by_cases h : min i (p i) ∈ s <;> simp [portionFun, h]
  · intro q hq
    have h : Function.Involutive q ∧ (lowerEnds q).card ≤ (k+3)/4 := by
      rcases List.mem_cons.mp hq with rfl | ht
      · exact ⟨portion_inv p hp s, ca⟩
      · rcases List.mem_singleton.mp ht with rfl
        exact ⟨portion_inv p hp sᶜ, cb⟩
    have eq := matching_card q h.1
    exact ⟨h.1, h.2, by omega⟩

/-- Each matching uses at most `⌈k/4⌉` pairs and fixes at least `k/2 - 2` bits. -/
theorem exists_short_matchings (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p) :
    ∃ a b : Equiv.Perm (Fin k), a.trans b = p ∧
      (∀ i, a i = i ∨ b i = i) ∧
      ∀ q ∈ [a, b], Function.Involutive q ∧
        (lowerEnds q).card ≤ (k+3)/4 ∧ k/2-2 ≤ (fixedPositions q).card := by
  obtain ⟨s, hs, hlen⟩ := Finset.exists_subset_card_eq
    (min_le_left (lowerEnds p).card ((k+3)/4))
  exact ⟨_, _, short_portions p hp s hs hlen⟩

private theorem two_mul_le_pow (m : ℕ) (hm : 8 ≤ m) : 2*m+1 ≤ 2^(m-2) := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h : m+1-2 = (m-2)+1 := by omega
    rw [h, pow_succ]
    omega

/-- A large enough matching has a selectable set of fixed bits whose cardinality
is the binary ceiling logarithm of the number of positions. -/
theorem short_payload_positions (hk : 16 ≤ k) (p : Equiv.Perm (Fin k))
    (h : k/2-2 ≤ (fixedPositions p).card) :
    ∃ s ⊆ fixedPositions p, s.card = Nat.clog 2 k := by
  apply Finset.exists_subset_card_eq
  apply le_trans _ h
  apply Nat.clog_le_of_le_pow
  exact (show k ≤ 2*(k/2)+1 by omega).trans (two_mul_le_pow _ (by omega))

/-- Execute a list of individual position exchanges, with the head executed last. -/
def positionExchanges {α : Type*} [DecidableEq α] : List (α × α) → Equiv.Perm α
  | [] => Equiv.refl _
  | (i,j)::tail => (positionExchanges tail).trans (Equiv.swap i j)

private theorem gather_positions {α : Type*} [DecidableEq α] (s t : Finset α)
    (size : s.card = t.card) :
    ∃ moves : List (α × α), moves.length ≤ t.card ∧
      (∀ x ∈ t, positionExchanges moves x ∈ s) ∧
      ∀ x, x ∉ s → x ∉ t → positionExchanges moves x = x := by
  induction t using Finset.induction generalizing s with
  | empty => exact ⟨[], by simp, by simp, fun _ _ _ => rfl⟩
  | @insert x t hx ih =>
    rw [Finset.card_insert_of_notMem hx] at size
    obtain ⟨y,hy,pick⟩ : ∃ y ∈ s, x ∈ s → y = x := by
      by_cases h : x ∈ s
      · exact ⟨x,h,fun _ => rfl⟩
      · obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
        exact ⟨y,hy,fun hx => (h hx).elim⟩
    have smaller : (s.erase y).card = t.card := by rw [Finset.card_erase_of_mem hy, size]; omega
    obtain ⟨tail,hsize,mem,away⟩ := ih _ smaller
    have free : x ∉ s.erase y := by
      intro e
      obtain ⟨hxy, hxs⟩ := Finset.mem_erase.mp e
      exact hxy (pick hxs).symm
    refine ⟨(x,y)::tail,?_,?_,?_⟩
    · simp [Finset.card_insert_of_notMem hx, hsize]
    · intro a ha
      change Equiv.swap x y (positionExchanges tail a) ∈ s
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rw [away _ free hx, Equiv.swap_apply_left]
        exact hy
      · have hv := mem _ ha
        have ne : positionExchanges tail a ≠ x := fun e => free (e ▸ hv)
        rw [Equiv.swap_apply_of_ne_of_ne ne (Finset.mem_erase.mp hv).1]
        exact (Finset.mem_erase.mp hv).2
    · intro a hs ht
      have hax : a ≠ x := fun e => ht (e ▸ Finset.mem_insert_self x t)
      have hay : a ≠ y := fun e => hs (e ▸ hy)
      have haway := away a (fun e => hs (Finset.mem_erase.mp e).2) (fun e => ht (Finset.mem_insert_of_mem e))
      change Equiv.swap x y (positionExchanges tail a) = a
      rw [haway, Equiv.swap_apply_of_ne_of_ne hax hay]

/-- Conjugation by at most `⌈log₂ k⌉` individual exchanges moves the reserved
fixed positions to the least significant end. The conjugated permutation fixes
every index in that contiguous range. -/
theorem gather_short_payload (hk : 16 ≤ k) (p : Equiv.Perm (Fin k))
    (h : k/2-2 ≤ (fixedPositions p).card) :
    ∃ moves : List (Fin k × Fin k), moves.length ≤ Nat.clog 2 k ∧
      ∀ x : Fin k, x.val < Nat.clog 2 k →
        (((positionExchanges moves).trans p).trans (positionExchanges moves).symm) x = x := by
  obtain ⟨s,hs,sz⟩ := short_payload_positions hk p h
  have stop : Nat.clog 2 k ≤ k :=
    (Nat.clog_le_of_le_pow ((show k ≤ 2*(k/2)+1 by omega).trans
      (two_mul_le_pow _ (by omega)))).trans (by omega)
  let e : Fin (Nat.clog 2 k) ↪ Fin k := Fin.castLEEmb stop
  let low := Finset.univ.map e
  have lowSize : low.card = Nat.clog 2 k := by simp [low]
  obtain ⟨moves,len,land,_⟩ := gather_positions s low (sz.trans lowSize.symm)
  refine ⟨moves, lowSize ▸ len, ?_⟩
  intro x hx
  have inside : x ∈ low := Finset.mem_map.mpr ⟨⟨x.val,hx⟩, Finset.mem_univ _, rfl⟩
  have fix := (Finset.mem_filter.mp (hs (land x inside))).2
  change (positionExchanges moves).symm (p (positionExchanges moves x)) = x
  rw [fix, Equiv.symm_apply_apply]

/-- Separate the initial contiguous range from the higher bit positions. -/
def contiguousSplit {r : ℕ} (hr : r ≤ k) : Fin k ≃ Fin r ⊕ Fin (k-r) :=
  (finCongr (show k = r + (k-r) by omega)).trans finSumFinEquiv.symm

/-- A permutation fixing the low range is precisely a permutation on the remaining
`k-r` positions, acting as the identity on the reserved payload positions. -/
theorem restrict_high_positions {r : ℕ} (hr : r ≤ k) (p : Equiv.Perm (Fin k))
    (fix : ∀ x : Fin k, x.val < r → p x = x) :
    ∃ high : Equiv.Perm (Fin (k-r)),
      (((contiguousSplit hr).symm.trans p).trans (contiguousSplit hr)) =
        (Equiv.refl (Fin r)).sumCongr high := by
  let e := contiguousSplit hr
  let q := (e.symm.trans p).trans e
  have low (j : Fin r) : q (.inl j) = .inl j := by
    change e (p (e.symm (.inl j))) = .inl j
    rw [fix _ (show (e.symm (.inl j)).val < r from j.isLt), Equiv.apply_symm_apply]
  have keep (v : Fin r ⊕ Fin (k-r)) : v.isRight ↔ (q v).isRight := by
    cases v with
    | inl j => simp [low]
    | inr j =>
      cases eq : q (.inr j) with
      | inr j' => simp
      | inl j' => exact False.elim (Sum.inr_ne_inl (q.injective (eq.trans (low j').symm)))
  let right : {x : Fin r ⊕ Fin (k-r) // x.isRight} ≃ Fin (k-r) := Equiv.sumIsRight
  let sub := q.subtypeEquiv (p := fun x => x.isRight = true) (q := fun x => x.isRight = true) keep
  refine ⟨(right.symm.trans sub).trans right, ?_⟩
  apply Equiv.ext
  intro x
  cases x with
  | inl j => exact low j
  | inr j =>
    exact (congrArg Subtype.val (right.symm_apply_apply (sub (right.symm j)))).symm

end Controlled

end NearSquareRoot
end Computability
end OAI
