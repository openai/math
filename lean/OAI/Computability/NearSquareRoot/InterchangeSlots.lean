import OAI.Computability.IntegerMultiplication.Port.Lag

/-!
# Physical positions for a shared rectangle layout

Both wings of a node have `a` reserve fields, `m` main fields, and `a` more
reserve fields. For one query we place the `c` common-complement coordinates
in the first wing, one main coordinate in each wing, and the `e` difference
coordinates in the final reserve of the second wing. The other fields retain
their positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSlots

open IntegerMultiplication.Port

variable {a c e m : ℕ}

/-- The original position of a difference coordinate in the first wing. -/
def earlyReserve (hce : c + e = a) (i : Fin e) : Fin (a + m + a) :=
  ⟨c + i.val, by omega⟩

/-- The position in the final reserve to which a difference coordinate is moved. -/
def lateReserve (hce : c + e = a) (i : Fin e) : Fin (a + m + a) :=
  ⟨a + m + i.val, by omega⟩

theorem earlyReserve_injective (hce : c + e = a) :
    Function.Injective (earlyReserve (m := m) hce) := by
  intro i j h
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val h)

theorem lateReserve_injective (hce : c + e = a) :
    Function.Injective (lateReserve (m := m) hce) := by
  intro i j h
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val h)

def mainRank (a : ℕ) (j : Fin m) : Fin (a + m + a) := ⟨a + j.val, by omega⟩

/-- Physical embedding of the `C ⊕ R² ⊕ E` coordinates, in that order. -/
def active (hce : c + e = a) (j : Fin m) (i : Fin (c + (2 + e))) :
    Spot (Fin (a + m + a)) :=
  if h : i.val < c then (false, ⟨i.val, by omega⟩)
  else if h₁ : i.val = c then (false, mainRank a j)
  else if h₂ : i.val = c + 1 then (true, mainRank a j)
  else (true, lateReserve hce ⟨i.val - (c + 2), by omega⟩)

private def physicalIndex {n : ℕ} (u : Spot (Fin n)) : ℕ :=
  (if u.1 then n else 0) + u.2.val

private theorem early_iff_index_lt {n : ℕ} (u v : Spot (Fin n)) :
    Lag.early Fin.val u v ↔ physicalIndex u < physicalIndex v := by
  rcases u with ⟨_ | _, i⟩ <;> rcases v with ⟨_ | _, j⟩ <;>
    simp [Lag.early, physicalIndex] <;> omega

private theorem active_strictMono (hce : c + e = a) (j : Fin m) :
    StrictMono (fun i => physicalIndex (active hce j i)) := by
  intro i k hik
  have hik' : i.val < k.val := hik
  have hj := j.isLt
  change physicalIndex (active hce j i) < physicalIndex (active hce j k)
  unfold active
  split_ifs <;> simp [physicalIndex, mainRank, lateReserve] <;> omega

theorem active_injective (hce : c + e = a) (j : Fin m) :
    Function.Injective (active hce j) :=
  fun _ _ h => (active_strictMono hce j).injective (congrArg physicalIndex h)

theorem active_order (hce : c + e = a) (j : Fin m) :
    ∀ i l, i < l → Lag.early Fin.val (active hce j i) (active hce j l) :=
  fun i l hi => (early_iff_index_lt (active hce j i) (active hce j l)).2 (active_strictMono hce j hi)

theorem active_complement (hce : c + e = a) (j : Fin m) (i : Fin c) :
    active hce j ⟨i.val, by omega⟩ = (false, ⟨i.val, by omega⟩) := by
  simp [active, i.isLt]

theorem active_first (hce : c + e = a) (j : Fin m) :
    active hce j ⟨c, by omega⟩ = (false, mainRank a j) := by simp [active]

theorem active_second (hce : c + e = a) (j : Fin m) :
    active hce j ⟨c+1, by omega⟩ = (true, mainRank a j) := by simp [active]

theorem active_difference (hce : c + e = a) (j : Fin m) (i : Fin e) :
    active hce j ⟨c + 2 + i.val, by omega⟩ = (true, lateReserve hce i) := by
  simp [active, show ¬ c + 2 + i.val < c by omega, show c + 2 + i.val ≠ c by omega,
    show c + 2 + i.val ≠ c + 1 by omega]

private theorem pivot_other {J : Type} [DecidableEq J] {p f : ℕ}
    (x : Duplex J (Tower p f)) {u : Spot J} {l r : J}
    (hu : u ≠ (false, l)) (hv : u ≠ (true, r)) :
    hear (Lag.fire f x (.pivot l r)) u = hear x u := by
  simp [Lag.fire, hu, hv]

/-- A list of disjoint opposite-wing pivots interchanges all listed pairs and
preserves even occupied slots outside those pairs. -/
private theorem disjoint_pivots {J ι : Type} [DecidableEq J] {p f : ℕ}
    (l r : ι → J) (hl : Function.Injective l) (hr : Function.Injective r)
    (indices : List ι) (hd : indices.Nodup) (x : Duplex J (Tower p f)) :
    let y := (indices.map fun i => Lag.pivot (p := p) (l i) (r i)).foldl (Lag.fire f) x
    (∀ i ∈ indices, hear y (false, l i) = hear x (true, r i) ∧
        hear y (true, r i) = hear x (false, l i)) ∧
      ∀ u, (∀ i ∈ indices, u ≠ (false,l i) ∧ u ≠ (true,r i)) → hear y u = hear x u := by
  induction indices generalizing x with
  | nil => simp
  | cons i t ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hd
    let x' := Lag.fire f x (Lag.pivot (l i) (r i))
    obtain ⟨moved, fixed⟩ := ih ht x'
    constructor
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · have hleft : ∀ k ∈ t, (false, l j) ≠ (false,l k) ∧ (false,l j) ≠ (true,r k) := by
          intro k hk
          have hne : j ≠ k := fun h => hi (h ▸ hk)
          simp [hl.ne hne]
        have hright : ∀ k ∈ t, (true, r j) ≠ (false,l k) ∧ (true,r j) ≠ (true,r k) := by
          intro k hk
          have hne : j ≠ k := fun h => hi (h ▸ hk)
          simp [hr.ne hne]
        constructor
        · exact (fixed _ hleft).trans (by simp [x', Lag.fire])
        · exact (fixed _ hright).trans (by simp [x', Lag.fire])
      · have hne : j ≠ i := fun h => hi (h ▸ hj)
        obtain ⟨hleft, hright⟩ := moved j hj
        constructor
        · exact hleft.trans (pivot_other x (by simp) (by simp [hr.ne hne]))
        · exact hright.trans (pivot_other x (by simp [hl.ne hne]) (by simp))
    · intro u hu
      have hi := hu i List.mem_cons_self
      exact (fixed _ (fun k hk => hu k (List.mem_cons_of_mem _ hk))).trans
        (pivot_other x hi.1 hi.2)

/-- Exchange the occupied early difference coordinates with their late spare
coordinates, using one physical opposite-wing pivot for each pair. -/
def reservePivots {a c e m p : ℕ} (hce : c + e = a) : List (Lag (Fin (a+m+a)) p) :=
  (List.finRange e).map fun i =>
    .pivot (earlyReserve hce i) (lateReserve hce i)

theorem reservePivots_length {a c e m p : ℕ} (hce : c + e = a) :
    (reservePivots (p := p) (m := m) hce).length = e := by simp [reservePivots]

theorem reservePivots_prices {a c e m p : ℕ} (hce : c + e = a) :
    ((reservePivots (p := p) (m := m) hce).map Lag.prices).sum = e := by
  simp [reservePivots, List.map_map, Function.comp_def, Lag.prices]

theorem reservePivots_legal {a c e m p : ℕ} (hce : c + e = a)
    (rank : Fin (a+m+a) → ℕ) :
    ∀ q ∈ reservePivots (p := p) hce, q.legal rank := by
  intro q hq
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hq
  trivial

theorem reservePivots_effect {a c e m p : ℕ} (hce : c + e = a)
    (f : ℕ) (x : Duplex (Fin (a+m+a)) (Tower p f)) :
    let y := (reservePivots hce).foldl (Lag.fire f) x
    (∀ i : Fin e, hear y (false,earlyReserve hce i) = hear x (true,lateReserve hce i) ∧
      hear y (true,lateReserve hce i) = hear x (false,earlyReserve hce i)) ∧
    ∀ u, (∀ i : Fin e, u ≠ (false,earlyReserve hce i) ∧ u ≠ (true,lateReserve hce i)) →
      hear y u = hear x u := by
  simpa only [reservePivots, List.mem_finRange, forall_const] using
    disjoint_pivots (earlyReserve hce) (lateReserve hce)
      (earlyReserve_injective hce) (lateReserve_injective hce)
      (List.finRange e) (List.nodup_finRange _) x

/-- The endpoint can undo the reserve move by replaying the same list. -/
theorem reservePivots_involutive {a c e m p : ℕ} (hce : c + e = a) (f : ℕ) :
    Function.Involutive (fun x : Duplex (Fin (a+m+a)) (Tower p f) =>
      (reservePivots hce).foldl (Lag.fire f) x) := by
  intro x
  let y := (reservePivots hce).foldl (Lag.fire f) x
  obtain ⟨swap, fixed⟩ := reservePivots_effect hce f x
  obtain ⟨swap', fixed'⟩ := reservePivots_effect hce f y
  apply hear_all
  intro u
  by_cases h : ∃ i : Fin e, u = (false,earlyReserve hce i)
  · obtain ⟨i, rfl⟩ := h
    exact (swap' i).1.trans (swap i).2
  by_cases h' : ∃ i : Fin e, u = (true,lateReserve hce i)
  · obtain ⟨i, rfl⟩ := h'
    exact (swap' i).2.trans (swap i).1
  have hu : ∀ i : Fin e, u ≠ (false,earlyReserve hce i) ∧ u ≠ (true,lateReserve hce i) :=
    fun i => ⟨fun hi => h ⟨i, hi⟩, fun hi => h' ⟨i, hi⟩⟩
  exact (fixed' u hu).trans (fixed u hu)

end InterchangeSlots

end NearSquareRoot
end Computability
end OAI
