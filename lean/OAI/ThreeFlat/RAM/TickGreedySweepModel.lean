import OAI.ThreeFlat.RAM.TickGreedyRow

namespace OAI
/-! # Word-array representation and list replay of the greedy scheduler -/

namespace ThreeFlat.RAM.TickGreedySweep

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing TickGreedyRow

variable {w : ℕ}

abbrev Pair (w : ℕ) := Word w × Word w

structure Params (w : ℕ) where
  J : Word w
  B : Word w
  W : Word w
  groupCap : Word w
  slotCap : Word w

def Params.step (P : Params w) (s : State w) (item : Pair w) : State w :=
  update s item.1 item.2 P.J P.B P.W P.groupCap P.slotCap

/-- Word replay returns the final state and the pair published for every input row. -/
def replay (P : Params w) (s : State w) : List (Pair w) → State w × List (Pair w)
  | [] => (s,[])
  | item :: rest =>
    let d := P.step s item
    let tail := replay P d rest
    (tail.1,(d.group,d.slot)::tail.2)

@[simp] theorem replay_length (P : Params w) (s : State w) (items : List (Pair w)) :
    (replay P s items).2.length = items.length := by
  induction items generalizing s with
  | nil => rfl
  | cons item items ih => simp [replay,ih]

/-- Physical two-word input or output table starting at a natural word address. -/
def Stores (m : Memory w) : ℕ → List (Pair w) → Prop
  | _, [] => True
  | a, x::xs => m a = x.1 ∧ m (a+1) = x.2 ∧ Stores m (a+2) xs

def putPair (m : Memory w) (a : ℕ) (v : Pair w) : Memory w :=
  fun i => if i = a+1 then v.2 else if i = a then v.1 else m i

def putPairs (m : Memory w) (a : ℕ) : List (Pair w) → Memory w
  | [] => m
  | x::xs => putPairs (putPair m a x) (a+2) xs

theorem writePair_eq (m : Memory w) (a : ℕ) (fit : a+1 < 2^w) (v : Pair w) :
    writePair m (a : Word w) v.1 v.2 = putPair m a v := by
  have hs : (a : Word w)+1 = ((a+1 : ℕ) : Word w) := by simp
  funext i
  simp only [writePair,writeMemory,putPair,hs,Fin.val_cast_of_lt fit,Fin.val_cast_of_lt (by omega : a < 2^w)]

theorem putPairs_outside (m : Memory w) (a : ℕ) (xs : List (Pair w)) {i : ℕ}
    (outside : i < a ∨ a+2*xs.length ≤ i) : putPairs m a xs i = m i := by
  induction xs generalizing a m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons,Nat.mul_succ] at outside
    rw [putPairs,ih (putPair m a x) (a+2) (by omega)]
    simp [putPair,show i ≠ a+1 by omega,show i ≠ a by omega]

theorem stores_putPairs (m : Memory w) (a : ℕ) (xs : List (Pair w)) :
    Stores (putPairs m a xs) a xs := by
  induction xs generalizing a m with
  | nil => trivial
  | cons x xs ih =>
    change _ ∧ _ ∧ _
    refine ⟨?_,?_,ih (putPair m a x) (a+2)⟩
    · change putPairs (putPair m a x) (a+2) xs a = x.1
      rw [putPairs_outside _ _ _ (Or.inl (by omega))]
      simp [putPair]
    · change putPairs (putPair m a x) (a+2) xs (a+1) = x.2
      rw [putPairs_outside _ _ _ (Or.inl (by omega))]
      simp [putPair]

/-- Lookup of physical row `i` exposes both component words at consecutive addresses. -/
theorem stores_get (m : Memory w) (a : ℕ) (xs : List (Pair w)) (stored : Stores m a xs)
    (i : Fin xs.length) : m (a+2*i.val) = xs[i.val].1 ∧ m (a+2*i.val+1) = xs[i.val].2 := by
  induction xs generalizing a with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using And.intro stored.1 stored.2.1
    · have h := ih (a+2) stored.2.2 j
      simpa [Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem stores_congr {m m' : Memory w} (a : ℕ) (xs : List (Pair w)) (H : Stores m a xs)
    (same : ∀ x, a ≤ x → x < a+2*xs.length → m' x = m x) : Stores m' a xs := by
  induction xs generalizing a with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨v₀,v₁,tail⟩ := H
    simp only [List.length_cons,Nat.mul_succ] at same
    exact ⟨(same _ (by omega) (by omega)).trans v₀,
      (same _ (by omega) (by omega)).trans v₁,
      ih (a+2) tail (fun t h₁ h₂ => same t (by omega) (by omega))⟩

end ThreeFlat.RAM.TickGreedySweep

end OAI
