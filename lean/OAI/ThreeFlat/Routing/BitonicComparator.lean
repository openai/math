import OAI.ThreeFlat.Routing.CompareWord

namespace OAI
/-! # A linear-size compare-and-exchange network for unsigned binary words -/

namespace ThreeFlat.Routing.BitonicComparator

open scoped BigOperators Classical
open TableCompiler
noncomputable section

private abbrev Gate (u : ℕ) := Option (Fin u ⊕ Fin u)

private def wire {u : ℕ} : Gate u → Fin 5 → BitSource (u+1) ((u+u)+(u+u))
  | none => fun _ => .hidden 0
  | some (.inl i) =>
    ![.hidden i.castSucc, .pin ((Fin.natAdd u i).castAdd (u+u)),
      .pin ((i.castAdd u).castAdd (u+u)), .hidden i.succ, .constant false]
  | some (.inr i) =>
    ![.hidden (Fin.last u), .pin ((i.castAdd u).castAdd (u+u)),
      .pin ((Fin.natAdd u i).castAdd (u+u)), .pin (Fin.natAdd (u+u) (i.castAdd u)),
      .pin (Fin.natAdd (u+u) (Fin.natAdd u i))]

private def test {u : ℕ} : Gate u → (Fin 5 → Bool) → Prop
  | none, z => z 0 = false
  | some (.inl _), z => z 3 = (if z 1 = z 2 then z 0 else z 2)
  | some (.inr _), z => z 3 = (if z 0 then z 2 else z 1) ∧
                         z 4 = (if z 0 then z 1 else z 2)

/-- Compare the two input words and expose their minimum and maximum in that order. -/
def network (K : Type*) [Zero K] [One K] (u : ℕ) : BitNetwork K ((u+u)+(u+u)) :=
  BitNetwork.glue (fun g : Gate u => localTableNetwork fun z => if test g z then 1 else 0) wire

theorem network_cells (K : Type*) [Zero K] [One K] (u : ℕ) :
    (network K u).cells ≤ 2048 * (u+1) := by
  simp [network, Gate, localTableNetwork_cells]
  omega

theorem network_internal (K : Type*) [Zero K] [One K] (u : ℕ) :
    (network K u).internal ≤ 2048 * (u+1) := by
  simp [network, Gate, localTableNetwork_internal]
  omega

private def Accepts {u : ℕ} (a b c d : Fin u → Bool) (h : Fin (u+1) → Bool) : Prop :=
  ∀ g : Gate u, test g (fun k => (wire g k).read h
    (Fin.append (Fin.append a b) (Fin.append c d)))

private theorem accepts_iff {u : ℕ} (a b c d : Fin u → Bool) (h : Fin (u+1) → Bool) :
    Accepts a b c d h ↔
    h 0 = false ∧
    (∀ i : Fin u, h i.succ = (if b i = a i then h i.castSucc else a i)) ∧
    ∀ i : Fin u, c i = (if h (Fin.last u) then b i else a i) ∧
      d i = (if h (Fin.last u) then a i else b i) := by
  let pin := Fin.append (Fin.append a b) (Fin.append c d)
  have step (i : Fin u) : test (some (Sum.inl i)) (fun k => (wire (some (Sum.inl i)) k).read h pin) ↔
      h i.succ = (if b i = a i then h i.castSucc else a i) := by
    change (h i.succ = (if pin ((Fin.natAdd u i).castAdd (u+u)) =
      pin ((i.castAdd u).castAdd (u+u)) then h i.castSucc else
      pin ((i.castAdd u).castAdd (u+u)))) ↔ _
    simp only [pin, Fin.append_left, Fin.append_right]
  have mux (i : Fin u) : test (some (Sum.inr i)) (fun k => (wire (some (Sum.inr i)) k).read h pin) ↔
      c i = (if h (Fin.last u) then b i else a i) ∧
      d i = (if h (Fin.last u) then a i else b i) := by
    change (pin (Fin.natAdd (u+u) (i.castAdd u)) =
      (if h (Fin.last u) then pin ((Fin.natAdd u i).castAdd (u+u)) else
        pin ((i.castAdd u).castAdd (u+u))) ∧
      pin (Fin.natAdd (u+u) (Fin.natAdd u i)) =
      (if h (Fin.last u) then pin ((i.castAdd u).castAdd (u+u)) else
        pin ((Fin.natAdd u i).castAdd (u+u)))) ↔ _
    simp only [pin, Fin.append_left, Fin.append_right]
  constructor
  · intro ok
    exact ⟨ok none, fun i => (step i).mp (ok _), fun i => (mux i).mp (ok _)⟩
  · rintro ⟨hz,hs,ho⟩ (_ | (i | i))
    · exact hz
    · exact (step i).mpr (hs i)
    · exact (mux i).mpr (ho i)

private theorem accepts_canonical {u : ℕ} (a b c d : Fin u → Bool) :
    Accepts a b c d (prefixLT b a) ↔
      c = (addressEquiv u).symm (min (addressEquiv u a) (addressEquiv u b)) ∧
      d = (addressEquiv u).symm (max (addressEquiv u a) (addressEquiv u b)) := by
  rw [accepts_iff]
  have hz : prefixLT b a 0 = false := by simp [prefixLT, prefixValue]
  have hs := prefixLT_step b a
  have last : prefixLT b a (Fin.last u) = decide ((addressEquiv u b) < (addressEquiv u a)) := by
    change decide (wordValue b < wordValue a) = _
    simp only [wordValue_addressEquiv, Fin.lt_def]
  simp only [hz, hs, true_and, last]
  by_cases lt : addressEquiv u b < addressEquiv u a
  · simp [lt, min_eq_right lt.le, max_eq_left lt.le, funext_iff, forall_and]
  · have le := le_of_not_gt lt
    simp [lt, min_eq_left le, max_eq_right le, funext_iff, forall_and]

theorem network_eval {K : Type*} [CommSemiring K] (u : ℕ) (a b c d : Fin u → Bool) :
    (network K u).eval (Fin.append (Fin.append a b) (Fin.append c d)) =
      if c = (addressEquiv u).symm (min (addressEquiv u a) (addressEquiv u b)) ∧
         d = (addressEquiv u).symm (max (addressEquiv u a) (addressEquiv u b)) then 1 else 0 := by
  let pin := Fin.append (Fin.append a b) (Fin.append c d)
  have indicator (h : Fin (u+1) → Bool) :
      (∏ g : Gate u, (if test g (fun k => (wire g k).read h pin) then (1 : K) else 0)) =
        if Accepts a b c d h then 1 else 0 := by
    by_cases ok : Accepts a b c d h
    · rw [ite_eq_left ok]
      exact Finset.prod_eq_one (fun g _ => ite_eq_left (ok g))
    · rw [ite_eq_right ok]
      obtain ⟨g,hg⟩ := Classical.not_forall.mp ok
      exact Finset.prod_eq_zero (Finset.mem_univ g) (ite_eq_right hg)
  rw [network, BitNetwork.glue_eval]
  simp only [localTableNetwork_eval]
  change (∑ h, ∏ g : Gate u, (if test g (fun k => (wire g k).read h pin) then (1 : K) else 0)) = _
  simp_rw [indicator]
  rw [Finset.sum_eq_single_of_mem (prefixLT b a) (Finset.mem_univ _)]
  · exact if_congr (accepts_canonical a b c d) rfl rfl
  · intro h _ ne
    apply ite_eq_right
    intro ok
    obtain ⟨hz, hs, _⟩ := (accepts_iff a b c d h).mp ok
    exact ne (valid_carries b a h hz hs)

end
end ThreeFlat.Routing.BitonicComparator

end OAI
