import OAI.ThreeFlat.Routing.CallTag
import OAI.ThreeFlat.Routing.LocalChecksSize
import Init.Data.BitVec.Bitblast

namespace OAI
/-! # A ripple counter for idle position identifiers

Each row reports the count of earlier marked rows. A hidden carry crosses each
bit within a row. Consecutive rows share the preceding row's count wires.
-/

namespace ThreeFlat.Routing.CallPool.CallTagPrefix

open scoped Classical
open ExactQuantumFactoring
noncomputable section

abbrev Pin (H n : ℕ) := Fin H ⊕ (Fin H × Fin n)
private abbrev Hidden (H n : ℕ) := Fin H × Fin (n+1)

def pins {H n : ℕ} (flag : Fin H → Bool) (word : Fin H → Fin n → Bool) : Pin H n → Bool :=
  Sum.elim flag (Function.uncurry word)

def count {H : ℕ} (flag : Fin H → Bool) (i : Fin H) : ℕ :=
  ((Finset.Iio i).filter fun t => flag t = true).card

def words {H : ℕ} (n : ℕ) (flag : Fin H → Bool) (i : Fin H) (j : Fin n) : Bool :=
  (BitVec.ofNat n (count flag i)).getLsbD j.val

private def prev {H : ℕ} (i : Fin H) : Fin H := ⟨i.val-1, by have := i.isLt; omega⟩

private theorem count_zeroVal {H : ℕ} (flag : Fin H → Bool) (i : Fin H) (h : i.val=0) :
    count flag i = 0 := by
  have emp : Finset.Iio i = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have lt : t < i := Finset.mem_Iio.mp ht
    change t.val < i.val at lt
    omega
  simp [count,emp]

private theorem count_next {H : ℕ} (flag : Fin H → Bool) (i : Fin H) (hi : i.val≠0) :
    count flag i = count flag (prev i) + (flag (prev i)).toNat := by
  have step : Finset.Iio i = insert (prev i) (Finset.Iio (prev i)) := by
    ext t
    simp only [Finset.mem_Iio, Finset.mem_insert, Fin.ext_iff, Fin.lt_def, prev]
    omega
  unfold count
  rw [step,Finset.filter_insert]
  have fresh : prev i ∉ (Finset.Iio (prev i)).filter (fun t => flag t = true) :=
    fun h => (lt_irrefl _) (Finset.mem_Iio.mp (Finset.mem_filter.mp h).1)
  cases flag (prev i) <;> simp [fresh]

private abbrev Gate (H n : ℕ) := (Fin H) ⊕ ((Fin H × Fin n) ⊕ (Fin H × Fin n))
private def arity {H n : ℕ} : Gate H n → ℕ
  | .inl _ => 2
  | .inr _ => 3

private def wire (H n : ℕ) (g : Gate H n) : Fin (arity g) → Pin H n ⊕ Hidden H n :=
  match g with
  | .inl i => ![.inr (i,0), .inl (.inl (prev i))]
  | .inr (.inl (i,j)) => ![.inr (i,j.succ), .inl (.inr (prev i,j)), .inr (i,j.castSucc)]
  | .inr (.inr (i,j)) => ![.inl (.inr (i,j)), .inl (.inr (prev i,j)), .inr (i,j.castSucc)]

private def test {H n : ℕ} : (g : Gate H n) → (Fin (arity g) → Bool) → Prop
  | .inl _, b => b (0 : Fin 2) = b (1 : Fin 2)
  | .inr (.inl _), b => b (0 : Fin 3) = (b (1 : Fin 3) && b (2 : Fin 3))
  | .inr (.inr (i,_)), b => b (0 : Fin 3) = (if i.val=0 then false else b (1 : Fin 3) ^^ b (2 : Fin 3))

/-- An actual fixed network on the flags and proposed rank words. -/
def network (F : Type*) [Zero F] [One F] (H n : ℕ) : BitNetwork F (Fintype.card (Pin H n)) :=
  LocalChecks.network (fun g => Fin (arity g)) (wire H n) test

private def carry {H n : ℕ} (flag : Fin H → Bool) (word : Fin H → Fin n → Bool)
    (i : Fin H) (j : Fin (n+1)) : Bool :=
  BitVec.carry j.val (bitsValue (word (prev i))) 0 (flag (prev i))

private theorem carry_succ {H n : ℕ} (flag : Fin H → Bool) (word : Fin H → Fin n → Bool)
    (i : Fin H) (j : Fin n) :
    carry flag word i j.succ = (word (prev i) j && carry flag word i j.castSucc) := by
  simp only [carry,Fin.val_succ,Fin.val_castSucc,BitVec.carry_succ,bitsValue_bit]
  simp

private theorem add_bit {H n : ℕ} (flag : Fin H → Bool) (word : Fin H → Fin n → Bool)
    (i : Fin H) (j : Fin n) :
    (bitsValue (word (prev i)) + (BitVec.ofBool (flag (prev i))).setWidth n).getLsbD j.val =
    (word (prev i) j ^^ carry flag word i j.castSucc) := by
  rw [← bitsValue_bit (word (prev i)) j]
  simpa [carry] using BitVec.getLsbD_add_add_bool j.isLt
    (bitsValue (word (prev i))) (0 : BitVec n) (flag (prev i))

private theorem next_bit {H n : ℕ} (flag : Fin H → Bool) (i : Fin H) (j : Fin n) :
    words n flag i j = (if i.val=0 then false else
        words n flag (prev i) j ^^ carry flag (words n flag) i j.castSucc) := by
  by_cases hi : i.val=0
  · simp [hi,words,count_zeroVal flag i hi]
  · rw [ite_eq_right hi,←add_bit]
    have h : bitsValue (words n flag (prev i)) = BitVec.ofNat n (count flag (prev i)) :=
      bitsValue_bits _
    rw [h]
    unfold words
    rw [count_next flag i hi]
    congr 1
    cases hflag : flag (prev i) <;> simp [BitVec.ofNat_add,BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide : 0 < 1)]

private abbrev OK {H n : ℕ} (flag : Fin H → Bool) (word : Fin H → Fin n → Bool)
    (h : Hidden H n → Bool) :=
  LocalChecks.Accepts (fun g => Fin (arity g)) (wire H n) test (pins flag word) h

private theorem carries {H n : ℕ} (flag : Fin H → Bool) (word : Fin H → Fin n → Bool)
    (h : Hidden H n → Bool) (ok : OK flag word h) (i : Fin H) (j : Fin (n+1)) :
    h (i,j) = carry flag word i j := by
  induction j using Fin.induction with
  | zero =>
    simpa [carry] using (show h (i,0) = flag (prev i) from ok (.inl i))
  | succ j ih =>
    rw [carry_succ,←ih]
    exact ok (.inr (.inl (i,j)))

private theorem unique_word {H n : ℕ} (flag : Fin H → Bool) (word : Fin H → Fin n → Bool)
    (h : Hidden H n → Bool) (ok : OK flag word h) : word = words n flag := by
  have calcWord (i : Fin H) (j : Fin n) : word i j = (if i.val=0 then false else
      word (prev i) j ^^ carry flag word i j.castSucc) := by
    rw [←carries flag word h ok i j.castSucc]
    exact ok (.inr (.inr (i,j)))
  funext i
  induction hx : i.val using Nat.strong_induction_on generalizing i with
  | h z ih =>
    funext j
    rw [calcWord, next_bit]
    by_cases hi : i.val=0
    · simp [hi]
    · have earlier : (prev i).val < i.val := by change i.val - 1 < i.val; omega
      have prevWord := ih (prev i).val (by omega) (prev i) rfl
      simp only [ite_eq_right hi,carry,prevWord]

theorem network_eval (F : Type*) [CommSemiring F] {H n : ℕ} (flag : Fin H → Bool)
    (word : Fin H → Fin n → Bool) :
    TypedWiring.value (network F H n) (pins flag word) = if word = words n flag then 1 else 0 := by
  suffices result : TypedWiring.value (network F H n) (pins flag word) =
      @ite F (word = words n flag) (Classical.propDecidable _) 1 0 by
    by_cases eq : word = words n flag <;> simpa [eq] using result
  refine LocalChecks.eval_of_unique (F := F) (fun g => Fin (arity g)) (wire H n) test (pins flag word) (word = words n flag) ?_ ?_
  · rintro rfl
    refine ⟨Function.uncurry (carry flag (words n flag)), ?_, ?_⟩
    · intro g
      rcases g with i | ⟨i,j⟩ | ⟨i,j⟩
      · exact BitVec.carry_zero
      · exact carry_succ _ _ _ _
      · exact next_bit _ _ _
    · intro h ok
      funext ⟨i,j⟩
      exact carries _ _ _ ok i j
  · intro h ok
    exact unique_word _ _ _ ok

theorem network_cells (F : Type*) [Zero F] [One F] (H n : ℕ) :
    (network F H n).cells ≤ 40*(H+2*(H*n)) := by
  have bound (g : Gate H n) : Fintype.card (Fin (arity g)) ≤ 3 := by
    rcases g with _ | _ <;> norm_num [arity,Fintype.card_fin]
  have h := LocalChecks.cells_le (F := F) (fun g => Fin (arity g)) (wire H n) test bound
  simpa [network,Gate,Fintype.card_prod,two_mul,Nat.mul_comm,Nat.add_assoc] using h

theorem network_internal (F : Type*) [Zero F] [One F] (H n : ℕ) :
    (network F H n).internal ≤ H*(n+1) + 40*(H+2*(H*n)) := by
  apply (LocalChecks.internal_le_shared_add_cells (F := F) (fun g => Fin (arity g)) (wire H n) test).trans
  simpa only [Hidden,network,Fintype.card_prod,Fintype.card_fin] using Nat.add_le_add_left (network_cells F H n) (H*(n+1))

theorem words_idlePrefix {A : Type*} [Fintype A] {H n : ℕ} (f : A ↪ Fin H) (i : Fin H) (j : Fin n) :
    words n (fun t => decide (t ∉ Set.range f)) i j = (BitVec.ofNat n (idlePrefix f i)).getLsbD j.val := by
  simp only [words,count,idlePrefix,decide_eq_true_eq]

end
end ThreeFlat.Routing.CallPool.CallTagPrefix

end OAI
