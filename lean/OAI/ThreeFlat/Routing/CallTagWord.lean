import OAI.ThreeFlat.Routing.CallTagPrefix
import OAI.ThreeFlat.Routing.LocalChecksSize
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Canonical words for occupied and unused call positions -/

namespace ThreeFlat.Routing.CallPool.CallTagWord

open scoped Classical
noncomputable section

abbrev Field (d n : ℕ) := Option (Fin d ⊕ Fin n)

def addr (d n : ℕ) : Field d n ≃ Fin (1+d+n) :=
  Fintype.equivFinOfCardEq (by simp [Field]; omega)

private def bit {d n : ℕ} (active data : Bool) : Field d n → Bool
  | none => active
  | some (.inl _) => active && data
  | some (.inr _) => !active && data

/-- Inactive identifier fields and active rank fields are cleared. -/
def word {d n : ℕ} (active : Bool) (id : Fin d → Bool) (rank : Fin n → Bool) :
    Fin (1+d+n) → Bool := fun j =>
  let f := (addr d n).symm j
  bit active (f.elim active (Sum.elim id rank)) f

private theorem word_flag {d n : ℕ} (a : Bool) (x : Fin d → Bool) (y : Fin n → Bool) :
    word a x y (addr d n none) = a := by simp [word,bit]

private theorem word_id {d n : ℕ} (a : Bool) (x : Fin d → Bool) (y : Fin n → Bool) (i : Fin d) :
    word a x y (addr d n (some (.inl i))) = (a && x i) := by simp [word,bit]

private theorem word_rank {d n : ℕ} (a : Bool) (x : Fin d → Bool) (y : Fin n → Bool) (i : Fin n) :
    word a x y (addr d n (some (.inr i))) = (!a && y i) := by simp [word,bit]

/-- Active identifiers and idle ranks use disjoint fixed-width encodings. -/
def code (d n : ℕ) : ((Fin d → Bool) ⊕ Fin (2^n)) ↪ (Fin (1+d+n) → Bool) where
  toFun := Sum.elim (fun x => word true x (fun _ => false))
    (fun i => word false (fun _ => false) ((addressEquiv n).symm i))
  inj' := by
    rintro (x | i) (y | j) e
    · apply congrArg Sum.inl
      funext t
      simpa only [Sum.elim_inl,word_id,Bool.true_and] using congrFun e (addr d n (some (.inl t)))
    · have h := congrFun e (addr d n none)
      simp only [Sum.elim_inl,Sum.elim_inr,word_flag] at h
      contradiction
    · have h := congrFun e (addr d n none)
      simp only [Sum.elim_inl,Sum.elim_inr,word_flag] at h
      contradiction
    · apply congrArg Sum.inr
      apply (addressEquiv n).symm.injective
      funext t
      simpa only [Sum.elim_inr,word_rank,Bool.not_false,Bool.true_and] using congrFun e (addr d n (some (.inr t)))

@[simp] theorem code_left {d n : ℕ} (v : Fin d → Bool) :
    code d n (Sum.inl v) = word true v (fun _ => false) := rfl

@[simp] theorem code_right {d n : ℕ} (v : Fin (2^n)) :
    code d n (Sum.inr v) = word false (fun _ => false) ((addressEquiv n).symm v) := rfl

/-- The physical mask and verified prefix counters realize the abstract unit labels. -/
theorem word_unitLabel {A : Type*} [Fintype A] {n d : ℕ} (ids : A ↪ (Fin d → Bool)) (f : A ↪ Fin (2^n))
    (id : Fin (2^n) → Fin d → Bool) (live : ∀ a, id (f a) = ids a) (i : Fin (2^n)) :
    word (decide (i ∈ Set.range f)) (id i) (CallTagPrefix.words n (fun t => decide (t ∉ Set.range f)) i) =
      code d n (unitLabel ids f i) := by
  funext k
  obtain ⟨j,rfl⟩ := (addr d n).surjective k
  by_cases hi : i ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hi
    have on : f a ∈ Set.range f := ⟨a,rfl⟩
    rcases j with _ | (q | q) <;> simp [on,word_flag,word_id,word_rank,live]
  · rw [show unitLabel ids f i = Sum.inr ⟨idlePrefix f i,(idlePrefix_le f i).trans_lt i.isLt⟩ by
      simp [unitLabel,hi]]
    have bound := (idlePrefix_le f i).trans_lt i.isLt
    have inactive : decide (i ∈ Set.range f) = false := by simp [hi]
    rcases j with _ | (q | q)
    · simp only [inactive,code_right,word_flag]
    · simp only [inactive,code_right,word_id,Bool.false_and]
    simp only [inactive,code_right,word_rank,Bool.not_false,Bool.true_and]
    rw [CallTagPrefix.words_idlePrefix]
    apply congrArg (fun z : BitVec n => z.getLsbD q.val)
    apply BitVec.eq_of_toNat_eq
    exact Nat.mod_eq_of_lt bound

abbrev Pin (H d n : ℕ) := Fin H ⊕ ((Fin H × Fin d) ⊕ ((Fin H × Fin n) ⊕ (Fin H × Fin (1+d+n))))

def pins {H d n : ℕ} (active : Fin H → Bool) (id : Fin H → Fin d → Bool)
    (rank : Fin H → Fin n → Bool) (out : Fin H → Fin (1+d+n) → Bool) : Pin H d n → Bool :=
  Sum.elim active (Sum.elim (Function.uncurry id) (Sum.elim (Function.uncurry rank) (Function.uncurry out)))

private def wire {H d n : ℕ} (g : Fin H × Field d n) : Fin 3 → Pin H d n ⊕ Empty :=
  ![.inl (.inl g.1), .inl (g.2.elim (.inl g.1) (Sum.elim
      (fun j => .inr (.inl (g.1,j))) (fun j => .inr (.inr (.inl (g.1,j)))))),
    .inl (.inr (.inr (.inr (g.1,addr d n g.2))))]

private def test {H d n : ℕ} (g : Fin H × Field d n) (a : Fin 3 → Bool) : Prop :=
  a 2 = bit (a 0) (a 1) g.2

def network (F : Type*) [Zero F] [One F] (H d n : ℕ) : BitNetwork F (Fintype.card (Pin H d n)) :=
  LocalChecks.network (fun _ : Fin H × Field d n => Fin 3) wire test

theorem network_eval (F : Type*) [CommSemiring F] {H d n : ℕ} (active : Fin H → Bool)
    (id : Fin H → Fin d → Bool) (rank : Fin H → Fin n → Bool) (out : Fin H → Fin (1+d+n) → Bool) :
    TypedWiring.value (network F H d n) (pins active id rank out) =
      if out = fun i => word (active i) (id i) (rank i) then 1 else 0 := by
  rw [network,LocalChecks.eval,Fintype.sum_unique]
  congr 1
  apply propext
  constructor
  · intro h
    funext i j
    obtain ⟨f,rfl⟩ := (addr d n).surjective j
    have check := h (i,f)
    rcases f with _ | (k | k) <;>
      simpa [test,wire,pins,word,bit] using check
  · rintro rfl ⟨i,f⟩
    rcases f with _ | (k | k) <;> simp [test,wire,pins,word,bit]

theorem network_cells (F : Type*) [Zero F] [One F] (H d n : ℕ) :
    (network F H d n).cells ≤ 40*(H*(1+d+n)) := by
  have h := LocalChecks.cells_le (F := F) (fun _ : Fin H × Field d n => Fin 3) wire test
    (d := 3) (fun _ => by simp)
  simpa [network,Field,Fintype.card_prod,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,mul_comm] using h

theorem network_internal (F : Type*) [Zero F] [One F] (H d n : ℕ) :
    (network F H d n).internal ≤ (network F H d n).cells := by
  simpa [network] using LocalChecks.internal_le_shared_add_cells (F := F)
    (fun _ : Fin H × Field d n => Fin 3) wire test

end
end ThreeFlat.Routing.CallPool.CallTagWord

end OAI
