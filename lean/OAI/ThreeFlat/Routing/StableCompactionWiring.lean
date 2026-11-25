import OAI.ThreeFlat.Routing.PackedRows
import OAI.ThreeFlat.Routing.SwitchPins
import OAI.ThreeFlat.LocalTableNetwork
import OAI.ThreeFlat.BitNetworkGlue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace OAI
/-! # Wiring a binary record sorter for stable compaction -/

noncomputable section
open scoped Classical BigOperators

namespace ThreeFlat.Routing.StableCompaction.Wiring
open SortNetwork TableCompiler Finset
abbrev width (m : ℕ) := (1 + m) + 1
abbrev rowCount (m : ℕ) := 2^m
private abbrev packed (m : ℕ) := Fintype.card (Payload m (width m))
private abbrev pins (m : ℕ) := rowCount m + (rowCount m + rowCount m)
private abbrev hidden (m : ℕ) := rowCount m + packed m
private abbrev Gate (m : ℕ) := Option (Fin (rowCount m))

/-- Low bit, source address, and high inactive flag. -/
def word {m : ℕ} (off X : Fin (rowCount m) → Bool) (i : Fin (rowCount m)) :
    Fin (width m) → Bool :=
  Fin.append (Fin.append (fun _ : Fin 1 => X i) ((addressEquiv m).symm i))
    (fun _ : Fin 1 => off i)

def payload {m : ℕ} (z : Fin (width m) → Bool) : Bool :=
  !(z (Fin.last (1+m))) && z 0

private abbrev arity (m : ℕ) : Gate m → ℕ
  | none => packed m + packed m
  | some _ => 5

private def check (z : Fin 5 → Bool) : Prop :=
  z 0 = !(z 1) ∧ z 4 = (!(z 2) && z 3)

private def components {K : Type*} [Zero K] [One K] {m : ℕ}
    (S : BitNetwork K (packed m + packed m)) (g : Gate m) : BitNetwork K (arity m g) :=
  match g with
  | none => S
  | some _ => localTableNetwork (fun z => if check z then 1 else 0)

private abbrev Src (m : ℕ) := BitSource (hidden m) (pins m)

private def offSrc {m} (i : Fin (rowCount m)) : Src m := .hidden (i.castAdd (packed m))

private def outSrc {m} (i : Fin (rowCount m)) (j : Fin (width m)) : Src m :=
  .hidden ((Fintype.equivFin (Payload m (width m)) (i,j)).natAdd (rowCount m))

private def wordSrc {m} (i : Fin (rowCount m)) : Fin (width m) → Src m :=
  Fin.append (Fin.append (fun _ : Fin 1 => .pin ((i.castAdd _).natAdd (rowCount m)))
    (fun j => .constant ((addressEquiv m).symm i j))) (fun _ : Fin 1 => offSrc i)

private def wire (m : ℕ) (g : Gate m) : Fin (arity m g) → Src m :=
  match g with
  | none => Fin.append (fun j => Function.uncurry wordSrc ((Fintype.equivFin (Payload m (width m))).symm j))
      (fun j => .hidden (j.natAdd (rowCount m)))
  | some i => ![offSrc i, .pin (i.castAdd _), outSrc i (Fin.last (1+m)), outSrc i 0,
      .pin ((i.natAdd (rowCount m)).natAdd (rowCount m))]

/-- Apply a binary record sorter and extract the active payloads from its output. -/
def network {K : Type*} [Zero K] [One K] {m : ℕ} (S : BitNetwork K (packed m + packed m)) :
    BitNetwork K (pins m) := BitNetwork.glue (components S) (wire m)

theorem network_cells {K : Type*} [Zero K] [One K] {m : ℕ} (S : BitNetwork K (packed m + packed m)) :
    (network S).cells = S.cells + rowCount m * 224 := by
  simp [network, components, arity, Fintype.sum_option, localTableNetwork_cells, Nat.add_comm]

theorem network_internal {K : Type*} [Zero K] [One K] {m : ℕ} (S : BitNetwork K (packed m + packed m)) :
    (network S).internal = (rowCount m + packed m) + (S.internal + rowCount m * 192) := by
  simp [network, components, hidden, arity, Fintype.sum_option, localTableNetwork_internal, Nat.add_comm]

private def disabled {m : ℕ} (a : Fin (hidden m) → Bool) (i : Fin (rowCount m)) : Bool :=
  a (i.castAdd (packed m))
private def output {m : ℕ} (a : Fin (hidden m) → Bool) (i : Fin (rowCount m)) (j : Fin (width m)) : Bool :=
  a ((Fintype.equivFin (Payload m (width m)) (i,j)).natAdd (rowCount m))

private theorem read_wordSrc {m} (M X Y : Fin (rowCount m) → Bool) (a : Fin (hidden m) → Bool)
    (i : Fin (rowCount m)) (t : Fin (width m)) :
    (wordSrc i t).read a (Fin.append M (Fin.append X Y)) = word (disabled a) X i t := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) t
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j <;> simp [wordSrc, word, BitSource.read]
  · simp [wordSrc, word, offSrc, BitSource.read, disabled]

private theorem read_sort {m} (M X Y : Fin (rowCount m) → Bool) (a : Fin (hidden m) → Bool) :
    (fun t => (wire m none t).read a (Fin.append M (Fin.append X Y))) =
      Fin.append (pack (word (disabled a) X)) (pack (output a)) := by
  funext t
  refine Fin.addCases (fun j => ?_) (fun j => ?_) t
  · simpa [wire, pack, Function.uncurry] using read_wordSrc M X Y a
      ((Fintype.equivFin (Payload m (width m))).symm j).1 ((Fintype.equivFin _).symm j).2
  · simp only [wire, Fin.append_right, pack, output, BitSource.read, Function.uncurry,
      Prod.mk.eta, Equiv.apply_symm_apply]

private theorem read_row {m} (M X Y : Fin (rowCount m) → Bool) (a : Fin (hidden m) → Bool)
    (i : Fin (rowCount m)) :
    check (fun t => (wire m (some i) t).read a (Fin.append M (Fin.append X Y))) ↔
      disabled a i = !(M i) ∧ Y i = payload (output a i) := by
  change (disabled a i = !(Fin.append M (Fin.append X Y) (i.castAdd _)) ∧
    Fin.append M (Fin.append X Y) ((i.natAdd (rowCount m)).natAdd (rowCount m)) =
      payload (output a i)) ↔ _
  simp only [Fin.append_left, Fin.append_right]

private def guess {m} (off : Fin (rowCount m) → Bool) (Z : Records m (width m)) :
    Fin (hidden m) → Bool := Fin.append off (pack Z)

@[simp] private theorem disabled_guess {m} (off : Fin (rowCount m) → Bool) (Z : Records m (width m)) :
    disabled (guess off Z) = off := by ext i; simp [disabled, guess]

@[simp] private theorem output_guess {m} (off : Fin (rowCount m) → Bool) (Z : Records m (width m)) :
    output (guess off Z) = Z := by ext i j; simp [output, guess, pack]

private theorem guess_recover {m : ℕ} (a : Fin (hidden m) → Bool) :
    guess (disabled a) (output a) = a := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [guess, disabled, pack, output, Function.uncurry]

private theorem prod_ite {I K : Type*} [Fintype I] [CommSemiring K] (p : I → Prop) [DecidablePred p] :
    (∏ i, (if p i then 1 else 0 : K)) = if ∀ i, p i then 1 else 0 := by
  by_cases h : ∀ i, p i
  · simp [h]
  · obtain ⟨i, hi⟩ := Classical.not_forall.mp h
    have zero : (∏ j, (if p j then 1 else 0 : K)) = 0 :=
      prod_eq_zero (mem_univ i) (by simp [hi])
    simpa [h] using zero

theorem network_eval {K : Type*} [CommSemiring K] {m : ℕ}
    (S : BitNetwork K (packed m + packed m)) (sort : Records m (width m) → Records m (width m))
    (hS : ∀ A B, S.eval (Fin.append (pack A) (pack B)) = if B = sort A then 1 else 0)
    (M X Y : Fin (rowCount m) → Bool) :
    (network S).eval (Fin.append M (Fin.append X Y)) =
      if Y = (fun i => payload (sort (word (fun i => !(M i)) X) i)) then 1 else 0 := by
  let off := fun i => !(M i)
  let Z := sort (word off X)
  let a₀ := guess off Z
  let pins' := Fin.append M (Fin.append X Y)
  let accepts (a : Fin (hidden m) → Bool) :=
    output a = sort (word (disabled a) X) ∧ ∀ i, disabled a i = !(M i) ∧ Y i = payload (output a i)
  have weight (a : Fin (hidden m) → Bool) :
      (∏ g, (components S g).eval (fun t => (wire m g t).read a pins')) = if accepts a then 1 else 0 := by
    rw [Fintype.prod_option]
    have cells (i : Fin (rowCount m)) : (components S (some i)).eval
        (fun t => (wire m (some i) t).read a pins') =
        (if disabled a i = !(M i) ∧ Y i = payload (output a i) then 1 else 0) := by
      dsimp only [components, pins']
      rw [localTableNetwork_eval]
      exact if_congr (read_row M X Y a i) rfl rfl
    simp_rw [cells]
    rw [prod_ite (K := K) (fun i => disabled a i = !(M i) ∧ Y i = payload (output a i))]
    change S.eval _ * _ = _
    rw [show pins' = _ from rfl, read_sort, hS]
    split_ifs <;> simp_all [accepts]
  rw [network, BitNetwork.glue_eval]
  change (∑ a, ∏ g, (components S g).eval (fun t => (wire m g t).read a pins')) = _
  simp_rw [weight]
  rw [sum_eq_single_of_mem a₀ (mem_univ _)]
  · congr 1
    simp only [accepts, a₀, disabled_guess, output_guess, off, Z, true_and, funext_iff, implies_true]
  · intro a _ ne
    suffices ¬ accepts a by simp [this]
    rintro ⟨hZ, hr⟩
    have hd : disabled a = off := funext fun i => (hr i).1
    exact ne <| (guess_recover a).symm.trans (by rw [hd, hZ, hd])

end ThreeFlat.Routing.StableCompaction.Wiring

end
end OAI
