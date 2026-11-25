import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.ThreeFlat.Diagonal.TraceSlotOrder
import Mathlib.Data.List.ChainOfFn

namespace OAI
/-! # Boolean checks on adjacent sorted memory records -/

namespace ThreeFlat.Diagonal.TraceAdjacent

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization Computability.VPVNP.RAMMemory
open Computability.VPVNP.VerifierNetwork (Frame)
open TraceWords

variable {σ : Type*} {w : ℕ}

/-- The five words consulted by the physical predecessor test. The current
kind has code one for reads. All payload words of an empty slot are zero. -/
structure PairWords (α : Type*) where
  kind : α
  address : α
  value : α
  previousAddress : α
  previousValue : α

/-- Physical words of the predecessor and the current slot. -/
def pairWords (previous current : Option (WordRecord w)) : PairWords (Word w) where
  kind := current.elim 0 (fun r => Fin.ofNat _ r.kind.code)
  address := current.elim 0 WordRecord.address
  value := current.elim 0 WordRecord.value
  previousAddress := previous.elim 0 WordRecord.address
  previousValue := previous.elim 0 WordRecord.value

private def literals (v : Word w) (j : Fin w) : Expr σ := .const (bits v j)

/-- Test the read kind, then select the prior cell value or the zero initial
value using address equality. -/
def check (p : PairWords (Fin w → Expr σ)) : Expr σ :=
  .or (.not (sameWord p.kind (literals 1)))
    (Expr.mux (sameWord p.previousAddress p.address)
      (sameWord p.value p.previousValue) (sameWord p.value (literals 0)))

/-- A circuit input may be any five locally addressed slices of its wires. -/
def Represents (p : PairWords (Fin w → Expr σ)) (x : σ → Bool) (d : PairWords (Word w)) : Prop :=
  (∀ j, (p.kind j).eval x = bits d.kind j) ∧
  (∀ j, (p.address j).eval x = bits d.address j) ∧
  (∀ j, (p.value j).eval x = bits d.value j) ∧
  (∀ j, (p.previousAddress j).eval x = bits d.previousAddress j) ∧
  (∀ j, (p.previousValue j).eval x = bits d.previousValue j)

theorem check_at (p : PairWords (Fin w → Expr σ)) (x : σ → Bool) (d : PairWords (Word w))
    (h : Represents p x d) :
    (check p).eval x = true ↔
      (d.kind = 1 → d.value = if d.previousAddress = d.address then d.previousValue else 0) := by
  obtain ⟨hk, ha, hv, hp, hvp⟩ := h
  have k := sameWord_at p.kind (literals 1) x hk (fun _ => rfl)
  have a := sameWord_at p.previousAddress p.address x hp ha
  have v := sameWord_at p.value p.previousValue x hv hvp
  have z := sameWord_at p.value (literals 0) x hv (fun _ => rfl)
  have k' : (sameWord p.kind (literals 1)).eval x = decide (d.kind = 1) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using k)
  have a' : (sameWord p.previousAddress p.address).eval x =
      decide (d.previousAddress = d.address) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using a)
  by_cases h₁ : d.kind = 1 <;> by_cases h₂ : d.previousAddress = d.address <;>
    simp only [check, Expr.eval, Expr.eval_mux, k', a', h₁, h₂, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.false_or, Bool.true_or, ite_true, ite_false,
      Bool.false_eq_true, true_implies, false_implies, v, z]

/-- On canonical word slots the circuit tests precisely the physical
one-record assertion used by the sorted-memory checker. -/
theorem check_iff_padded (hw : 2 ≤ w) (p : PairWords (Fin w → Expr σ)) (x : σ → Bool)
    (previous current : Option (WordRecord w))
    (h : Represents p x (pairWords previous current)) :
    (check p).eval x = true ↔
      PaddedCheck (previous.map WordRecord.record) [current.map WordRecord.record] := by
  rw [check_at p x _ h]
  have hpow : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have h1 : (1 : ℕ) < 2^w := by omega
  have h2 : (2 : ℕ) < 2^w := by omega
  have zero_ne : (0 : Word w) ≠ 1 := by
    intro e
    have he := congrArg Fin.val e
    change 0 = 1 % 2^w at he
    rw [Nat.mod_eq_of_lt h1] at he
    contradiction
  have two_ne : (Fin.ofNat _ 2 : Word w) ≠ 1 := by
    intro e
    have he := congrArg Fin.val e
    change 2 % 2^w = 1 % 2^w at he
    rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at he
    contradiction
  have kind (k : Kind) : (Fin.ofNat _ k.code : Word w) = 1 ↔ k = .read := by
    cases k
    · simp only [Kind.code, reduceCtorEq, iff_false]
      intro he
      have he' := congrArg Fin.val he
      change 0 % 2^w = 1 % 2^w at he'
      rw [Nat.zero_mod, Nat.mod_eq_of_lt h1] at he'
      contradiction
    · exact iff_of_true rfl rfl
    · simpa only [Kind.code, reduceCtorEq, iff_false] using two_ne
  cases current with
  | none => simp [pairWords, PaddedCheck, zero_ne]
  | some c =>
    cases previous with
    | none =>
      change ((Fin.ofNat _ c.kind.code : Word w) = 1 → _) ↔ _
      rw [kind c.kind]
      by_cases h₀ : (0 : Word w) = c.address <;> simp [pairWords, PaddedCheck, previousValue, WordRecord.record, h₀]
    | some p =>
      change ((Fin.ofNat _ c.kind.code : Word w) = 1 → _) ↔ _
      rw [kind c.kind]
      by_cases ha : p.address = c.address <;> simp [pairWords, PaddedCheck, previousValue, WordRecord.record, Fin.val_inj, ha]

/-- A linear gate bound when each addressed input expression has size at most
one; this covers both direct wire references and constants. -/
theorem check_size (p : PairWords (Fin w → Expr σ)) (hk : ∀ j, (p.kind j).size ≤ 1)
    (ha : ∀ j, (p.address j).size ≤ 1) (hv : ∀ j, (p.value j).size ≤ 1)
    (hp : ∀ j, (p.previousAddress j).size ≤ 1) (hvp : ∀ j, (p.previousValue j).size ≤ 1) :
    (check p).size ≤ 50*w+11 := by
  have hl (v : Word w) (j : Fin w) : (literals (σ := σ) v j).size ≤ 1 := by rfl
  have h₁ := sameWord_size_le _ _ hk (hl 1)
  have h₂ := sameWord_size_le _ _ hp ha
  have h₃ := sameWord_size_le _ _ hv hvp
  have h₄ := sameWord_size_le _ _ hv (hl 0)
  simp only [check, Expr.mux, Expr.size]
  omega

/-- Bind the two records to named local wires. -/
def addressed (wires : PairWords (Fin w → σ)) : PairWords (Fin w → Expr σ) :=
  ⟨.input ∘ wires.kind, .input ∘ wires.address, .input ∘ wires.value,
   .input ∘ wires.previousAddress, .input ∘ wires.previousValue⟩

noncomputable def frame [Fintype σ] (wires : PairWords (Fin w → σ)) : Frame σ Unit :=
  (Frame.initial (id : σ → σ)).step (fun _ => check (addressed wires))

theorem circuit_eval [Fintype σ] (hw : 2 ≤ w) (wires : PairWords (Fin w → σ))
    (x : σ → Bool) (previous current : Option (WordRecord w))
    (h : Represents (addressed wires) x (pairWords previous current)) :
    ((frame wires).circuit ()).eval x = true ↔
      PaddedCheck (previous.map WordRecord.record) [current.map WordRecord.record] := by
  have e : (Frame.initial (id : σ → σ)).eval x = x := funext fun _ => by simp
  simpa [frame, e] using check_iff_padded hw (addressed wires) x previous current h

theorem circuitSize_le [Fintype σ] (wires : PairWords (Fin w → σ)) :
    (frame wires).circuitSize () ≤ 4*(50*w+11) := by
  apply ((frame wires).circuitSize_le ()).trans
  apply Nat.mul_le_mul_left
  have h := check_size (addressed wires) (fun _ => by rfl) (fun _ => by rfl)
    (fun _ => by rfl) (fun _ => by rfl) (fun _ => by rfl)
  simpa [frame] using (Frame.initial (id : σ → σ)).step_size_le
    (fun _ : Unit => check (addressed wires)) (50*w+11) (fun _ => h)

/-- Read the address, kind and value at their offsets in each seven-word sorting key. -/
def slices {α : Type*} (previous current : Fin 7 → α) : PairWords α :=
  ⟨current 5, current 1, current 6, previous 1, previous 6⟩

theorem slices_fields (hw : 2 ≤ w) (previous current : Option (WordRecord w)) :
    slices (TraceSlots.fields hw previous) (TraceSlots.fields hw current) =
      pairWords previous current := by
  have h4 : 4 ≤ 2^w := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  have tag (n : Fin 4) : TraceSlots.small hw n = Fin.ofNat _ n.val :=
    Fin.ext ((Nat.mod_eq_of_lt (n.isLt.trans_le h4)).symm)
  cases previous <;> cases current
    <;> simp only [slices, TraceSlots.fields, pairWords, Option.elim, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    <;> first | rfl | rename_i c; cases hk : c.kind <;> simp [Kind.code, tag]

theorem represents_slices (hw : 2 ≤ w) (x : σ → Bool)
    (previous current : Option (WordRecord w)) (a b : Fin 7 → Fin w → Expr σ)
    (ha : ∀ f j, (a f j).eval x = bits (TraceSlots.fields hw previous f) j)
    (hb : ∀ f j, (b f j).eval x = bits (TraceSlots.fields hw current f) j) :
    Represents (slices a b) x (pairWords previous current) := by
  rw [← slices_fields hw]
  exact ⟨hb 5, hb 1, hb 6, ha 1, ha 6⟩

/-- On a nonempty array, the first test uses the incoming record. The tests
on all successive wires use exactly the preceding physical slot, including
the padding case. -/
theorem paddedCheck_cons (previous cur : Option (Record (Word w)))
    (rest : List (Option (Record (Word w)))) :
    PaddedCheck previous (cur :: rest) ↔ PaddedCheck previous [cur] ∧ PaddedCheck cur rest := by
  cases cur <;> simp [PaddedCheck]

private theorem padded_chain (previous : Option (Record (Word w)))
    (slots : List (Option (Record (Word w)))) :
    PaddedCheck previous slots ↔
      (previous :: slots).IsChain (fun a b => PaddedCheck a [b]) := by
  induction slots generalizing previous with
  | nil => simp [PaddedCheck]
  | cons s t ih => rw [paddedCheck_cons, List.isChain_cons_cons, ih]

/-- Adjoin the incoming slot to index adjacent pairs uniformly. -/
def withPrevious {α : Type*} {n : ℕ} (a : α) (s : Fin n → α) : Fin (n+1) → α :=
  Fin.cons a s

/-- Array-local form, with the supplied incoming record preceding the first wire. -/
theorem padded_ofFn_iff {n : ℕ} (previous : Option (Record (Word w)))
    (slots : Fin n → Option (Record (Word w))) :
    PaddedCheck previous (List.ofFn slots) ↔
      ∀ i : Fin n, PaddedCheck (withPrevious previous slots i.castSucc) [slots i] := by
  rw [padded_chain, ← List.ofFn_cons, List.isChain_ofFn]
  constructor
  · intro h i
    exact h i.val (Nat.succ_lt_succ i.isLt)
  · intro h i hi
    exact h ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Check each pair of addressed records in parallel, followed by one AND tree. -/
noncomputable def arrayFrame [Fintype σ] {n : ℕ} (wires : Fin n → PairWords (Fin w → σ)) :
    Frame σ Unit :=
  ((Frame.initial (id : σ → σ)).step (fun i => check (addressed (wires i)))).step
    (fun _ => allBits fun i => .input i)

theorem arrayCircuit_eval [Fintype σ] {n : ℕ} (hw : 2 ≤ w)
    (wires : Fin n → PairWords (Fin w → σ)) (x : σ → Bool)
    (previous : Option (WordRecord w)) (slots : Fin n → Option (WordRecord w))
    (h : ∀ i, Represents (addressed (wires i)) x
      (pairWords (withPrevious previous slots i.castSucc) (slots i))) :
    ((arrayFrame wires).circuit ()).eval x = true ↔
      PaddedCheck (previous.map WordRecord.record) (List.ofFn fun i => (slots i).map WordRecord.record) := by
  have e : (Frame.initial (id : σ → σ)).eval x = x := funext fun _ => by simp
  simp only [arrayFrame, Frame.circuit_eval, Frame.step_eval, allBits_true, Expr.eval, e,
    padded_ofFn_iff]
  apply forall_congr'
  intro i
  have hprev : (withPrevious previous slots i.castSucc).map WordRecord.record =
      withPrevious (previous.map WordRecord.record) (fun j => (slots j).map WordRecord.record)
        i.castSucc := by
    generalize i.castSucc = j
    induction j using Fin.cases <;> simp [withPrevious]
  simpa [hprev] using check_iff_padded hw (addressed (wires i)) x _ _ (h i)

theorem arrayCircuitSize_le [Fintype σ] {n : ℕ} (wires : Fin n → PairWords (Fin w → σ)) :
    (arrayFrame wires).circuitSize () ≤ 4 * (n*(50*w+11) + 2*n+1) := by
  apply ((arrayFrame wires).circuitSize_le ()).trans
  apply Nat.mul_le_mul_left
  let f := (Frame.initial (id : σ → σ)).step (fun i => check (addressed (wires i)))
  have hf : f.size ≤ n*(50*w+11) := by
    simpa [f] using (Frame.initial (id : σ → σ)).step_size_le
      (fun i => check (addressed (wires i))) (50*w+11) (fun i =>
        check_size _ (fun _ => by rfl) (fun _ => by rfl) (fun _ => by rfl)
          (fun _ => by rfl) (fun _ => by rfl))
  have H : (allBits (fun i : Fin n => .input i)).size ≤ n*2+1 :=
    allBits_size_le _ (s := 1) fun _ => by rfl
  have hf' := f.step_size_le (fun _ : Unit => allBits fun i => .input i) (n*2+1) fun _ => H
  change (f.step _).size ≤ _
  simp only [Fintype.card_unit, Nat.one_mul] at hf'
  omega

end ThreeFlat.Diagonal.TraceAdjacent

end OAI
