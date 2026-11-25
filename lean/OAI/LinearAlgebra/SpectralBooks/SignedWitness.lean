import OAI.LinearAlgebra.SpectralBooks.MachinePadding
import OAI.LinearAlgebra.SpectralBooks.MachineLookup
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The signed universal witness polynomial

Section 2 of *An explicit VNP family requires superpolynomial border circuit size over
every field* leaves the choice of a self-delimiting binary encoding of multitape programs
open. Here the header `1^k 0` gives the length of the program body. Within the body, all
natural numbers use unary notation with a zero terminator. The body gives the number of
work tapes, the number of transition rules, and the rules themselves. An instruction
contains precisely one work-tape entry per tape. This is a finite transition table that a
universal machine can scan at each simulated step.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open SignedMachine

namespace ProgramCode

private abbrev Parser := StateT (List Bool) Option

/-- The code for a natural number is a run of ones followed by a zero. -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

private def readNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: tail => some (0, tail)
  | true :: tail => do
    let (n, rest) ← readNat tail
    pure (n + 1, rest)

private def natField : Parser ℕ := readNat

private def readFields {α : Type} (field : Parser α) : ℕ → Parser (List α)
  | 0 => pure []
  | n + 1 => do
    let a ← field
    let rest ← readFields field n
    pure (a :: rest)

private def three {α : Type} (a b c : α) : Parser α := do
  match ← natField with
  | 0 => pure a
  | 1 => pure b
  | 2 => pure c
  | _ => failure

private def symbol : Parser Symbol := three .blank .zero .one
private def direction : Parser Direction := three .left .stay .right

private def transition (tapes : ℕ) : Parser Transition := do
  let state ← natField
  let move ← direction
  let tapeMoves ← readFields (Prod.mk <$> symbol <*> direction) tapes
  pure ⟨state, move, tapeMoves⟩

private def action (tapes : ℕ) : Parser Action := do
  match ← natField with
  | 0 => return .halt (← three .zero .pos .neg)
  | 1 => return .step (← transition tapes)
  | 2 => return .branch (← transition tapes) (← transition tapes)
  | _ => failure

private def rule (tapes : ℕ) : Parser Rule := do
  return ⟨← natField, ← symbol, ← readFields symbol tapes, ← action tapes⟩

private def table (tapes : ℕ) : Parser (List Rule) := do
  let count ← natField
  let rules ← readFields (rule tapes) count
  guard (rules.map (fun r => (r.state, r.inputSymbol, r.workSymbols))).Nodup
  pure rules

/-- Check that the entire program body is one well-formed table. -/
def decodeBody (body : List Bool) : Option Program := do
  let (tapes, fields) ← readNat body
  let (rules, rest) ← (table tapes).run fields
  guard rest.isEmpty
  pure ⟨tapes, rules⟩

/-- Read the initial program while retaining all bits as input to the simulation. -/
def decode (bits : List Bool) : Option Program := do
  let (k, rest) ← readNat bits
  guard (k ≤ rest.length)
  decodeBody (rest.take k)

private theorem readNat_unary_append (n : ℕ) (tail : List Bool) :
    readNat (unary n ++ tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change readNat (true :: (unary n ++ tail)) = _
    simp [readNat, ih]

/-- Appending any data after a framed program preserves the decoded program. -/
theorem decode_frame_append (body data : List Bool) :
    decode (unary body.length ++ (body ++ data)) = decodeBody body := by
  simp [decode, readNat_unary_append]

private def symbolBits : Symbol → List Bool
  | .blank => unary 0
  | .zero => unary 1
  | .one => unary 2

private def directionBits : Direction → List Bool
  | .left => unary 0
  | .stay => unary 1
  | .right => unary 2

private def outputBits : Output → List Bool
  | .zero => unary 0
  | .pos => unary 1
  | .neg => unary 2

private def moveBits (m : Symbol × Direction) : List Bool := symbolBits m.1 ++ directionBits m.2

private def transitionBits (t : Transition) : List Bool :=
  unary t.state ++ directionBits t.inputMove ++ t.workMoves.flatMap moveBits

private def actionBits : Action → List Bool
  | .halt out => unary 0 ++ outputBits out
  | .step t => unary 1 ++ transitionBits t
  | .branch s t => unary 2 ++ transitionBits s ++ transitionBits t

private def ruleBits (r : Rule) : List Bool :=
  unary r.state ++ symbolBits r.inputSymbol ++ r.workSymbols.flatMap symbolBits ++ actionBits r.action

private def bodyBits (p : Program) : List Bool :=
  unary p.workTapes ++ unary p.table.length ++ p.table.flatMap ruleBits

/-- Write a self-delimiting program prefix. -/
def encode (p : Program) : List Bool := unary (bodyBits p).length ++ bodyBits p

/-- Each transition acts on exactly the specified number of work tapes. -/
def ActionArity (k : ℕ) : Action → Prop
  | .halt _ => True
  | .step t => t.workMoves.length = k
  | .branch s t => s.workMoves.length = k ∧ t.workMoves.length = k

/-- A deterministic transition-table lookup, with one test and one update per work tape. -/
def WellFormed (p : Program) : Prop :=
  (p.table.map (fun r => (r.state, r.inputSymbol, r.workSymbols))).Nodup ∧
  ∀ r ∈ p.table, r.workSymbols.length = p.workTapes ∧ ActionArity p.workTapes r.action

private abbrev Reads {α : Type} (f : Parser α) (bits : List Bool) (a : α) : Prop :=
  ∀ rest, f.run (bits ++ rest) = some (a, rest)

private theorem reads_nat (n : ℕ) (rest : List Bool) :
    natField.run (unary n ++ rest) = some (n, rest) := readNat_unary_append n rest

private theorem reads_symbol (s : Symbol) : Reads symbol (symbolBits s) s := by
  cases s <;> exact fun _ => rfl

private theorem reads_direction (d : Direction) : Reads direction (directionBits d) d := by
  cases d <;> exact fun _ => rfl

private theorem reads_output (o : Output) : Reads (three .zero .pos .neg) (outputBits o) o := by
  cases o <;> exact fun _ => rfl

private theorem reads_fields {α : Type} {field : Parser α} {bits : α → List Bool} (xs : List α)
    (h : ∀ x ∈ xs, Reads field (bits x) x) :
    Reads (readFields field xs.length) (xs.flatMap bits) xs := by
  induction xs with
  | nil => exact fun _ => rfl
  | cons x xs ih =>
    intro rest
    simp [readFields, List.append_assoc, StateT.run_bind, h x (by simp),
      ih (fun a ha => h a (by simp [ha]))]

private theorem reads_move (m : Symbol × Direction) :
    Reads (Prod.mk <$> symbol <*> direction) (moveBits m) m := by
  intro rest
  simp [moveBits, List.append_assoc, StateT.run_seq, StateT.run_map, reads_symbol,
    reads_direction]

private theorem reads_transition {k : ℕ} (t : Transition) (ht : t.workMoves.length = k) :
    Reads (transition k) (transitionBits t) t := by
  subst k
  intro rest
  simp [transition, transitionBits, List.append_assoc, StateT.run_bind, reads_nat,
    reads_direction, reads_fields _ (fun x _ => reads_move x)]

private theorem reads_action {k : ℕ} (a : Action) (ha : ActionArity k a) :
    Reads (action k) (actionBits a) a := by
  intro rest
  cases a with
  | halt o =>
    simp [action, actionBits, List.append_assoc, StateT.run_bind, reads_nat,
      reads_output]
  | step t =>
    simp [action, actionBits, List.append_assoc, StateT.run_bind, reads_nat,
      reads_transition t ha]
  | branch s t =>
    simp [action, actionBits, List.append_assoc, StateT.run_bind, reads_nat,
      reads_transition s ha.1, reads_transition t ha.2]

private theorem reads_rule {k : ℕ} (r : Rule)
    (hr : r.workSymbols.length = k ∧ ActionArity k r.action) :
    Reads (rule k) (ruleBits r) r := by
  obtain ⟨rfl, ha⟩ := hr
  intro rest
  simp [rule, ruleBits, List.append_assoc, StateT.run_bind, reads_nat,
    reads_symbol, reads_fields _ (fun x _ => reads_symbol x), reads_action r.action ha]

/-- Every well-formed program is represented and can be followed by arbitrary input data. -/
theorem decode_encode_append (p : Program) (hp : WellFormed p) (data : List Bool) :
    decode (encode p ++ data) = some p := by
  have ht := reads_fields p.table (fun r hr => reads_rule r (hp.2 r hr)) []
  simp only [List.append_nil] at ht
  rw [encode, List.append_assoc, decode_frame_append]
  simp [decodeBody, bodyBits, List.append_assoc, readNat_unary_append, table, reads_nat,
    StateT.run_bind, ht, hp.1]

private theorem readNat_length {bits rest : List Bool} {k : ℕ}
    (h : readNat bits = some (k, rest)) : k + 1 + rest.length = bits.length := by
  induction bits generalizing k rest with
  | nil => simp [readNat] at h
  | cons b bs ih =>
    cases b with
    | false =>
      obtain ⟨rfl, rfl⟩ := (by simpa [readNat] using h : 0 = k ∧ bs = rest)
      simp [Nat.add_comm]
    | true =>
      cases h' : readNat bs with
      | none => simp [readNat, h'] at h
      | some pair =>
        obtain ⟨m, tail⟩ := pair
        simp [readNat, h'] at h
        have := ih h'
        obtain ⟨rfl, rfl⟩ := h
        simp
        omega

private theorem readFields_length {α : Type} (field : Parser α) {n : ℕ}
    {bits rest : List Bool} {xs : List α}
    (h : (readFields field n).run bits = some (xs, rest)) : xs.length = n := by
  induction n generalizing bits xs with
  | zero =>
    change some ([], bits) = some (xs, rest) at h
    cases h
    rfl
  | succ n ih =>
    change (do
      let (a, mid) ← field.run bits
      let (ys, tail) ← (readFields field n).run mid
      return (a :: ys, tail)) = _ at h
    cases he : field.run bits with
    | none => simp [he] at h
    | some pair =>
      obtain ⟨a, mid⟩ := pair
      cases hy : (readFields field n).run mid with
      | none => simp [he, hy] at h
      | some pair =>
        obtain ⟨ys, tail⟩ := pair
        simp [he, hy] at h
        rcases h with ⟨rfl, rfl⟩
        simp [ih hy]

private theorem table_bound {k : ℕ} {bits rest : List Bool} {rs : List Rule}
    (h : (table k).run bits = some (rs, rest)) : rs.length ≤ bits.length := by
  simp only [table, natField, StateT.run_bind] at h
  change (do
    let p ← readNat bits
    let q ← (readFields (rule k) p.1).run p.2
    let u ← (guard (q.1.map (fun (r : Rule) => (r.state, r.inputSymbol, r.workSymbols))).Nodup :
      Parser Unit).run q.2
    pure (q.1, u.2)) = _ at h
  cases he : readNat bits with
  | none => simp [he] at h
  | some pair =>
    obtain ⟨m, mid⟩ := pair
    cases hr : (readFields (rule k) m).run mid with
    | none => simp [he, hr] at h
    | some pair =>
      obtain ⟨rows, tail⟩ := pair
      have hlen := readFields_length _ hr
      have hbound := readNat_length he
      by_cases hv : (rows.map (fun r => (r.state, r.inputSymbol, r.workSymbols))).Nodup
      · simp [he, hr, guard, hv] at h
        obtain ⟨rfl, rfl⟩ := h
        omega
      · simp [he, hr, guard, hv] at h

/-- The tape count and the number of transition rules of a decoded program are both
bounded by the whole input length. -/
theorem decode_size_bounds {bits : List Bool} {p : Program} (h : decode bits = some p) :
    p.workTapes ≤ bits.length ∧ p.table.length ≤ bits.length := by
  cases hn : readNat bits with
  | none => simp [decode, hn] at h
  | some frame =>
    obtain ⟨len, rest⟩ := frame
    by_cases hlen : len ≤ rest.length
    · simp [decode, hn, hlen] at h
      cases ht : readNat (rest.take len) with
      | none => simp [decodeBody, ht] at h
      | some fields =>
        obtain ⟨k, data⟩ := fields
        cases hr : (table k).run data with
        | none => simp [decodeBody, ht, hr] at h
        | some result =>
          obtain ⟨rs, rem⟩ := result
          cases rem with
          | nil =>
            simp [decodeBody, ht, hr] at h
            subst p
            have hk := readNat_length ht
            have hrule := table_bound hr
            have hl := readNat_length hn
            simp at hk
            change k ≤ bits.length ∧ rs.length ≤ bits.length
            omega
          | cons => simp [decodeBody, ht, hr] at h
    · simp [decode, hn, hlen] at h

/-- Every configuration reached before the signed-witness clock expires occupies only
polynomially many tape cells, also when the program and its tape count vary with its input. -/
theorem reachable_cells_le {bits : List Bool} {p : Program} {t : ℕ} {c : Config}
    (hp : decode bits = some p) (h : p.Reachable bits t c) (ht : t ≤ bits.length ^ 100) :
    c.cells ≤ max 1 bits.length + bits.length ^ 100 + bits.length * (1 + bits.length ^ 100) :=
  h.cells_le.trans (Nat.add_le_add (Nat.add_le_add_left ht _) (Nat.mul_le_mul
    (decode_size_bounds hp).1 (Nat.add_le_add_left ht 1)))

/-- A single interpreted transition checks at most quadratically many work symbols. -/
theorem lookup_comparisons_le {bits : List Bool} {p : Program} {t : ℕ} {c : Config}
    (hp : decode bits = some p) (h : p.Reachable bits t c) :
    (scanRules c p.table).2 ≤ bits.length ^ 2 := by
  rw [pow_two]
  obtain ⟨hk, hr⟩ := decode_size_bounds hp
  exact (scanRules_spec _ _).2.trans (Nat.mul_le_mul hr (h.tape_bounds.1.le.trans hk))

/-- All successor states fit the indicated bound. Halting programs have no successors. -/
def ActionStateBound (bound : ℕ) : Action → Prop
  | .halt _ => True
  | .step t => t.state ≤ bound
  | .branch s t => s.state ≤ bound ∧ t.state ≤ bound

private theorem flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    exact (Nat.add_le_add (h _ (by simp)) (ih (fun b hb => h _ (by simp [hb])))).trans_eq
      (Nat.add_comm ..)

private theorem symbolBits_length_le (s : Symbol) : (symbolBits s).length ≤ 3 := by
  cases s <;> decide

private theorem directionBits_length_le (d : Direction) : (directionBits d).length ≤ 3 := by
  cases d <;> decide

private theorem transitionBits_length_oneTape {bound : ℕ} (t : Transition)
    (h : t.workMoves.length = 1) (hs : t.state ≤ bound) : (transitionBits t).length ≤ bound + 10 := by
  have hm := flatMap_length_le t.workMoves moveBits 6 (fun m _ => by
    have hd := directionBits_length_le m.2
    have hw := symbolBits_length_le m.1
    simpa only [moveBits, List.length_append] using Nat.add_le_add hw hd)
  rw [h, one_mul] at hm
  have hd := directionBits_length_le t.inputMove
  simp only [transitionBits, List.length_append, unary, List.length_replicate,
    List.length_cons, List.length_nil] at *
  omega

private theorem actionBits_length_oneTape {bound : ℕ} (a : Action)
    (h : ActionArity 1 a) (hs : ActionStateBound bound a) :
    (actionBits a).length ≤ 2 * bound + 23 := by
  cases a with
  | halt o =>
    cases o <;> simp [actionBits, outputBits, unary]
  | step t =>
    have := transitionBits_length_oneTape t h hs
    simp [actionBits, unary]
    omega
  | branch s t =>
    have := transitionBits_length_oneTape s h.1 hs.1
    have := transitionBits_length_oneTape t h.2 hs.2
    simp [actionBits, unary]
    omega

/-- The unary encoding of a one-work-tape program is linear in the table length for a
fixed bound on state names. The bound includes both the rules and their destinations. -/
theorem encode_length_oneTape_le (p : Program) (bound : ℕ) (hk : p.workTapes = 1)
    (hp : WellFormed p) (h : ∀ r ∈ p.table, r.state ≤ bound ∧ ActionStateBound bound r.action) :
    (encode p).length ≤ (p.table.length + 1) * (8 * bound + 100) := by
  have hrows := flatMap_length_le p.table ruleBits (3 * bound + 30) (by
    intro r hr
    obtain ⟨hw, ha⟩ := hp.2 r hr
    rw [hk] at hw ha
    obtain ⟨hs, hu⟩ := h r hr
    have hhead := symbolBits_length_le r.inputSymbol
    have hwork := flatMap_length_le r.workSymbols symbolBits 3 (fun s _ => symbolBits_length_le s)
    rw [hw, one_mul] at hwork
    have hact := actionBits_length_oneTape r.action ha hu
    simp only [ruleBits, unary, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    omega)
  simp only [encode, bodyBits, unary, List.length_append, List.length_cons, List.length_nil,
    List.length_replicate, hk]
  rw [Nat.mul_add] at hrows ⊢
  simp only [Nat.add_mul, Nat.one_mul, Nat.mul_left_comm p.table.length] at hrows ⊢
  omega

end ProgramCode

/-- The integer path sum of the program at the start of `x`, with the clock `n^100`. -/
def signedWitness {n : ℕ} (x : Fin n → Bool) : ℤ :=
  let bits := List.ofFn x
  match ProgramCode.decode bits with
  | none => 0
  | some p => pathSum p bits (n ^ 100)

theorem abs_signedWitness_le {n : ℕ} (x : Fin n → Bool) :
    |signedWitness x| ≤ (2 : ℤ) ^ (n ^ 100) := by
  simp only [signedWitness]
  split
  · simp
  · apply abs_pathSum_le

/-- Deterministic signed verifier, with exactly as many guess bits as clock steps. -/
def signedVerifier {n : ℕ} (x : Fin n → Bool) (guesses : Fin (n ^ 100) → Bool) : Output :=
  let bits := List.ofFn x
  match ProgramCode.decode bits with
  | none => .zero
  | some p => paddedOutput p.next (n ^ 100) (p.initial bits) guesses

/-- Unused guesses are required to be zero, so padding does not change the multiplicity of paths. -/
theorem signedWitness_eq_sum_verifier {n : ℕ} (x : Fin n → Bool) :
    signedWitness x = ∑ guesses, (signedVerifier x guesses).value := by
  unfold signedWitness signedVerifier
  dsimp only
  cases h : ProgramCode.decode (List.ofFn x) with
  | none => simp [Output.value]
  | some p => exact (sum_paddedRun p.next (n ^ 100) (p.initial _) (le_refl _)).symm

/-- The explicit comparison family `P_n^*`, with its integral coefficients mapped to `R`. -/
noncomputable def signedWitnessPolynomial (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin n × Bool) R :=
  ∑ x : Fin n → Bool, MvPolynomial.C (signedWitness x : R) *
    ∏ i, MvPolynomial.X (i, x i)

theorem signedWitnessPolynomial_isHomogeneous (R : Type*) [CommRing R] (n : ℕ) :
    (signedWitnessPolynomial R n).IsHomogeneous n := by
  apply MvPolynomial.IsHomogeneous.sum
  intro x _
  apply MvPolynomial.IsHomogeneous.C_mul
  simpa using MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => MvPolynomial.X (R := R) (i, x i)) (fun _ => 1)
    (fun i _ => MvPolynomial.isHomogeneous_X R (i, x i))

/-- Selecting one variable in each pair recovers the associated signed path sum. -/
theorem eval_signedWitnessPolynomial (R : Type*) [CommRing R] {n : ℕ} (x : Fin n → Bool) :
    MvPolynomial.eval (fun p : Fin n × Bool => if p.2 = x p.1 then 1 else 0)
      (signedWitnessPolynomial R n) = (signedWitness x : R) := by
  classical
  rw [signedWitnessPolynomial, map_sum, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
    simp only [map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    have h : (∏ i, (if y i = x i then (1 : R) else 0)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj]
    rw [h, mul_zero]
  · simp

/-- Specialization to a field (or ring) takes the coefficient-wise image of the integral family. -/
theorem map_signedWitnessPolynomial (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial.map (Int.castRingHom R) (signedWitnessPolynomial ℤ n) =
    signedWitnessPolynomial R n := by
  simp [signedWitnessPolynomial]

end SpectralBooks
end LinearAlgebra
end OAI
