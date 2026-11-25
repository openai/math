import OAI.Optimization.LinearProgramming.Lattice.OracleQuerySize
import OAI.Optimization.LinearProgramming.Contraction.Dyadic

/-! The sign-rounding algorithm's actual serial oracle packets and their total bit length. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice

open OracleSpec

/-- The coordinates of a query are signed integers in the repository's framed little-endian
format. The dimension is a parameter of the oracle. -/
abbrev signRowWord {p : ℕ} (row : Fin p → ℤ) : Word := Contract.bitApproximation row

private theorem signRowWord_succ {p : ℕ} (row : Fin (p+1) → ℤ) :
    signRowWord row = (decide (row 0 < 0) :: encodeNat (row 0).natAbs) ++
      signRowWord (fun i : Fin p ↦ row i.succ) := by
  simp [signRowWord, Contract.bitApproximation, List.ofFn_succ]

/-- Consume exactly `p` signed integer fields with a streaming decoder, returning unused bits. -/
def readSignRow : (p : ℕ) → Word → Option ((Fin p → ℤ) × Word)
  | 0, w => some (Fin.elim0, w)
  | p+1, w => do
    let (z, rest) ← Contraction.readSigned w
    let (zs, rest) ← readSignRow p rest
    return (Fin.cons z zs, rest)

theorem readSignRow_append {p : ℕ} (row : Fin p → ℤ) (suffix : Word) :
    readSignRow p (signRowWord row ++ suffix) = some (row, suffix) := by
  induction p with
  | zero =>
    change some (Fin.elim0, suffix) = some (row, suffix)
    rw [show Fin.elim0 = row from funext fun i ↦ i.elim0]
  | succ p ih =>
    rw [signRowWord_succ, List.append_assoc, readSignRow, Contraction.readSigned_word]
    simp [ih]
    exact funext fun i ↦ Fin.cases rfl (fun _ ↦ rfl) i

theorem signRowWord_length {p : ℕ} (row : Fin p → ℤ) :
    (signRowWord row).length = ∑ i, (2*(row i).natAbs.size + 2) := by
  induction p with
  | zero => simp [signRowWord, Contract.bitApproximation]
  | succ p ih =>
    rw [signRowWord_succ, List.length_append, List.length_cons, Contraction.encodeNat_length,
      ih, Fin.sum_univ_succ]

/-- All three replies of the sign oracle have two bits. -/
def signReply : Ordering → Word
  | .lt => [false, false]
  | .eq => [false, true]
  | .gt => [true, false]

def readSignReply : Word → Option Ordering
  | [false, false] => some .lt
  | [false, true] => some .eq
  | [true, false] => some .gt
  | _ => none

@[simp] theorem readSignReply_signReply (s : Ordering) : readSignReply (signReply s) = some s := by
  cases s <;> rfl

@[simp] theorem signReply_length (s : Ordering) : (signReply s).length = 2 := by cases s <;> rfl

/-- The genuine ternary oracle is accessed by the rounding tree through its nonnegative test. -/
def signNonnegative {p : ℕ} (sign : (Fin p → ℤ) → Ordering) : (Fin p → ℤ) → Bool :=
  fun a ↦ decide (sign a ≠ .lt)

/-- The oracle operates on the same `WordOracle` domain as the stack-machine specification.
Extra trailing bits, missing coordinates, and truncated frames receive an empty response. -/
def wordSignOracle {p : ℕ} (sign : (Fin p → ℤ) → Ordering) : WordOracle := fun _ w ↦
  match readSignRow p w with
  | some (a, []) => signReply (sign a)
  | _ => []

@[simp] theorem wordSignOracle_query {p : ℕ} (sign : (Fin p → ℤ) → Ordering)
    (past : Transcript) (row : Fin p → ℤ) :
    wordSignOracle sign past (signRowWord row) = signReply (sign row) := by
  have h := readSignRow_append row []
  rw [List.append_nil] at h
  simp [wordSignOracle, h]

namespace SignQueries

/-- Run the adaptive decision tree by emitting the actual integer-vector encoding and parsing
its ternary reply. Malformed responses are rejected. -/
def runWords {p : ℕ} {α : Type*} (oracle : WordOracle) : SignQueries p α → Transcript → Option (α × Transcript)
  | .done x, tr => some (x, tr)
  | .ask a next, tr =>
    let packet := signRowWord a
    let answer := oracle tr packet
    match readSignReply answer with
    | none => none
    | some s => runWords oracle (next (decide (s ≠ .lt))) ((packet, answer) :: tr)

/-- Actual request and response packets, in transcript order. -/
def wireTranscript {p : ℕ} {α : Type*} (sign : (Fin p → ℤ) → Ordering) (t : SignQueries p α) : Transcript :=
  (history (signNonnegative sign) t).map (fun a ↦ (signRowWord a, signReply (sign a)))

theorem runWords_eq {p : ℕ} {α : Type*} (sign : (Fin p → ℤ) → Ordering) (t : SignQueries p α)
    (past : Transcript) :
    runWords (wordSignOracle sign) t past = some (run (signNonnegative sign) t, wireTranscript sign t ++ past) := by
  induction t generalizing past with
  | done x => rfl
  | ask a next ih =>
    simp [runWords, wireTranscript, history, run, signNonnegative, ih]

end SignQueries

/-- Number of transferred bits in the serialized transcript (arguments plus ternary results). -/
def communicationBits (tr : Transcript) : ℕ := (tr.map fun (q,a) ↦ q.length + a.length).sum

/-- Cost of emitting all argument words followed by their `ask` transitions, whose boundary charge
also transfers the argument and response. Internal arithmetic and control instructions are separate. -/
def emitAskCost (tr : Transcript) : ℕ := (tr.map fun (q,a) ↦ 2*q.length + 1 + a.length).sum

private theorem transcript_bound {p : ℕ} (rs : List (Fin p → ℤ)) (sign : (Fin p → ℤ) → Ordering)
    (width : ℕ) (h : ∀ r ∈ rs, ∀ i, (r i).natAbs.size ≤ width) :
    let tr := rs.map (fun a ↦ (signRowWord a, signReply (sign a)))
    communicationBits tr ≤ rs.length * (p*(2*width + 2) + 2) ∧
    emitAskCost tr ≤ rs.length * (2*(p*(2*width + 2)) + 3) := by
  induction rs with
  | nil => simp [communicationBits, emitAskCost]
  | cons r rs ih =>
    have hrlen : (signRowWord r).length ≤ p * (2*width+2) := by
      rw [signRowWord_length]
      calc
        _ ≤ ∑ _ : Fin p, (2*width+2) := Finset.sum_le_sum fun i _ ↦ by have := h r List.mem_cons_self i; omega
        _ = _ := by simp
    obtain ⟨hc, he⟩ := ih (fun a ha ↦ h a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons, communicationBits, emitAskCost, List.sum_cons, signReply_length,
      List.length_cons] at hc he ⊢
    rw [Nat.succ_mul rs.length (p*(2*width+2)+2), Nat.succ_mul rs.length (2*(p*(2*width+2))+3)]
    constructor <;> omega

/-- Polynomial bound on the request and response bits of the complete adaptive execution, and on
the combined cost of its `emit` and `ask` instructions. -/
theorem roundingProgramWith_communication {p M : ℕ} (hp : 0 < p) (hM : 0 < M)
    (select : (Fin p → ℚ) → ℕ × (Fin p → ℤ))
    (hsel : ∀ u, 0 < (select u).1 ∧ (select u).1 ≤ searchDenominator p M ^ (p+1) ∧
      ∀ i, |((select u).1 : ℚ)*u i - (select u).2 i| ≤ 1/(8*(p : ℚ)*M))
    (v : Fin p → ℝ) (sign : (Fin p → ℤ) → Ordering)
    (hsign : ∀ c, (signNonnegative sign) c = true ↔ 0 ≤ formValue c v) :
    let tr := SignQueries.wireTranscript sign (roundingProgramWith M select)
    let calls := p*(2*p+1+p*searchPrecision p M)
    let packet := p*(2*queryCoefficientWidth p M + 2)
    communicationBits tr ≤ calls*(packet + 2) ∧ emitAskCost tr ≤ calls*(2*packet+3) := by
  let t := roundingProgramWith M select
  let o := signNonnegative sign
  have h := transcript_bound (SignQueries.history o t) sign (queryCoefficientWidth p M)
    (fun _ hr i ↦ roundingProgramWith_query_size hp hM select hsel v o hsign hr i)
  have hc : (SignQueries.history o t).length ≤ p*(2*p+1+p*searchPrecision p M) := by
    rw [SignQueries.history_length]; exact roundingProgramWith_cost M select o
  exact ⟨h.1.trans (Nat.mul_le_mul_right _ hc), h.2.trans (Nat.mul_le_mul_right _ hc)⟩

end Lattice
end LinearProgramming
end Optimization
end OAI
