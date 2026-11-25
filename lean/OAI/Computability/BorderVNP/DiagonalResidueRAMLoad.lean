import OAI.Computability.BorderVNP.DiagonalResidueRAMScan

/-! # Preparing finite advice and verifying the two valuation scans -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA

variable {w u v k : ℕ}

/-- A bit scan changes only its own interval. -/
theorem putBits_outside (m : Memory w) (start : ℕ) (bs : List Bool) (j : ℕ)
    (hj : j < start ∨ start + bs.length ≤ j) : putBits m start bs j = m j := by
  induction bs generalizing m start with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at hj
    rw [putBits, ih _ _ (by omega), Function.update_of_ne (by omega : j ≠ start)]

/-- Every bit is stored in the designated word of the input interval. -/
theorem putBits_get (m : Memory w) (start : ℕ) (bs : List Bool) (i : Fin bs.length) :
    putBits m start bs (start+i.val) = wordBit w bs[i.val] := by
  induction bs generalizing m start with
  | nil => exact i.elim0
  | cons b bs ih =>
    rcases i with ⟨i,hi⟩
    cases i with
    | zero =>
      rw [putBits, putBits_outside _ _ _ _ (Or.inl (by simp))]
      simp
    | succ j =>
      have hj : j < bs.length := by simpa using hi
      simpa only [putBits, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using
        ih (Function.update m start (wordBit w b)) (start+1) ⟨j,hj⟩

/-- The memory initially contains both constant bits and the query. -/
def queryLoaded (m : Memory w) (base : ℕ) (x : Fin u → Bool) : Prop :=
  (∀ b : Bool, m (base+b.toNat) = wordBit w b) ∧
  ∀ i, m (base+2+i.val) = wordBit w (x i)

/-- Appending a complete private guess vector produces exactly the input
valuation expected by the shared gate evaluator. -/
theorem putBits_knows (m : Memory w) (base : ℕ) (x : Fin u → Bool) (y : Fin v → Bool)
    (hx : queryLoaded m base x) :
    Knows base x y Fin.elim0 (putBits m (base+2+u) (List.ofFn y)) := by
  intro r
  cases r with
  | const b =>
    change putBits m _ _ (base+b.toNat) = _
    rw [putBits_outside _ _ _ _ (Or.inl (by cases b <;> simp <;> omega))]
    exact hx.1 b
  | var t =>
    cases t with
    | inl i =>
      change putBits m _ _ (base+2+i.val) = _
      rw [putBits_outside _ _ _ _ (Or.inl (by omega))]
      exact hx.2 i
    | inr j =>
      have h := putBits_get m (base+2+u) (List.ofFn y) ⟨j.val, by simp⟩
      simpa [address, Ref.read] using h
  | gate i => exact i.elim0

/-- Gate writes change only their consecutive output cells. -/
theorem putRows_outside (m : Memory w) (start : ℕ) (rs : List Row) (a : ℕ)
    (h : a < start ∨ start+rs.length ≤ a) : putRows m start rs a = m a := by
  induction rs generalizing start m with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.length_cons] at h
    rw [putRows,ih _ _ (by omega),Function.update_of_ne (by omega)]

/-- Sequential scans can be split at any gate boundary. -/
theorem putRows_append (m : Memory w) (start : ℕ) (a b : List Row) :
    putRows m start (a++b) = putRows (putRows m start a) (start+a.length) b := by
  induction a generalizing m start with
  | nil => simp [putRows]
  | cons r rs ih => simp [putRows, ih, Nat.add_assoc, Nat.add_comm 1]

/-- Scanning the three-word advice for the given shared-gate program computes
the same memory as its typed, snoc-indexed execution. -/
theorem putRows_typed (m : Memory w) (base : ℕ) (p : Program (Fin u ⊕ Fin v) k) :
    putRows m (gateBase base u v) (List.ofFn (rows base p)) = executeGates base m p := by
  induction p with
  | nil => simp [rows, putRows, executeGates]
  | snoc p r ih =>
    simp only [rows, List.ofFn_succ', Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append,
      putRows_append, putRows, List.length_ofFn, ih, executeGates]

/-- All gates reference only cells within the finite valuation bank. -/
theorem rows_addresses (base : ℕ) (p : Program (Fin u ⊕ Fin v) k) (i : Fin k) :
    (rows base p i).left < gateBase base u v + k ∧
      (rows base p i).right < gateBase base u v + k := by
  induction p with
  | nil => exact i.elim0
  | @snoc k p g ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [rows, Fin.snoc_last]
      cases g with
      | and a b => exact ⟨(address_lt base a).trans (by omega), (address_lt base b).trans (by omega)⟩
      | not a => exact ⟨(address_lt base a).trans (by omega), (address_lt base a).trans (by omega)⟩
    · simp only [rows, Fin.snoc_castSucc]
      exact ⟨(ih j).1.trans (by omega),(ih j).2.trans (by omega)⟩

/-- Serialize the gate records as three words per gate. -/
def adviceData (rs : List Row) : List (Word w) :=
  rs.flatMap fun r => [word w r.left, word w r.right, wordBit w r.invert]

/-- The exact advice length contains three words per gate and no table of
the verifier's values on different queries. -/
theorem adviceData_length (rs : List Row) : (adviceData (w := w) rs).length = 3*rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [adviceData, Nat.mul_succ] at ih ⊢; omega

/-- A packed advice array supplies exactly the required sequential records. -/
theorem loadedRows_of_packed (m : Memory w) (a : ℕ) (rs : List Row)
    (hdata : ∀ i : Fin (adviceData (w := w) rs).length, m (a+i.val) = (adviceData rs)[i.val])
    (hfit : ∀ r ∈ rs, r.left < 2^w ∧ r.right < 2^w) : loadedRows m a rs := by
  induction rs generalizing a with
  | nil => trivial
  | cons r rs ih =>
    have hrow := hfit r (by simp)
    have get (i : ℕ) (hi : i < 3) := hdata ⟨i, by simp [adviceData]; omega⟩
    refine ⟨⟨?_,?_,?_⟩,hrow.1,hrow.2,ih (a+3) ?_ (fun z hz => hfit z (by simp [hz]))⟩
    · simpa [adviceData] using get 0 (by decide)
    · simpa [adviceData] using get 1 (by decide)
    · simpa [adviceData] using get 2 (by decide)
    · intro i
      have hi := i.isLt
      have h := hdata ⟨i.val+3, by simp [adviceData] at hi ⊢; omega⟩
      simpa [adviceData, Nat.add_assoc, Nat.add_comm 3] using h

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
