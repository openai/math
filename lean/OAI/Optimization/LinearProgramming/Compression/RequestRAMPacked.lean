import OAI.Optimization.LinearProgramming.Compression.RequestRAMScan

/-! Normal packed input and complete scalar-machine trace for the reduced basis scan. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestScreen

open RAM

/-- The problem dimensions in the initial address registers for the fixed scan program. -/
def addressInput (n : ℕ) : List ℕ :=
  List.ofFn fun i : Fin 28 => if i.val = 20 ∨ i.val = 21 then 24 else
    if i.val = 23 then n+2 else if i.val = 27 then n+1 else 0

private def inputRow {n : ℕ} (r : Fin (n+1) → Fin (n+2) → ℚ) (row col : ℕ) : ℚ :=
  if hi : row < n+1 then if hj : col < n+2 then r ⟨row,hi⟩ ⟨col,hj⟩ else 0 else 0

private def datum {n : ℕ} (r : Fin (n+1) → Fin (n+2) → ℚ) (a : ℕ) : ℚ :=
  if a = 0 then (requestCutoff (n+1) : ℚ)^2 else if a < 24 then 0
  else inputRow r ((a-24)/(n+2)) ((a-24)%(n+2))

/-- The squared cutoff and contiguous rational basis entries in the scalar register bank. -/
def scalarInput {n : ℕ} (r : Fin (n+1) → Fin (n+2) → ℚ) : List ℚ :=
  List.ofFn fun a : Fin (24+(n+1)*(n+2)) => datum r a.val

private theorem datum_row {n : ℕ} (r : Fin (n+1) → Fin (n+2) → ℚ)
    (i : Fin (n+1)) (j : Fin (n+2)) :
    datum r (24+i.val*(n+2)+j.val) = r i j := by
  have hd : (i.val*(n+2)+j.val)/(n+2) = i.val := by
    rw [Nat.mul_comm i.val (n+2), Nat.mul_add_div (by omega : 0<n+2), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hm : (i.val*(n+2)+j.val)%(n+2) = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  have hb : ¬ 24+i.val*(n+2)+j.val < 24 := by omega
  have hsub : 24+i.val*(n+2)+j.val-24 = i.val*(n+2)+j.val := by omega
  simp [datum, hb, hsub, hd, hm, inputRow, i.isLt, j.isLt]

private theorem scalarInput_get_row {n : ℕ} (r : Fin (n+1) → Fin (n+2) → ℚ)
    (i : Fin (n+1)) (j : Fin (n+2)) :
    (scalarInput r)[24+i.val*(n+2)+j.val]?.getD 0 = r i j := by
  have hi := Nat.mul_le_mul_right (n+2) i.isLt
  have h : 24+i.val*(n+2)+j.val < 24+(n+1)*(n+2) := by
    rw [Nat.succ_mul] at hi
    omega
  simpa only [scalarInput, List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_some] using datum_row r i j

private theorem scalarInput_height {n R : ℕ} (r : Fin (n+1) → Fin (n+2) → ℚ)
    (hR : 1 ≤ R) (hcap : requestCutoff (n+1)^2 ≤ R)
    (hrow : ∀ i j, (r i j).num.natAbs ≤ R ∧ (r i j).den ≤ R) (a : ℕ) :
    let x := (scalarInput r)[a]?.getD 0
    x.num.natAbs ≤ R ∧ x.den ≤ R := by
  dsimp only
  have hzero : (0 : ℚ).num.natAbs ≤ R ∧ (0 : ℚ).den ≤ R := by simp [hR]
  by_cases h : a < 24+(n+1)*(n+2)
  · simp only [scalarInput, List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_some]
    unfold datum
    split_ifs
    · norm_cast
    · exact hzero
    · unfold inputRow
      split_ifs <;> first | exact hrow _ _ | exact hzero
  · simpa only [scalarInput, List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_none] using hzero

/-- Source-independent instruction list for the entire first-candidate selection. -/
def program : Program := scan.compile 0 ++ [.halt 0]

/-- Starting from its standard packed data, the uniform RAM halts with the very same
row selection as the executable rational `requestCandidate` function. The bit bound
covers all scalar registers of every state in the trace. -/
theorem packed_trace {n H : ℕ} (w : Fin (n+1) → ℚ) (g : Fin (n+1) → Fin (n+1) → ℤ)
    (hheight : ∀ i j, ((requestGraphRat w (g i)) j).num.natAbs ≤ H ∧
      ((requestGraphRat w (g i)) j).den ≤ H) :
    let r := fun i => requestGraphRat w (g i)
    let B := max H (requestCutoff (n+1)^2)
    ∃ k ≤ (n+1)*(9*(n+2)+19)+5, ∃ t : Fin (k+1) → State ℚ,
      Trace program (start (addressInput n) (scalarInput r)) k t ∧
      (t (Fin.last k)).output = some 0 ∧ (t (Fin.last k)).index 28 =
        ((requestCandidate w g (Fin.last n)).map Fin.val).getD (n+1) ∧
      ∀ i, scalarBound (affineEvalBits (n+2) B) (t i) := by
  let r := fun i => requestGraphRat w (g i)
  let B := max H (requestCutoff (n+1)^2)
  let m := (start (addressInput n) (scalarInput r)).memory
  have hH : 1 ≤ H := (r 0 0).den_pos.trans_le (hheight 0 0).2
  have hB : 1 ≤ B := hH.trans (le_max_left ..)
  have hs : m.AllData (fun a => ratBits a ≤ affineEvalBits (n+2) B) := by
    intro a
    exact ratBits_affine_input (n+2) _ (scalarInput_height r hB (le_max_right ..)
      (fun i j => ⟨(hheight i j).1.trans (le_max_left ..), (hheight i j).2.trans (le_max_left ..)⟩) a)
  have h20 : m.index 20 = 24 := by simp [m, State.memory, start, addressInput]
  have h21 : m.index 21 = 24 := by simp [m, State.memory, start, addressInput]
  have h23 : m.index 23 = n+2 := by simp [m, State.memory, start, addressInput]
  have h27 : m.index 27 = n+1 := by simp [m, State.memory, start, addressInput]
  have hcap : m.data 0 = (requestCutoff (n+1) : ℚ)^2 := by
    simp [m, State.memory, start, scalarInput, datum]
  have hzero : m.data 2 = 0 := by
    change (scalarInput r)[2]?.getD 0 = 0
    have ht : 2 < 24+(n+1)*(n+2) := by omega
    simp only [scalarInput, List.getElem?_ofFn, ht, ↓reduceDIte, Option.getD_some]
    simp [datum]
  have row (i : Fin (n+1)) (j : Fin (n+2)) :
      m.data (m.index 20+i.val*(n+2)+j.val) = requestGraphRat w (g i) j := by
    rw [h20]
    exact scalarInput_get_row r i j
  obtain ⟨k,hk,s,run,hsel⟩ := scan_spec w g m (fun i j => And.intro
    ((hheight i j).1.trans (le_max_left H (requestCutoff (n+1)^2)))
    ((hheight i j).2.trans (le_max_left H (requestCutoff (n+1)^2)))) hs
    (by omega) (h21.trans h20.symm) h23 h27 row hcap hzero
  obtain ⟨t,htr,hhalt,hmem,hsafe⟩ := run.halted_trace (tag := 0)
  refine ⟨k+1,by omega,t,htr,hhalt,?_,hsafe⟩
  change (t (Fin.last (k+1))).memory.index 28 = _
  rwa [hmem]

end RequestScreen
end Compression
end LinearProgramming
end Optimization
end OAI
