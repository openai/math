import OAI.ThreeFlat.RAM.ContractionLookup

namespace OAI
/-! # The cell scan evaluates the product of local coefficients -/

namespace ThreeFlat.RAM.Contraction

open Computability.VPVNP.BurstRAM BitLayout Fin.CommRing

variable {F : Type*} [Fintype F] [Field F] {p w : ℕ}
variable (N : BitNetwork F p) (fit : Fits N w)

noncomputable abbrev codec := FieldCode.ofCardLe (card_le_word N fit)

noncomputable def parameters : Fin 5 → Word w :=
  ![(hiddenBase p : Word w), (cellsBase p N.internal : Word w),
    (mulBase p N.internal N.cells : Word w), (Fintype.card F : Word w), (codec N fit).encode 1]

private def pending (i : ℕ) : Finset (Fin N.cells) :=
  Finset.univ.filter (fun j => i ≤ j.val)

omit [Fintype F] [Field F] in
private theorem pending_last : pending N N.cells = ∅ := by
  ext j
  simp [pending]

omit [Fintype F] [Field F] in
private theorem pending_cons (i : Fin N.cells) :
    pending N i.val = insert i (pending N (i.val+1)) := by
  ext j
  simp only [pending, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

omit [Fintype F] [Field F] in
theorem next_pointer (i : ℕ) :
    ((cellAddr N i : ℕ) : Word w)+1+1+1+8 = ((cellAddr N (i+1) : ℕ) : Word w) := by
  simp only [cellAddr, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem cell_scan (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (fuel : ℕ) (r : Registers w) (i : ℕ) (hi : i ≤ N.cells) (a : F)
    (ptr : r 1 = (cellAddr N i : Word w))
    (last : r 2 = (mulBase p N.internal N.cells : Word w))
    (stride : r 3 = (Fintype.card F : Word w)) (acc : r 4 = (codec N fit).encode a)
    (one : r 5 = 1) (tailMem : Memory w := fun _ => 0) :
    eval (codec N fit) (parameters N fit) (fuel + 22*(N.cells-i) + 2) 12 r
        (memoryWithTail tailMem N (codec N fit) pin hidden) =
      a * ∏ j ∈ pending N i, N.factor pin hidden j := by
  induction h : N.cells - i generalizing i r a with
  | zero =>
    obtain rfl : i = N.cells := by omega
    have heq : r 1 = r 2 := ptr.trans last.symm
    simp [cells_done _ _ fuel _ _ heq, pending_last, acc, FieldCode.decode_encode]
  | succ n ih =>
    let j : Fin N.cells := ⟨i, by omega⟩
    let m := memoryWithTail tailMem N (codec N fit) pin hidden
    let s := afterCell r m
    have hnext : N.cells - (i+1) = n := by omega
    have hne : r 1 ≠ r 2 := by
      rw [ptr,last]
      intro hx
      have hv := congrArg Fin.val hx
      rw [Fin.val_cast_of_lt (cellAddr_lt N fit hi),
        Fin.val_cast_of_lt (mulBase_lt N fit)] at hv
      simp only [cellAddr, mulBase] at hv
      omega
    have tail := ih s (i+1) (by omega) (a * N.factor pin hidden j)
      (by change r 1+1+1+1+8 = _; rw [ptr, next_pointer]) last stride
      (by
        change m (r 4 * r 3 + coefficient m (r 1) + r 2).val = _
        rw [ptr, acc, stride, last]
        rw [show coefficient m (cellAddr N i : Word w) =
            (codec N fit).encode (N.factor pin hidden j) from
          read_coefficient N fit _ pin hidden j tailMem]
        exact read_multiplication N fit pin hidden a (N.factor pin hidden j) tailMem)
      one hnext
    rw [show fuel + 22*(n+1) + 2 = (fuel+22*n+2)+22 by omega,
      cell_round _ _ _ _ _ hne one]
    change eval _ _ (fuel+22*n+2) 12 s m = _
    rw [tail, pending_cons N j, Finset.prod_insert]
    · exact mul_assoc _ _ _
    · simp [pending, j]

theorem cell_scan_all (pin : Fin p → Bool) (hidden : Fin N.internal → Bool)
    (fuel : ℕ) (r : Registers w)
    (ptr : r 1 = (cellsBase p N.internal : Word w))
    (last : r 2 = (mulBase p N.internal N.cells : Word w))
    (stride : r 3 = (Fintype.card F : Word w)) (acc : r 4 = (codec N fit).encode 1)
    (one : r 5 = 1) (tailMem : Memory w := fun _ => 0) :
    eval (codec N fit) (parameters N fit) (fuel+22*N.cells+2) 12 r
        (memoryWithTail tailMem N (codec N fit) pin hidden) = N.weight pin hidden := by
  simpa [pending, BitNetwork.weight] using cell_scan N fit pin hidden fuel r 0
    (Nat.zero_le _) 1 (by simpa [cellAddr] using ptr) last stride acc one tailMem

end ThreeFlat.RAM.Contraction

end OAI
