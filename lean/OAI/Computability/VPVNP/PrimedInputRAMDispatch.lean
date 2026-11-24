import OAI.Computability.VPVNP.PrimedInputRAM
import OAI.Computability.VPVNP.PrimedInputRAMAddresses

/-!
# Arithmetic dispatch for each position in the pair counter

The two passes of Section 11 enumerate the rectangular input positions in
row-major order. Division and remainder identify the group, site, and tape
offset. Comparisons with the public field boundaries decide whether the bit
is literal, comes from a header word, or must be read at a designated
scratch address. The same computation marks the first-pass branch sites.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open BurstRAM RAMLayout RAMSerialization

/-- Raw addresses precede conversion to the bounded address word. -/
inductive RawCopy where
  | literal (value : Bool)
  | fetch (address : ℕ)

/-- The group, site and tape bit designate a row-major scratch word. -/
def rectangleAddress (base n r g v j : ℕ) : ℕ :=
  base + (2 ^ r * g + v) * n + j

private abbrev Decision := RawCopy × Bool

private def zero : Decision := (.literal false, false)

/-- Decide which of the header and path bits to fetch. The middle cut
always resides in the outgoing cut slot of group zero. -/
def dispatchHeader (L : Lengths) (base n r P g v j : ℕ) : Decision :=
  let middle := RawCopy.fetch (rectangleAddress base n r 0 v (P + r + 3))
  match j with
  | 0 => if v < L.index then (.fetch (3 + g * L.index + v), false) else zero
  | 1 => if v < L.advice then (.fetch (3 + 2 * L.index + v), false) else zero
  | 2 =>
    if g = 0 then
      if v < L.leftCut then (.fetch (3 + 2 * L.index + L.advice + v), false) else zero
    else if v < L.middleCut then (middle, false) else zero
  | _ =>
    if g = 0 then
      if v < L.middleCut then (middle, true) else zero
    else if v < L.rightCut then (.fetch (3 + 2 * L.index + L.advice + L.cutCapacity + v), false)
    else zero

/-- Resolve the transcript part of the row. No parsing is applied to
the data at the designated location. -/
def dispatchPort (base n r H w P g v k : ℕ) : Decision × ℕ :=
  let sender := rawSource r H w v k
  match sender.1 with
  | none => (zero, sender.2 + 1)
  | some (u, t) =>
    ((.fetch (rectangleAddress base n r g u (P + r + 4 + t)), decide (u = v ∧ t = k)),
      sender.2 + 14)

/-- Dispatch within one row. The prefix is a private public-data array, and
the field lengths and widths are public registers. Charges cover boundary
arithmetic, comparisons, branching, and the calculation of the result. -/
def dispatchRow (L : Lengths) (n r H w base P : ℕ) (prefixAt : ℕ → Bool) (g v j : ℕ) :
    Decision × ℕ :=
  if j < P then ((.literal (prefixAt j), false), 3)
  else if j < P + r then ((.literal (v.testBit (j - P)), false), 8)
  else if j < P + r + 4 then (dispatchHeader L base n r P g v (j - (P + r)), 26)
  else if j < P + r + 4 + width r H w then
    let result := dispatchPort base n r H w P g v (j - (P + r + 4))
    (result.1, result.2 + 12)
  else (zero, 12)

/-- Scalar program, with group, site and within-row bit extracted from the
enumeration counter. The four quotient/remainder operations and the shift
constructing `2^r` cost five word steps. -/
def dispatch (L : Lengths) (n r H w base P : ℕ) (prefixAt : ℕ → Bool) (i : ℕ) :
    Decision × ℕ :=
  let row := i / n
  let result := dispatchRow L n r H w base P prefixAt (row / 2 ^ r) (row % 2 ^ r) (i % n)
  (result.1, result.2 + 5)

theorem dispatch_work (L : Lengths) (n r H w base P : ℕ) (prefixAt : ℕ → Bool) (i : ℕ) :
    (dispatch L n r H w base P prefixAt i).2 ≤ 6 * r + 63 := by
  simp only [dispatch, dispatchRow]
  split_ifs <;> try omega
  rename_i hj
  have h := rawSource_work r H w (i / n % 2 ^ r) (i % n - (P + r + 4))
  simp only [dispatchPort]
  split <;> omega

variable {L : Lengths} {n r H w : ℕ}

namespace Layout

variable (Q : Layout L n r H w)

private abbrev P := (UniversalMachine.programPrefix Q.program).length

/-- The prefix table is indexed in private storage and padded by zero. -/
def prefixAt (j : ℕ) : Bool := (UniversalMachine.programPrefix Q.program)[j]?.getD false

private def rawRef : Ref L r H w → RawCopy
  | .literal b => .literal b
  | .header j => .fetch j.address.val
  | .shared b => .fetch (Q.bitAddress (Q.internalOwner b).val).val

private theorem middle_raw (v : Fin L.middleCut) :
    Q.rawRef (.shared (.inl v)) =
      .fetch (rectangleAddress Q.scratchBase n r 0 v.val (Q.P + r + 3)) := by
  unfold rawRef
  apply congrArg RawCopy.fetch
  change Q.scratchBase + (Q.P + (r + 3) + n * (v.val + 2 ^ r * 0)) = _
  simp [rectangleAddress, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem port_raw (g : Fin 2) (p : SharedBit r H w) :
    Q.rawRef (.shared (.inr (g, p))) = .fetch (rectangleAddress Q.scratchBase n r g.val p.val.1.val
      (Q.P + r + 4 + (offset r H w p.val.2).val)) := by
  unfold rawRef
  apply congrArg RawCopy.fetch
  change Q.scratchBase + (Q.P + (r + (4 + (offset r H w p.val.2).val)) +
    n * (p.val.1.val + 2 ^ r * g.val)) = _
  simp [rectangleAddress, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem dispatchHeader_eq (g : Fin 2) (v : Fin (2 ^ r)) (j : Fin 4) :
    dispatchHeader L Q.scratchBase n r Q.P g.val v.val j.val =
      (Q.rawRef (headerRef L g v j), decide (j = 3 ∧ g = 0 ∧ v.val < L.middleCut)) := by
  fin_cases j <;> fin_cases g <;>
    simp [dispatchHeader, headerRef, zero] <;>
    split_ifs <;> (try simp only [middle_raw]) <;> simp_all [rawRef, Header.address, rectangleAddress]

private theorem dispatchPort_eq (g : Fin 2) (v : Fin (2 ^ r)) (p : Slot r H w) :
    (dispatchPort Q.scratchBase n r H w Q.P g.val v.val (offset r H w p).val).1 =
      (Q.rawRef (cellRef L (UniversalMachine.programPrefix Q.program).get
        ((g,v), (.inr (.inr (.inr (.inl p))) : RowField Q.program n r H w))), decide (IsSend (v,p))) := by
  simp only [cellRef]
  split
  · rename_i hs
    have hd : ¬ IsSend (v, p) := by
      intro h
      have he := (sourcePort_eq_self_iff _).mpr ((designated_iff _).mpr h)
      rw [sourcePort_eq_source, hs] at he
      contradiction
    simp [dispatchPort, rawSource_offset, sourcePort_eq_source, hs, zero, rawRef, hd]
  · rename_i y hs
    simp only [dispatchPort, rawSource_offset, sourcePort_eq_source, hs, Option.map_some]
    rw [port_raw]
    have he : y.1.val = v.val ∧ (offset r H w y.2).val = (offset r H w p).val ↔ IsSend (v, p) := by
      rw [← designated_iff, ← sourcePort_eq_self_iff, sourcePort_eq_source, hs, Option.some.injEq]
      constructor
      · rintro ⟨ha,hb⟩
        exact Prod.ext (Fin.ext ha) ((offset r H w).injective (Fin.ext hb))
      · rintro rfl
        exact ⟨rfl, rfl⟩
    rw [decide_eq_decide.mpr he]

private theorem testBit_wordBits (v : Word r) (a : Fin r) : v.val.testBit a.val = wordBits r v a := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  change decide (v.val / 2 ^ a.val % 2 = 1) = (finFunctionFinEquiv.symm v a == 1)
  rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, Fin.ext_iff, finFunctionFinEquiv_symm_apply_val]
  rfl

private theorem dispatchRow_eq (g : Fin 2) (v : Fin (2 ^ r)) (f : RowField Q.program n r H w) :
    (dispatchRow L n r H w Q.scratchBase Q.P Q.prefixAt g.val v.val (rowIndex Q.program Q.fits f).val).1 =
      (Q.rawRef (cellRef L (UniversalMachine.programPrefix Q.program).get ((g,v), f)),
        cellOwner L ((g,v), f)) := by
  rcases f with p | (a | (t | (port | pad)))
  · change (dispatchRow _ _ _ _ _ _ _ _ _ _ p.val).1 = (.literal _, false)
    have hp : p.val < Q.P := p.isLt
    simp [dispatchRow, hp, prefixAt]
  · change (dispatchRow _ _ _ _ _ _ _ _ _ _ (Q.P + a.val)).1 = (.literal (wordBits r v a), false)
    have ha := a.isLt
    rw [dispatchRow, ite_eq_right (by omega), ite_eq_left (by omega), Nat.add_sub_cancel_left,
      testBit_wordBits]
  · change (dispatchRow _ _ _ _ _ _ _ _ _ _ (Q.P + (r + t.val))).1 = _
    have ht := t.isLt
    rw [dispatchRow, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    rw [show Q.P + (r + t.val) - (Q.P + r) = t.val by omega]
    exact Q.dispatchHeader_eq g v t
  · let k := (offset r H w port).val
    change (dispatchRow _ _ _ _ _ _ _ _ _ _ (Q.P + (r + (4 + k)))).1 = _
    have hk : k < width r H w := (offset r H w port).isLt
    rw [dispatchRow, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
    rw [show Q.P + (r + (4 + k)) - (Q.P + r + 4) = k by omega]
    exact Q.dispatchPort_eq g v port
  · change (dispatchRow _ _ _ _ _ _ _ _ _ _ (Q.P + (r + (4 + (width r H w + pad.val))))).1 = zero
    rw [dispatchRow, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]

private theorem dispatch_coordinates (g : Fin 2) (v : Fin (2 ^ r)) (f : RowField Q.program n r H w) :
    (PrimedInputRAM.dispatch L n r H w Q.scratchBase Q.P Q.prefixAt (Q.coordinates ((g,v), f)).val).1 =
      (Q.rawRef (cellRef L (UniversalMachine.programPrefix Q.program).get ((g,v), f)),
        cellOwner L ((g,v), f)) := by
  let j := (rowIndex Q.program Q.fits f).val
  have hj : j < n := (rowIndex Q.program Q.fits f).isLt
  let row := v.val + 2 ^ r * g.val
  have hq : (Q.coordinates ((g,v), f)).val = j + n * row := rfl
  have hrow : (j + n * row) / n = row := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hbit : (j + n * row) % n = j := by simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have hg : row / 2 ^ r = g.val := by
    rw [show row = v.val + 2 ^ r * g.val by rfl, Nat.add_mul_div_left _ _ (Nat.two_pow_pos r),
      Nat.div_eq_of_lt v.isLt, Nat.zero_add]
  have hv : row % 2 ^ r = v.val := by simp [row, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
  simp only [PrimedInputRAM.dispatch, hq, hrow, hbit, hg, hv]
  exact Q.dispatchRow_eq g v f

/-- Every header or scratch address returned by the natural-number
calculation fits the physical address word before the conversion. -/
theorem dispatch_fetch_lt (i : Fin (positions n r)) {a : ℕ}
    (ha : (PrimedInputRAM.dispatch L n r H w Q.scratchBase
      (UniversalMachine.programPrefix Q.program).length Q.prefixAt i.val).1.1 = .fetch a) : a < 2 ^ w := by
  obtain ⟨⟨⟨g,v⟩, f⟩, rfl⟩ := Q.coordinates.surjective i
  rw [Q.dispatch_coordinates g v f] at ha
  cases hr : cellRef L (UniversalMachine.programPrefix Q.program).get ((g,v), f) with
  | literal b => simp [hr, rawRef] at ha
  | header j =>
    simp [hr, rawRef] at ha
    exact ha ▸ (Q.readHeader j).isLt
  | shared b =>
    simp [hr, rawRef] at ha
    exact ha ▸ (Q.bitAddress (Q.internalOwner b).val).isLt

/-- Convert the arithmetic result into the actual source instruction of a
bounded-word burst RAM. At every valid position the fetch address fits. -/
def compileCopy (bitWord : Bool → Word w) : RawCopy → CopySource w
  | .literal b => .literal (bitWord b)
  | .fetch a => .fetch (Fin.ofNat (2 ^ w) a)

private theorem compile_rawRef (bitWord : Bool → Word w) (ref : Ref L r H w) :
    compileCopy bitWord (Q.rawRef ref) = Q.refSource bitWord ref := by
  cases ref with
  | literal b => rfl
  | header j =>
    apply congrArg CopySource.fetch
    exact Fin.ext (Nat.mod_eq_of_lt (Q.readHeader j).isLt)
  | shared b =>
    apply congrArg CopySource.fetch
    exact Fin.ext (Nat.mod_eq_of_lt (Q.bitAddress (Q.internalOwner b).val).isLt)

/-- Both instructions needed by the two loops at this flattened position. -/
def dispatch (bitWord : Bool → Word w) (i : Fin (positions n r)) : CopySource w × Bool :=
  let d := PrimedInputRAM.dispatch L n r H w Q.scratchBase Q.P Q.prefixAt i.val
  (compileCopy bitWord d.1.1, d.1.2)

/-- The scalar dispatcher recovers both the second-pass copy source and
the first-pass owner decision at every position. -/
theorem dispatch_eq (bitWord : Bool → Word w) (i : Fin (positions n r)) :
    Q.dispatch bitWord i = (Q.source bitWord i, Q.owns i) := by
  obtain ⟨⟨⟨g,v⟩, f⟩, rfl⟩ := Q.coordinates.surjective i
  change (compileCopy bitWord (PrimedInputRAM.dispatch _ _ _ _ _ _ _ _ _).1.1, _) =
    (Q.refSource bitWord (cellRef L (UniversalMachine.programPrefix Q.program).get
      (Q.coordinates.symm (Q.coordinates ((g,v),f)))),
      cellOwner L (Q.coordinates.symm (Q.coordinates ((g,v),f))))
  rw [Equiv.symm_apply_apply, Q.dispatch_coordinates g v f, Q.compile_rawRef]

end Layout
end PrimedInputRAM

end VPVNP
end Computability
end OAI
