import OAI.Computability.VPVNP.PrimedInputRAMOpcodeLoad
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeDispatch
import OAI.Computability.VPVNP.LiveHeaderBits
import OAI.Computability.VPVNP.CursorBounds

/-!
# Public words and the register state on entry to the input dispatcher

The fixed program prefix occupies the low bits of one public word. Each call
loads the dimensions of the two rectangles from the public words, reads the
three pair-specific cut lengths from RAM, and decodes its persistent cursor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM RAMLayout

variable {L : Lengths} {n r H w : ℕ}

/-- Numeric value of the literal program prefix, least significant bit first. -/
def packedPrefix (p : UniversalMachine.Program) : Word (UniversalMachine.programPrefix p).length :=
  (RAMSerialization.wordBits _).symm (UniversalMachine.programPrefix p).get

/-- Dimensions, fixed field widths, and the packed prefix in instruction-table order. -/
def pubNat (Q : Layout L n r H w) (i : Pub) : ℕ :=
  match i.val with
  | 0 => positions n r
  | 1 => n
  | 2 => 2^r
  | 3 => r
  | 4 => w
  | 5 => H
  | 6 => Q.scratchBase
  | 7 => (UniversalMachine.programPrefix Q.program).length
  | 8 => width r H w
  | 9 => L.index
  | 10 => L.advice
  | 11 => L.cutCapacity
  | 12 => (packedPrefix Q.program).val
  | 13 => blockBits H w
  | 14 => 8*w
  | _ => 16*w

/-- Encode a public layout parameter from the opcode table's ordered list as a width-`w` word. -/
def pubWord (Q : Layout L n r H w) (i : Pub) : Word w := Fin.ofNat _ (pubNat Q i)

/-- Word-fit conditions beyond the tape and address bounds already in the layout. -/
structure ParameterFit (Q : Layout L n r H w) : Prop where
  prefixFits : (UniversalMachine.programPrefix Q.program).length ≤ w
  blockFits : blockBits H w < 2^w

private theorem layoutRow_lt (Q : Layout L n r H w) : n < 2^w := by
  have hrow : n ≤ positions n r := Nat.le_mul_of_pos_left _ (by positivity)
  have := Q.cursorFits
  omega

/-- As soon as the site address is nonempty, the row contains a full sort block. -/
theorem parameterFit_of_prefix (Q : Layout L n r H w) (hr : 0 < r)
    (hP : (UniversalMachine.programPrefix Q.program).length ≤ w) : ParameterFit Q := by
  have hc : 1 ≤ layerCount r := PortCode.layerCount_mono (show 1 ≤ r from hr)
  have hs : 2 * blockBits H w ≤ layerCount r * (2 * blockBits H w) :=
    Nat.le_mul_of_pos_left _ hc
  have ht := Q.fits
  unfold ProcessorInput.Fits width at ht
  have hn := layoutRow_lt Q
  exact ⟨hP, by omega⟩

/-- At every sufficiently large length the fixed prefix and all public fields
fit the paper's word width, uniformly over all well-formed layouts. -/
theorem eventually_parameterFit (p : UniversalMachine.Program) {B : ℕ} (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ L H (Q : Layout L n (addressWidth B n) H (CursorBounds.wordBits B n)),
      Q.program = p → ParameterFit Q := by
  let P := (UniversalMachine.programPrefix p).length
  filter_upwards [Filter.eventually_ge_atTop (2^(P+1))] with n hn
  have hn₀ : 0 < n := (Nat.two_pow_pos _).trans_le hn
  have hlarge := ((Nat.le_log2 hn₀.ne').mpr hn).trans (log2_le_addressWidth hB n)
  intro L H Q hQ
  apply parameterFit_of_prefix Q (by omega)
  rw [hQ]
  change P ≤ (addressWidth B n + 10)^4
  exact (show P ≤ addressWidth B n + 10 by omega).trans (Nat.le_self_pow (by decide) _)

theorem pubNat_lt (Q : Layout L n r H w) (F : ParameterFit Q) (i : Pub) : pubNat Q i < 2^w := by
  have hc := Q.cursorFits
  have ha := Q.addressesFit
  have hh := Q.headersFit
  unfold Header.count at hh
  have ht := Q.fits
  unfold ProcessorInput.Fits at ht
  have hn := layoutRow_lt Q
  have hpos : 0 < n := by omega
  have hs : 2 * 2^r ≤ positions n r := Nat.le_mul_of_pos_right _ hpos
  have h8 : 16*w ≤ width r H w := by unfold width; omega
  have hw : 0 < w := by
    by_contra! hz
    have : w = 0 := by omega
    simp [this] at hn
    omega
  have hH : H ≤ blockBits H w := by
    have h := Nat.le_mul_of_pos_right (4*H*5) hw
    unfold blockBits
    omega
  have hb := F.blockFits
  have hp := (packedPrefix Q.program).isLt.trans_le (Nat.pow_le_pow_right (by decide) F.prefixFits)
  have := Nat.two_pow_pos r
  fin_cases i
  · change positions n r < 2^w; omega
  · exact hn
  · change 2^r < 2^w; omega
  · change r < 2^w; omega
  · change w < 2^w; omega
  · change H < 2^w; omega
  · change Q.scratchBase < 2^w; omega
  · change (UniversalMachine.programPrefix Q.program).length < 2^w; omega
  · change width r H w < 2^w; omega
  · change L.index < 2^w; omega
  · change L.advice < 2^w; omega
  · change L.cutCapacity < 2^w; omega
  · exact hp
  · exact hb
  · change 8*w < 2^w; omega
  · change 16*w < 2^w; omega

@[simp] theorem pubWord_val (Q : Layout L n r H w) (F : ParameterFit Q) (i : Pub) :
    (pubWord Q i).val = pubNat Q i := Nat.mod_eq_of_lt (pubNat_lt Q F i)

theorem pubWord_cells (Q : Layout L n r H w) (F : ParameterFit Q) :
    (pubWord Q 0).val = positions n r := pubWord_val Q F 0

theorem pubWord_prefixBit (Q : Layout L n r H w) (F : ParameterFit Q) (t : ℕ)
    (ht : t < (UniversalMachine.programPrefix Q.program).length) :
    (pubWord Q 12).val.testBit t = Q.prefixAt t := by
  rw [pubWord_val Q F]
  let i : Fin (UniversalMachine.programPrefix Q.program).length := ⟨t, ht⟩
  change (packedPrefix Q.program).val.testBit i.val = _
  rw [LiveHeader.testBit_wordBits, packedPrefix, Equiv.apply_symm_apply]
  simp [Layout.prefixAt, ht, i]

/-- Memory invariant for the three cut-length words, independent of the rest of memory. -/
def CutMemory (L : Lengths) (m : Memory w) : Prop :=
  ∀ j : Fin 3, (m j.val).val = cutLength L j

theorem cutMemory_header (Q : Layout L n r H w) (hdr : Header L → Bool) (hist : List (Word w)) :
    CutMemory L (headerMemory L hdr hist) := by
  intro j
  rw [headerMemory_length]
  exact Nat.mod_eq_of_lt (Q.cutLength_lt j)

theorem CutMemory.congr {m m' : Memory w} (hc : CutMemory L m)
    (h : ∀ j : Fin 3, m' j.val = m j.val) : CutMemory L m' := fun j => (congrArg Fin.val (h j)).trans (hc j)

/-- Exact state reached by the parameter-load and cursor-decoding instructions. -/
structure Prepared (Q : Layout L n r H w) (state : Word w) (rs : Regs w 48) : Prop where
  dispatch : DispatchInput L n r H w Q.scratchBase (UniversalMachine.programPrefix Q.program).length
    (state.val % positions n r / n / (2^r)) (state.val % positions n r / n % (2^r))
    (state.val % positions n r % n) Q.prefixAt (pubWord Q) rs
  cursor : Cursor n r Q.scratchBase state rs
  stateReg : rs 4 = state
  cells : (rs 5).val = positions n r

private theorem prepared_of_loaded (Q : Layout L n r H w) (F : ParameterFit Q)
    (state : Word w) (m : Memory w) (rs : Regs w 48) (hstate : state.val < positions n r + positions n r)
    (hc : CutMemory L m) (hl : Loaded (pubWord Q) state m rs) : Prepared Q state (cursorRegs rs) := by
  have ht := Q.fits
  unfold ProcessorInput.Fits at ht
  have hn := layoutRow_lt Q
  have hsmall : 3 < 2^w := by omega
  have small (k : ℕ) (hk : k ≤ 3) : (Fin.ofNat (2^w) k).val = k := Nat.mod_eq_of_lt (by omega)
  have e0 : (rs 0).val = 0 := (congrArg Fin.val hl.zero).trans (small _ (by decide))
  have e1 : (rs 1).val = 1 := (congrArg Fin.val hl.one).trans (small _ (by decide))
  have e2 : (rs 2).val = 2 := (congrArg Fin.val hl.two).trans (small _ (by decide))
  have e3 : (rs 3).val = 3 := (congrArg Fin.val hl.three).trans (small _ (by decide))
  have pv {i : Reg} {j : Pub} (h : rs i = pubWord Q j) : (rs i).val = pubNat Q j :=
    (congrArg Fin.val h).trans (pubWord_val Q F j)
  have readLength {i : Reg} (j : Fin 3) (h : rs i = m (Fin.ofNat (2^w) j.val).val) :
      (rs i).val = cutLength L j := by rw [h, small j.val (by have := j.isLt; omega), hc j]
  have hcur := cursorRegs_spec (n := n) (r := r) (base := Q.scratchBase) rs state e1 hl.cursor
    (pv hl.cells) (pv hl.rowWidth) (pv hl.sites) (pv hl.base)
    (by have := Q.cursorFits; omega) (by have := Q.addressesFit; omega)
  refine ⟨?_, hcur, hl.cursor, pv hl.cells⟩
  refine ⟨?_, pv hl.sites, pv hl.incident, hcur.bit, Nat.mod_lt _ (Nat.two_pow_pos _), ?_,
    by omega, pubWord_val Q F 13, pubWord_val Q F 14, pubWord_val Q F 15⟩
  · exact ⟨e0, e1, e2, e3, pv hl.rowWidth, pv hl.siteBits, pv hl.base, pv hl.prefixWidth,
      pv hl.indexWidth, pv hl.adviceWidth, pv hl.cutCapacity, readLength 0 hl.left,
      readLength 1 hl.middle, readLength 2 hl.right, hcur.group, hcur.site, rfl⟩
  · intro t ht
    change (rs 17).val.testBit t = _
    rw [hl.prefixWord]
    exact pubWord_prefixBit Q F t ht

/-- Every data call reaches the dispatch contract by 18 private loads, three
header reads and seven cursor arithmetic steps, leaving external memory intact. -/
theorem load_unpack_exec (Q : Layout L n r H w) (F : ParameterFit Q) (state : Word w)
    (m : Memory w) (rs : Regs w 48) (hstate : state.val < positions n r + positions n r)
    (hc : CutMemory L m) :
    ∃ out, Flow.Exec (pubWord Q) state (.seq loadParameters unpackCursor) rs m
      (parameterEvents w m ++ List.replicate 7 .tick) out m ∧ Prepared Q state out := by
  obtain ⟨rs', he, hl⟩ := loadParameters_exec (pubWord Q) state m rs
  exact ⟨_, he.seq (unpackCursor_exec _ _ _ _), prepared_of_loaded Q F state m rs' hstate hc hl⟩

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
