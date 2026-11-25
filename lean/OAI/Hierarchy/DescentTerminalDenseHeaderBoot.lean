import OAI.Hierarchy.DescentTerminalAppendixNumbers
import OAI.Hierarchy.DescentTerminalDenseHeaderRAM
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.ThreeFlat.Diagonal.TraceBanks
import OAI.ThreeFlat.Diagonal.TraceWordTests

namespace OAI
/-! # Four shared physical dictionaries for all dense width streams -/
namespace Hierarchy.DescentTerminalDenseHeaderBoot
open DescentTerminalDenseHeader DescentTerminalDenseWindow ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section


def bank (q p base : ℕ) (c : Fin 4) : Bank :=
  ⟨base+stride q p*c.val,strideBits q p⟩

def sources (q p base : ℕ) (widths : Bank) : Fin 5 → Bank :=
  ![widths,bank q p base 0,bank q p base 1,bank q p base 2,bank q p base 3]

def layout (q p base : ℕ) (widths rem whole index control : Bank) : DescentTerminalDenseHeaderRAM.Layout :=
  ⟨widths,bank q p base 0,bank q p base 1,bank q p base 2,bank q p base 3,rem,whole,index,control⟩

theorem capacity (q p : ℕ) : profiles q p*(q*p) ≤ stride q p := Nat.le_pow_clog (by decide) _

theorem offset_capacity {q p : ℕ} (pos : 0<q*p) : profiles q p ≤ stride q p :=
  (Nat.le_mul_of_pos_right _ pos).trans (capacity q p)

private theorem key_space {q p bits : ℕ} (room : formatBits q p + 2*(q*p) ≤ bits/2) :
    profiles q p*(q*p) ≤ 2^(bits/2) := by
  have profilesBound : profiles q p ≤ 2^(q*Nat.clog 2 (p+1)) := by
    rw [Nat.mul_comm q,pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
  have exponents : q*Nat.clog 2 (p+1)+q*p ≤ bits/2 := by
    unfold formatBits at room
    rw [Nat.mul_add] at room
    omega
  have b : q*p ≤ 2^(q*p) := Nat.le_of_lt Nat.lt_two_pow_self
  exact (Nat.mul_le_mul profilesBound b).trans (by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) exponents)

/-- The enclosing address range includes all three lookup tables and the ordinal offset table. -/
theorem extent_le {q p bits : ℕ} (room : formatBits q p + 2*(q*p) ≤ bits/2) :
    extent q p ≤ 4*2^(bits/2) :=
  Nat.mul_le_mul_left 4 (Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow (key_space room)))

theorem coefficients {q p w : ℕ} (room : formatBits q p + 2*(q*p) ≤ w/2)
    (a : Profile q p) (r : Fin (q*p)) :
    (encode q p a).val*(q*p) < 2^w ∧ residue a r < 2^w ∧
    carry a r < 2^w ∧ (formatIndex q p (DescentTerminalDenseHeader.control a r)).val < 2^w := by
  have pos : 0 < q*p := (Nat.zero_le r.val).trans_lt r.isLt
  have pow : 2^(w/2) ≤ 2^w := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have keyFit := (key a r).isLt.trans_le ((key_space room).trans pow)
  rw [key_val] at keyFit
  have rawFit : q*p ≤ 2^w :=
    (Nat.le_mul_of_pos_left _ (show 0 < profiles q p from Nat.pow_pos (Nat.succ_pos _))).trans
      ((key_space room).trans pow)
  have carryOne := carry_le a r
  have high : 1 < 2^w := Nat.one_lt_two_pow (by omega)
  exact ⟨by omega, (Nat.mod_lt _ pos).trans_le rawFit, carryOne.trans_lt high,
    (formatIndex q p _).isLt.trans_le ((format_room q p).trans (Nat.pow_le_pow_right (by decide) (by omega)))⟩

private def takeWord {w n : ℕ} (v : Vector (Word w) n) (i : ℕ) : Word w :=
  if inside : i<n then v[i] else 0

def atColumn (w q p : ℕ) : ℕ → ℕ → Word w
  | 0 => takeWord (offsets w q p)
  | 1 => takeWord (table w (residue (q:=q) (p:=p)))
  | 2 => takeWord (table w (carry (q:=q) (p:=p)))
  | 3 => takeWord (table w (fun (z : Profile q p) r => (formatIndex q p (DescentTerminalDenseHeader.control z r)).val))
  | _ => fun _ => 0

/-- No finite coefficient wraps at the actual lookup address. -/
theorem exact_values {w q p : ℕ} (room : formatBits q p + 2*(q*p) ≤ w/2)
    (a : Profile q p) (r : Fin (q*p)) :
    (atColumn w q p 0 (encode q p a).val).val = (encode q p a).val*(q*p) ∧
    (atColumn w q p 1 (key a r).val).val = residue a r ∧
    (atColumn w q p 2 (key a r).val).val = carry a r ∧
    (atColumn w q p 3 (key a r).val).val = (formatIndex q p (DescentTerminalDenseHeader.control a r)).val := by
  obtain ⟨offsetBound,nextBound,carryBound,formatBound⟩ := coefficients room a r
  have offsetRead : atColumn w q p 0 (encode q p a).val = (((encode q p a).val*(q*p):ℕ):Word w) := by
    simp [atColumn,takeWord,offsets,(encode q p a).isLt]
  have nextRead : atColumn w q p 1 (key a r).val = (residue a r:Word w) := by
    simpa only [atColumn,takeWord,dite_eq_left (key a r).isLt] using table_key w residue a r
  have carryRead : atColumn w q p 2 (key a r).val = (carry a r:Word w) := by
    simpa only [atColumn,takeWord,dite_eq_left (key a r).isLt] using table_key w carry a r
  have fmtRead : atColumn w q p 3 (key a r).val =
      ((formatIndex q p (DescentTerminalDenseHeader.control a r)).val:Word w) := by
    simpa only [atColumn,takeWord,dite_eq_left (key a r).isLt] using
      table_key w (fun u v => (formatIndex q p (DescentTerminalDenseHeader.control u v)).val) a r
  rw [offsetRead,nextRead,carryRead,fmtRead]
  exact ⟨Fin.val_cast_of_lt offsetBound,Fin.val_cast_of_lt nextBound,
    Fin.val_cast_of_lt carryBound,Fin.val_cast_of_lt formatBound⟩

/-- The public relative tape can be appended once to the original machine header. -/
def back (w q p : ℕ) : Memory w := fun j => atColumn w q p (j/stride q p) (j%stride q p)

theorem back_cell (w q p : ℕ) (c : Fin 4) {i : ℕ} (within : i < stride q p) :
    back w q p (stride q p*c.val+i) = atColumn w q p c.val i := by
  have positive : 0 < stride q p := Nat.two_pow_pos _
  simp only [back,Nat.mul_add_div positive,Nat.div_eq_of_lt within,
    Nat.add_zero,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt within]

theorem cell_end (q p base : ℕ) (c : Fin 4) :
    (bank q p base c).base+(bank q p base c).size ≤ base+extent q p := by
  have top := Nat.mul_le_mul_left (stride q p) c.isLt
  change base+stride q p*c.val+stride q p ≤ base+4*stride q p
  rw [Nat.mul_succ] at top
  simpa only [Nat.add_assoc,Nat.mul_comm 4] using Nat.add_le_add_left top base

theorem source_ends (q p base : ℕ) (widths : Bank) {limit : ℕ}
    (wordEnd : widths.base+widths.size ≤ limit) (romEnd : base+extent q p ≤ limit) :
    ∀ j : Fin 5, (sources q p base widths j).base+(sources q p base widths j).size ≤ limit := by
  intro j
  fin_cases j
  · exact wordEnd
  · exact (cell_end q p base 0).trans romEnd
  · exact (cell_end q p base 1).trans romEnd
  · exact (cell_end q p base 2).trans romEnd
  · exact (cell_end q p base 3).trans romEnd

/-- Every bit of the appended tables is a public literal independent of the proposal. -/
def backPin {X : Type*} (w q p : ℕ) (i : Fin (extent q p) × Fin (w+1)) : X ⊕ Bool :=
  .inr ((back w q p i.1.val).val.testBit i.2.val)

theorem backPin_read {X : Type*} (z : X → Bool) (w q p : ℕ) (i : Fin (extent q p) × Fin (w+1)) :
    (backPin w q p i).elim z id = ThreeFlat.Diagonal.TraceWords.bits
      (ThreeFlat.Diagonal.TraceBanks.wide (back w q p i.1.val)) i.2 := rfl

theorem bank_fits {q p base w : ℕ} (stop : base+extent q p<2^w) (c : Fin 4) :
    (bank q p base c).Fits w (base+extent q p) := by
  have endAt := cell_end q p base c
  exact ⟨Nat.two_pow_pos _,by omega,endAt⟩

theorem reads {w q p n : ℕ} (base : ℕ) (widths rem whole index control : Bank)
    (a : Fin n → Profile q p) (m : Memory w) (pos : 0<q*p) (limit : base+extent q p<2^w)
    (loaded : ∀ i : Fin n, widths.read m (i.val : Word w) = ((encode q p (a i)).val : Word w))
    (kept : ∀ j < extent q p, m (base+j) = back w q p j) :
    DescentTerminalDenseHeaderRAM.Reads (layout q p base widths rem whole index control) a m := by
  have cell (c : Fin 4) (i : ℕ) (within : i < stride q p) :
      (bank q p base c).read m (i : Word w) = atColumn w q p c.val i := by
    rw [DescentTerminalDenseHeaderRAM.bank_nat m (bank_fits limit c) within]
    change m ((base+stride q p*c.val)+i) = _
    have bound := cell_end q p 0 c
    change 0+stride q p*c.val+stride q p ≤ 0+extent q p at bound
    rw [Nat.add_assoc, kept _ (by omega), back_cell _ _ _ _ within]
  refine ⟨loaded,?_,?_,?_,?_⟩
  · intro z
    have h := cell 0 z.val (z.isLt.trans_le (offset_capacity pos))
    simpa [atColumn,takeWord,z.isLt,offsets,layout] using h
  · intro z r
    let k := key z r
    have h := cell 1 k.val (k.isLt.trans_le (capacity q p))
    refine h.trans ?_
    change atColumn w q p 1 (key z r).val = (residue z r : Word w)
    simpa only [atColumn,takeWord,dite_eq_left (key z r).isLt] using table_key w residue z r
  · intro z r
    let k := key z r
    have h := cell 2 k.val (k.isLt.trans_le (capacity q p))
    refine h.trans ?_
    change atColumn w q p 2 (key z r).val = (carry z r : Word w)
    simpa only [atColumn,takeWord,dite_eq_left (key z r).isLt] using table_key w carry z r
  · intro z r
    let k := key z r
    have h := cell 3 k.val (k.isLt.trans_le (capacity q p))
    refine h.trans ?_
    change atColumn w q p 3 (key z r).val =
      ((formatIndex q p (DescentTerminalDenseHeader.control z r)).val : Word w)
    simpa only [atColumn,takeWord,dite_eq_left (key z r).isLt] using
      table_key w (fun u v => (formatIndex q p (DescentTerminalDenseHeader.control u v)).val) z r

def writer (w q p base : ℕ) :=
  DescentStaticWordColumn.program w base (fun i => (back w q p i).val) (extent q p)

def mounted (w q p base : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (fun i => (back w q p i).val) m (extent q p)

/-- A literal-write startup is also available when the tables are placed after the dynamic widths. -/
theorem writer_run (w q p base : ℕ) (m : Memory w) (room : base+extent q p<2^w) :
    (writer w q p base).Exec m (mounted w q p base m) (4+10*extent q p) :=
  DescentStaticWordColumn.mount _ _ _ _ room

theorem writer_cheap (w q p base : ℕ) : CheapCode (writer w q p base) :=
  DescentStaticWordColumn.cheap w base _ _

theorem writer_names (w q p base : ℕ) :
    DescentStaticWordColumn.names (writer w q p base) = 15*(extent q p+1) :=
  DescentStaticWordColumn.names_mount w base _ _

theorem written (w q p base : ℕ) (m : Memory w) (j : ℕ) (live : j < extent q p) :
    mounted w q p base m (base+j) = back w q p j := by
  simpa only [mounted,Fin.cast_val_eq_self] using
    DescentStaticWordColumn.read base (extent q p) (fun i => (back w q p i).val) m live

theorem writer_frame (w q p base : ℕ) (m : Memory w) (j : ℕ) (away : j<base ∨ base+extent q p≤j) :
    mounted w q p base m j = m j :=
  DescentStaticWordColumn.frame _ _ _ _ j away

/-- Installing after the original profile rows preserves their actual codes for the dense scan. -/
theorem mounted_reads {w q p n : ℕ} (base : ℕ) (widths rem whole index control : Bank)
    (a : Fin n → Profile q p) (m : Memory w) (pos : 0<q*p) (limit : base+extent q p<2^w)
    (earlier : widths.base+widths.size ≤ base)
    (loaded : ∀ i : Fin n, widths.read m (i.val : Word w) = ((encode q p (a i)).val : Word w)) :
    DescentTerminalDenseHeaderRAM.Reads (layout q p base widths rem whole index control) a
      (mounted w q p base m) := by
  refine reads base widths rem whole index control a _ pos limit ?_ (written w q p base m)
  intro i
  have h := Nat.mod_lt (i.val : Word w).val (Nat.two_pow_pos widths.bits)
  exact (writer_frame w q p base m (widths.base+(i.val : Word w).val%widths.size)
    (.inl (by change widths.base+2^widths.bits ≤ base at earlier; change _+_ % 2^widths.bits < base; omega))).trans (loaded i)

end
end Hierarchy.DescentTerminalDenseHeaderBoot

end OAI
