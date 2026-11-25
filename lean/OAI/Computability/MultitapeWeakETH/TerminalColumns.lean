import OAI.Computability.MultitapeWeakETH.TerminalSlots
import OAI.Computability.MultitapeWeakETH.DescriptorProgram

/-! # Scanning the two terminal incidence columns on binary tapes -/

namespace OAI.Computability.MultitapeWeakETH.TerminalWords

open IntegerMultiplication Code Carry Staff Strip VPVNP BurstRAM Compression CompressorRecords PairSimulation
open NativeGrid TerminalGatherGeometry LocalHistory
open scoped Fin.CommRing
open private width_cells from OAI.Computability.VPVNP.PairTerminalPrefix
noncomputable section

private abbrev reg (X : Type) [Codec X] : Regime X := ⟨size,send,Dom.base _⟩

/-- Saturating binary-to-unary conversion prevents an invalid memory image
from allocating an unbounded number of cells. -/
def capped (q : Bits.Word × Tally) := tally (min (Bits.value q.1) q.2.length)

theorem capped_poly : Poly capped := by
  let ρ := reg (Bits.Word × Tally)
  have cap : Realizes ρ (fun q => q.2.length) := by
    change Poly (fun q : Bits.Word × Tally => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Bits.Word) (Y:=Tally)).poly
  have value : Figure ρ (fun q => Bits.value q.1) := ⟨_,Easy.fst.poly,fun _ => rfl⟩
  let b := Figure.of_spoken cap
  have small := value.variant b (value.compare_ b)
  apply Figure.pay (r:=ρ) (a:=fun q => min (Bits.value q.1) q.2.length) ?_ ((diameter _ cap).mono fun _ => min_le_right ..)
  simpa only [min_def_lt] using small

private def address (q : Bits.Word × Tally) := Bits.short q.1.length (Bits.value q.1 + q.2.length)

private theorem address_poly : Poly address := by
  let ρ := reg (Bits.Word × Tally)
  have a : Figure ρ (fun q => Bits.value q.1) := ⟨_,Easy.fst.poly,fun _ => rfl⟩
  have i : Realizes ρ (fun q => q.2.length) := by
    change Poly (fun q : Bits.Word × Tally => tally q.2.length)
    simpa only [recover_tally] using (Easy.snd (X:=Bits.Word) (Y:=Tally)).poly
  have w : Realizes ρ (fun q => q.1.length) := by
    change Poly (fun q : Bits.Word × Tally => tally q.1.length)
    have p := (Easy.ruler (Easy.fst (X:=Bits.Word) (Y:=Tally))).poly
    convert p using 1
    funext q
    rw [← recover_tally (ruler q.1),ruler_length]
  exact (a.added (Figure.of_spoken i)).write w

private theorem address_eq {w : ℕ} (h : Word w) (i : ℕ) :
    address (wordBits h,tally i) = wordBits (h + (i : Word w)) := by
  apply Bits.word_inject
  · simp [address]
  · simp [address,value_native,Fin.val_add,Fin.val_natCast,Nat.add_mod_mod]

variable {A : Type} [Codec A] (read : A × Bits.Word → Bits.Word)

abbrev Column (A : Type) := ((A × Bits.Word) × Tally) × Tally

/-- The input supplies the lookup context, start address, cap on each
decoded value, and the number of consecutive addresses to read. -/
def scan (q : Column A) :=
  (Iter.lineup q.2).map fun j => capped (read (q.1.1.1,address (q.1.1.2,j)),q.1.2)

theorem scan_poly [Inhabited A] (hr : Poly read) : Poly (scan read) := by
  have addr : Poly (fun q : Column A => address (q.1.1.2,q.2)) :=
    (((Easy.fst.compose Easy.fst).compose Easy.snd).pair Easy.snd).poly.compose address_poly
  have ctx : Poly (fun q : Column A => q.1.1.1) := ((Easy.fst.compose Easy.fst).compose Easy.fst).poly
  have cap : Poly (fun q : Column A => q.1.2) := (Easy.fst.compose Easy.snd).poly
  have get := (((ctx.pair addr).compose hr).pair cap).compose capped_poly
  exact (Easy.fst.poly.pair (Easy.snd.poly.compose Iter.poly_line)).compose (Poly.push default [] get)

omit [Codec A] in
theorem scan_eq {w : ℕ} (ctx : A) (m : Memory w)
    (reads : ∀ h : Word w, Bits.value (read (ctx,wordBits h)) = (m h.val).val)
    (head : Word w) (cap count : ℕ) :
    scan read (((ctx,wordBits head),tally cap),tally count) =
      List.ofFn (fun j : Fin count => tally (min (m (head+(j.val : Word w)).val).val cap)) := by
  simp [scan,Iter.lined,List.map_ofFn,Function.comp_def,capped,address_eq,reads]

variable {w a g : ℕ} (X : State a g) (T : IncidenceDirectory w) (ctx : A) (m : Memory w)
    (reads : ∀ h : Word w, Bits.value (read (ctx,wordBits h)) = (m h.val).val)
    (cols : T.ActualColumns X m)

private theorem ordinal (i : Fin (TerminalPrefix.arcCount X)) :
    IncidenceDirectory.actualPort (w:=w) X ((edgeOrder X).entries i) = (i.val : Word w) :=
  (TerminalPrefix.actualPort_eq X _).trans
    (congrArg (fun j : Fin (TerminalPrefix.arcCount X) => (j.val : Word w))
      ((edgeOrder X).entries.symm_apply_apply i))

include cols reads
omit [Codec A] in
theorem scan_inverse (fit : TerminalPrefix.arcCount X ≤ 2^w) :
    scan read (((ctx,wordBits T.actualIn),tally (TerminalPrefix.arcCount X)),tally (TerminalPrefix.arcCount X)) =
      inverse X := by
  rw [scan_eq read ctx m reads]
  apply congrArg List.ofFn
  funext i
  let e := (edgeOrder X).entries i
  let j := number X (X.slots.actualGraph.target.symm e)
  have cell := cols.actualIn e
  rw [ordinal X i] at cell
  have result := cell.trans (TerminalPrefix.actualPort_eq (w:=w) X (X.slots.actualGraph.target.symm e))
  have val : (m (T.actualIn+(i.val : Word w)).val).val = j.val :=
    (congrArg Fin.val result).trans (Nat.mod_eq_of_lt (j.isLt.trans_le fit))
  simp only [val,Nat.min_eq_left j.isLt.le]
  rfl

omit [Codec A] in
theorem scan_widths (cap : ℕ) (allow : X.totalWidth ≤ cap) (fit : X.totalWidth < 2^w) :
    scan read (((ctx,wordBits T.width),tally cap),tally (TerminalPrefix.arcCount X)) = widths X := by
  rw [scan_eq read ctx m reads]
  apply congrArg List.ofFn
  funext i
  have le := Finset.single_le_sum (f:=TerminalPrefix.width X) (fun j _ => Nat.zero_le (TerminalPrefix.width X j))
    (Finset.mem_univ i)
  rw [TerminalPrefix.width_sum] at le
  have cell := cols.width ((edgeOrder X).entries i)
  rw [ordinal X i] at cell
  have val : (m (T.width+(i.val : Word w)).val).val = TerminalPrefix.width X i :=
    (congrArg Fin.val cell).trans (Nat.mod_eq_of_lt (le.trans_lt fit))
  rw [val,Nat.min_eq_left (le.trans allow)]

end
end OAI.Computability.MultitapeWeakETH.TerminalWords
