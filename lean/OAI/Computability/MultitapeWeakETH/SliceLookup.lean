import OAI.Computability.MultitapeWeakETH.PacketSpan
import OAI.Computability.VPVNP.PairResidentFrameColumn

/-! # Pointwise simulation of an interval copy on the operand tapes -/

namespace OAI.Computability.MultitapeWeakETH.SliceLookup

open IntegerMultiplication Code Carry Staff Strip VPVNP BurstRAM PairSimulation NativeGrid
open private encoded_short from OAI.Computability.MultitapeWeakETH.TerminalLayout
open scoped Fin.CommRing
noncomputable section

/-- Three binary words give the first source and destination addresses and
the length of the copied interval. The last word is the queried address. -/
abbrev Input := ((Bits.Word × Bits.Word) × Bits.Word) × Bits.Word

def locate (q : Input) : Option Bits.Word :=
  let src := Bits.value q.1.1.1
  let dst := Bits.value q.1.1.2
  let len := Bits.value q.1.2
  let addr := Bits.value q.2
  if addr < dst then none else if addr < dst+len then
    some (Bits.short q.2.length (src + (addr-dst))) else none

private abbrev regime : Regime Input := ⟨size,send,Dom.base _⟩

private theorem branch {f g : Input → Option Bits.Word} {p : Input → Prop} [DecidablePred p]
    (c : Classified regime p) (hf : Poly f) (hg : Poly g) : Poly (fun q => if p q then f q else g q) := by
  obtain ⟨test,cost,correct⟩ := c
  convert Poly.choose (show Poly test from cost) hf hg using 1
  funext q
  cases h : test q <;> simp_all

theorem locate_poly : Poly locate := by
  have fig (f : Input → Bits.Word) (h : Poly f) : Figure regime (fun q => Bits.value (f q)) := ⟨f,h,fun _ => rfl⟩
  have src := fig (fun q => q.1.1.1) (by fun_prop)
  have dst := fig (fun q => q.1.1.2) (by fun_prop)
  have len := fig (fun q => q.1.2) (by fun_prop)
  have addr := fig Prod.snd Easy.snd.poly
  have width : Realizes regime (fun q => q.2.length) := by
    change Poly (fun q : Input => tally q.2.length)
    convert (Easy.ruler (Easy.snd (X:=(Bits.Word × Bits.Word) × Bits.Word) (Y:=Bits.Word))).poly using 1
    funext q
    rw [← ruler_length q.2,recover_tally]
  have source := (src.added (addr.subtracted dst)).write width
  exact branch (addr.compare_ dst) (Code.Poly.const none) (branch (addr.compare_ (dst.added len))
    ((show Code.Poly _ from source).compose Easy.some.poly) (Code.Poly.const none))

/-- Lookup agrees at each address with writing all the source bits by the
native private-memory convention. Empty slices leave every address untouched. -/
theorem locate_copy {w : ℕ} (row : ResidentColumn.Row) (read prior : Bits.Word → Bool)
    (src dst len : Word w) (addr : Word w)
    (count : len.val = row.bits.length)
    (offsets : 0 < row.bits.length → src = ((row.source + row.sourceOffset : ℕ) : Word w) ∧
      dst.val = row.destination + row.targetOffset)
    (room : 0 < row.bits.length → row.destination + row.targetOffset + row.bits.length ≤ 2^w)
    (reads : row.reads (fun k : Word w => PrivateFields.bitValue w (read (wordBits k)))) :
    PrivateFields.bitValue w ((locate (((wordBits src,wordBits dst),wordBits len),wordBits addr)).elim
      (prior (wordBits addr)) read) =
      row.write (fun k : Word w => PrivateFields.bitValue w (prior (wordBits k))) addr := by
  let start := row.destination + row.targetOffset
  by_cases pos : 0 < row.bits.length
  · obtain ⟨hs,hd⟩ := offsets pos
    have good := room pos
    simp only [locate,value_native,length_wordBits,count,hd]
    by_cases left : addr.val < start
    · rw [ite_eq_left left]
      exact (PrivateFields.storeBits_outside start row.bits (fun k : Word w => PrivateFields.bitValue w (prior (wordBits k))) addr good (Or.inl left)).symm
    rw [ite_eq_right left]
    by_cases inside : addr.val < start + row.bits.length
    · rw [ite_eq_left inside]
      let i : Fin row.bits.length := ⟨addr.val-start,by omega⟩
      have address : addr = ((start+i.val : ℕ) : Word w) := by
        apply Fin.ext
        change addr.val = (start + (addr.val-start)) % (2^w)
        rw [Nat.add_sub_of_le (by omega : start ≤ addr.val),Nat.mod_eq_of_lt addr.isLt]
      have bits := PrivateFields.storeBits_read start row.bits
        (fun k : Word w => PrivateFields.bitValue w (prior (wordBits k))) good i
      have key : Bits.short w (src.val + i.val) = wordBits ((row.source + row.sourceOffset + i.val : ℕ) : Word w) := by
        rw [← encoded_short]
        apply congrArg wordBits
        change ((src.val + i.val : ℕ) : Word w) = _
        rw [Nat.cast_add,Nat.cast_add,Fin.cast_val_eq_self,hs]
      change PrivateFields.bitValue w (read (Bits.short w (src.val+i.val))) = _
      rw [key]
      rw [address]
      exact (reads i).trans bits.symm
    · rw [ite_eq_right inside]
      exact (PrivateFields.storeBits_outside start row.bits (fun k : Word w => PrivateFields.bitValue w (prior (wordBits k))) addr good (Or.inr (by omega))).symm
  · have empty : row.bits = [] := List.length_eq_zero_iff.mp (by omega)
    by_cases lt : addr.val < dst.val <;>
      simp [locate,value_native,count,empty,lt,ResidentColumn.Row.write,PrivateFields.storeBits]

end
end OAI.Computability.MultitapeWeakETH.SliceLookup
