import OAI.Hierarchy.GridStructuralHeader
import OAI.Hierarchy.GridSelfHeader
import OAI.ThreeFlat.Diagonal.NavigationTerminalWindow

namespace OAI
/-! # Public directory words and the selector in the controller input -/

namespace Hierarchy.GridStructuralHeader
open ThreeFlat RAM Diagonal Diagonal.PhysicalStage NavigationPass NavigationDirectory
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false


variable {F : Type} [Field F] [Fintype F] {w pc regs slots S base d fuel : ℕ}
variable (B : Block F) (axes n cap : ℕ)
local notation "P" => (B.repeat n)
local notation "rem" => (axes-(P).charge)
local notation "ss" => ((P).directory rem axes)
local notation "edges" => ((P).finalEdges rem axes)

variable (M : Machine (64*w) pc regs slots) (fit : NativeTrace.Fits M S base d fuel)
variable (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (raw gateBase : ℕ)
local notation "G" => TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs slots d
local notation "dir" => (directory (w:=w) B axes n cap)
local notation "packet" => TraceReceiverTemplate.words M fit hF st (FieldCode.ofCardLe hF) raw gateBase

local notation "lib" => (HistoryStageBody.Physical.libraryWords B (64*w))
local notation "total" => (wordCount (dir).length (TraceReceiverTemplate.count G) lib)


section Captured
variable {k p E bank tp tr tk ep er ek ell : ℕ}
variable (X : Catalyst.Approximation F k p) (enc : FieldCode F (64*w))
variable (recv : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
local notation "params" => parameters B axes n cap M fit hF st raw gateBase

/-- The control path's initial packer reads the literal directory bytes from the
same captured description used to place receiver parameters. -/
theorem captured_directory (pins : Fin (E*2)→Bool) {start : ℕ}
    (room : GridSelfHeader.rawSize w E bank total≤ start) (selector : Fin ell→Bool)
    (i : ℕ) (hi : i<(dir).length) (b : ℕ) (hb : b<64*w) :
    GridSelfHeader.captured (B:=bank) X enc params recv eval pins start selector
      ((E*2+w^2+bank*w^2)+(64*w)*i+b) =
        (((((dir)[i]?.getD 0:ℕ):Word (64*w)).val.testBit (64*w-1-b)).toNat :Word (64*w)) := by
  let j : Fin (dir).length:=⟨i,hi⟩
  let axis := (j.castAdd (TraceReceiverTemplate.count G+((dir).length+lib))).castAdd (GridReceiverHeader.count w)
  let bit : Fin (64*w):=⟨b,hb⟩
  let ix := finProdFinEquiv (axis,bit)
  have out := GridSelfHeader.operand_at (B:=bank) X enc params recv eval pins room selector ix
  have addr : E*2+w^2+(bank*w^2+ix.val)=(E*2+w^2+bank*w^2)+(64*w)*i+b := by
    change E*2+w^2+(bank*w^2+(b+(64*w)*i))=_; omega
  rw [addr] at out
  have payload : GridSelfHeader.words params axis=((dir)[i]:Word (64*w)) := by
    let ordinal : Fin total := j.castAdd (TraceReceiverTemplate.count G+((dir).length+lib))
    have observed := Fin.addCases_left (m:=total) (n:=GridReceiverHeader.count w)
      (motive:=fun _ => Word (64*w)) (left:=params) (right:=GridReceiverHeader.thresholdWords w) ordinal
    exact observed.trans (first B axes n cap M fit hF st raw gateBase j)
  have read:=GridReceiverHeader.word_at (GridSelfHeader.words params) axis bit
  rw [show GridReceiverHeader.wordBits (64*w) (GridSelfHeader.words params) ix =
      (GridSelfHeader.words params axis).val.testBit (64*w-1-bit.val) from read,payload] at out
  simpa only [List.getElem?_eq_getElem hi,Option.getD_some,bit] using out

/-- Both the early repeated histogram guard and the final widths/zero-padding
guard see exactly the original selector, even after unpacking the compact X. -/
theorem seeded_sources (pins : Fin (E*2)→Bool) (s : Fin (cap+1)→Bool)
    (off slots0 : ℕ) (small : GridSelfHeader.rawSize w E bank total≤GridDescription.sector w)
    (compact : 12*bank ≤ GridDescription.sector w) (capacity : cap≤GridDescription.sector w) :
    let J:=GridDescription.sector w
    let rst:=E*2+w^2+bank*w^2
    let a:=TraceSeedWriter.archive B w axes off slots0 cap rst
    let source:=selectorBit cap s
    let capture:=GridSelfHeader.captured (B:=bank) X enc params recv eval pins (12*J) s
    let loaded:=GridApproximationAdvice.paddedMemory X enc bank (2*J) capture
    (∀ i<(a.directory ss edges (64*w)).length,∀j<64*w,loaded (rst+(64*w)*i+j)=
      (((((a.directory ss edges (64*w))[i]?.getD 0:ℕ):Word (64*w)).val.testBit (64*w-1-j)).toNat:Word (64*w))) ∧
    (∀i<cap,loaded (12*J+1+i)=(source i).toNat) ∧
    (∀ next : Memory (64*w),(∀i,i<a.seed→next i=loaded i) → a.RawWindow ss source next) := by
  intro J rst a source capture loaded
  have Jpos : 0<J := Nat.two_pow_pos _
  have changeDir : a.directory ss edges (64*w)=dir := TraceSeedWriter.archive_directory ..
  have base : rst+total*(64*w)≤J := by
    apply le_trans _ small
    dsimp only [GridSelfHeader.rawSize,rst];gcongr;omega
  have low (i : ℕ) (hi : i<J) : loaded i=capture i := by
    simp only [loaded,GridApproximationAdvice.paddedMemory,fillSegment,ite_eq_right (by omega : ¬(2*J ≤ i ∧ i<2*J+12*bank))]
  have body (i : ℕ) (hi : i<cap) : loaded (12*J+1+i)=(source i).toNat := by
    have keep : ¬(2*J≤12*J+1+i ∧ 12*J+1+i<2*J+12*bank) := by omega
    simp only [loaded,GridApproximationAdvice.paddedMemory,fillSegment,ite_eq_right keep,capture,GridSelfHeader.captured]
    have observed:=GuessLoop.install_get (12*J) s
      (Computability.VPVNP.RAMMemory.initialMemory (GridSelfHeader.rawSize w E bank total) (fun j=>TraceBitHeader.binaryWord (64*w)
        (GridSelfHeader.rawTape (B:=bank) X enc params recv eval pins j))) (Fin.succ ⟨i,hi⟩)
    have literal (b : Bool) : BitLayout.bitWord (64*w) b=(b.toNat:Word (64*w)) := by
      apply Fin.ext
      simp only [BitLayout.bitWord,Fin.ofNat,Fin.val_natCast]
    simpa only [source,selectorBit,dite_eq_left hi,Fin.val_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      using observed.trans (literal _)
  refine ⟨?_,body,?_⟩
  · rw [changeDir]
    intro i hi j hj
    have row : (i+1)*(64*w)≤total*(64*w) := Nat.mul_le_mul_right _ (by unfold wordCount;omega)
    have inside : rst+(64*w)*i+j<J:=by
      rw [Nat.succ_mul,Nat.mul_comm i (64*w)] at row
      omega
    rw [low _ inside]
    exact captured_directory B axes n cap M fit hF st raw gateBase X enc recv eval pins
      (small.trans (by omega)) s i hi j hj
  · intro next same
    have hseed : a.seed=16*J := rfl
    refine ⟨?_,?_,?_,?_⟩
    · change 12*J<16*J;omega
    · change 12*J+1+cap≤16*J;omega
    · change 12*J+1+cap≤16*J;omega
    · intro j hj
      change next ((if next (12*J)=1 then 12*J+1 else 12*J+1)+j)=_
      rw [ite_self,same _ (by rw [hseed];change j<cap at hj;omega)]
      exact body j hj

end Captured
end
end Hierarchy.GridStructuralHeader

end OAI
