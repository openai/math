import OAI.Hierarchy.DescentTerminalGatePadding
import OAI.Hierarchy.DescentTerminalDenseWindowRAM
import OAI.Hierarchy.DescentTerminalScalarTransposes

namespace OAI
/-! # A single paid host for every branch's two terminal transposes -/
namespace Hierarchy.DescentTerminalScalarPadded
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalScalarTransposes DescentTerminalDenseWindow
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical
noncomputable section
variable {K cap W q piece bits : ℕ}

def front (fit : K ≤ cap) (x : Proposal cap W q piece) : Proposal K W q piece :=
  fun b=>x (b.castLE fit)
def copyRow (fit : K ≤ cap) (i : Fin (K*W)) := i.castLE (Nat.mul_le_mul_right W fit)

@[simp] theorem copy_pair (fit : K ≤ cap) (b : Fin K) (s : Fin W) :
    copyRow fit (finProdFinEquiv (b,s))=finProdFinEquiv (b.castLE fit,s) := Fin.ext rfl

theorem row_front (fit : K ≤ cap) (x : Proposal cap W q piece) (i : Fin (K*W)) :
    rowWord (front fit x) i=rowWord x (copyRow fit i) := by
  obtain ⟨⟨b,u⟩,rfl⟩:=finProdFinEquiv.surjective i
  simp [rowWord,front]
theorem chunks_front (fit : K ≤ cap) (x : Proposal cap W q piece) (i : Fin (K*W)) :
    chunks (front fit x) i=chunks x (copyRow fit i) := by
  obtain ⟨⟨b,u⟩,rfl⟩:=finProdFinEquiv.surjective i
  simp [chunks,front]

def blank (q p : ℕ) : Format q p := fun _=>(0,0)
local notation "routes" => DescentTerminalBinFormat.address W q

theorem slice_front (fit : K ≤ cap) (ctl : Fin K→Tagged.Row (DescentTerminalBinFormat.controlBits W q))
    (x y : Proposal cap W q piece)
    (checked : wide ∘ chunks y=sliceOutput (bits:=bits) routes (gates ctl) x) :
    wide ∘ chunks (front fit y)=sliceOutput (bits:=bits) routes ctl (front fit x) := by
  funext i
  obtain ⟨⟨b,u⟩,rfl⟩:=finProdFinEquiv.surjective i
  have matched:=congrFun checked (finProdFinEquiv (b.castLE fit,u))
  simpa [sliceOutput,controls,chunks,gates,front,pad_front] using matched

theorem slice_tail (room : sliceWidth W q piece ≤ bits)
    (ctl : Fin K→Tagged.Row (DescentTerminalBinFormat.controlBits W q)) (x y : Proposal cap W q piece)
    (checked : wide ∘ chunks y=sliceOutput (bits:=bits) routes (gates ctl) x)
    (b : Fin cap) (outside : K ≤ b.val) (s : Slot W q) (d : Fin (W*piece)) : y b s d=false := by
  have witness:=congrArg (routed room) checked
  rw [from_slices] at witness
  rw [witness]
  simp [routed,sliceOutput,controls,chunks,reassembled,gates,pad,not_lt.mpr outside,emptyGate,
    DescentTerminalBinFormat.address_encode]

local notation "p" => W*piece
def observed {pool : ℕ} (room : q*p ≤ bits) (idx : Fin pool→ℕ) (fmt : Fin pool→Format q p)
    (raw : ℕ→Word (q*p)) (m : Memory bits) (out : ℕ) (i : Fin pool) :=
  low room (ThreeFlat.RAM.fillSegment out pool
    (DescentTerminalDenseWindowRAM.file out idx fmt raw) m (out+i.val))

theorem observed_at {pool : ℕ} (room : q*p ≤ bits) (idx : Fin pool→ℕ) (fmt : Fin pool→Format q p)
    (raw : ℕ→Word (q*p)) (m : Memory bits) (out : ℕ) (i : Fin pool) :
    observed room idx fmt raw m out i=word (fmt i) (raw (idx i)) (raw (idx i+1)) := by
  apply (wordBits _).injective
  funext j
  simp only [observed,low,Equiv.apply_symm_apply]
  exact DescentTerminalDenseWindowRAM.output_bit out idx fmt raw m i j room

theorem source_front (fit : K ≤ cap) (room : q*p ≤ bits) (idx : Fin (K*W)→ℕ)
    (fmt : Fin (K*W)→Format q p) (raw : ℕ→Word (q*p)) (m : Memory bits) (out : ℕ)
    (x : Proposal cap W q piece)
    (checked : rowWord x=observed room (pad idx 0) (pad fmt (blank q p)) raw m out) :
    ∀i : Fin (K*W),rowWord (front fit x) i=observed room idx fmt raw m out i := by
  intro i
  rw [row_front,checked,observed_at,observed_at]
  simp [copyRow]

theorem source_tail (room : q*p ≤ bits) (idx : Fin (K*W)→ℕ) (fmt : Fin (K*W)→Format q p)
    (raw : ℕ→Word (q*p)) (m : Memory bits) (out : ℕ) (x : Proposal cap W q piece)
    (checked : rowWord x=observed room (pad idx 0) (pad fmt (blank q p)) raw m out) :
    ∀b : Fin cap,K ≤ b.val→∀(s : Slot W q) (d : Fin p),x b s d=false := by
  intro b outside s d
  let row:=finProdFinEquiv (b,s.1)
  have lo : K*W ≤ row.val := by
    change K*W ≤ s.1.val+W*b.val
    rw [Nat.mul_comm K W]
    exact (Nat.mul_le_mul_left W outside).trans (Nat.le_add_left _ _)
  have fmt_off : pad fmt (blank q p) row=blank q p := by
    unfold pad
    exact dite_eq_right (not_lt.mpr lo)
  have matchBit:=congrArg (fun v=>wordBits _ v (finProdFinEquiv (s.2,d))) (congrFun checked row)
  rw [observed_at,fmt_off] at matchBit
  have unpack : wordBits _ (rowWord x row) (finProdFinEquiv (s.2,d))=x b s d := by
    obtain ⟨u,v⟩ := s
    simp only [rowWord,row,Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  exact unpack.symm.trans (matchBit.trans (by simp [word_at,select,blank]))

/-- Both comparisons include every bit of the fixed host. Its first scan
uses the two raw-row sentinels and a zero-length format on the tail.
Its slice scan sends every unused bin to zero independently of its input. -/
theorem fixed_witnesses (room : q*p ≤ bits) (idx : Fin (K*W)→ℕ) (fmt : Fin (K*W)→Format q p)
    (raw : ℕ→Word (q*p)) (m : Memory bits) (out : ℕ)
    (ctl : Fin K→Tagged.Row (DescentTerminalBinFormat.controlBits W q)) :
    ∃!xy : Proposal cap W q piece × Proposal cap W q piece,
      rowWord xy.1=observed room (pad idx 0) (pad fmt (blank q p)) raw m out ∧
      wide ∘ chunks xy.2=sliceOutput (bits:=bits) routes (gates ctl) xy.1 := by
  obtain ⟨x,first,onlyX⟩:=row_unique (K:=cap) (W:=W) (q:=q) (piece:=piece)
    (observed room (pad idx 0) (pad fmt (blank q p)) raw m out)
  have room' : sliceWidth W q piece ≤ bits := by simpa only [sliceWidth_eq] using room
  obtain ⟨y,second,onlyY⟩:=full_slice_unique room' routes (gates ctl) x
  refine ⟨(x,y),⟨first,second⟩,?_⟩
  rintro ⟨a,b⟩ ⟨left,right⟩
  obtain rfl:=onlyX a left
  exact Prod.ext rfl (onlyY b right)

end
end Hierarchy.DescentTerminalScalarPadded

end OAI
