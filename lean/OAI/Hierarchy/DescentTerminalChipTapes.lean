import OAI.Hierarchy.DescentTerminalChipBooks

namespace OAI
/-! # Materializing both fixed data views and the shared tables of the scalar chip -/
namespace Hierarchy.DescentTerminalChipSource
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalScalarTransposes
open DescentTerminalBinReaddress DescentTerminalDenseWindow DescentTerminalDenseWindowRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {K W q p w : ℕ}
local notation "n" => K*W
local notation "d" => q*(W*p)
local notation "c" => DescentTerminalBinFormat.controlBits W q
local notation "routes" => DescentTerminalBinFormat.address W q

theorem wide_nat {u : ℕ} (room : u ≤ w) (a : Word u) :
    DescentTerminalScalarTransposes.wide a=(a.val:Word w) := by
  apply (wordBits _).injective
  funext j
  have fit : a.val<2^w := a.isLt.trans_le (Nat.pow_le_pow_right (by decide) room)
  rw [←Computability.VPVNP.LiveHeader.testBit_wordBits (a.val:Word w) j,Fin.val_cast_of_lt fit]
  simp only [DescentTerminalScalarTransposes.wide,Equiv.apply_symm_apply]
  by_cases included : j.val<u
  · simpa only [dite_eq_left included] using (Computability.VPVNP.LiveHeader.testBit_wordBits a ⟨j.val,included⟩).symm
  · have zero : a.val.testBit j.val=false :=
      Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt included)))
    simpa only [dite_eq_right included] using zero.symm

/-- Static geometry and three shared Boolean tables. The fourth proposal
column is consumed by the scalar-key shelf after the two flag words. -/
structure Tapes (B : Banks) (s : Content K W q p) (m : Memory w)
    (z : DescentTerminalChipPins.Inputs K W q p→Bool) : Prop where
  index : ∀i : Fin n,m (B.index.base+i.val)=(s.first i:Word w)
  format : ∀i : Fin n,m (B.formats.base+i.val)=((formatIndex q (W*p) (s.format i)).val:Word w)
  raw : ∀j<B.raw.size,m (B.raw.base+j)=((s.raw j).val:Word w)
  gates : ∀i : Fin n,m (B.gate.base+3*i.val)=((controls s.gate i).val:Word w)
  pins : ∀which slice : Bool,∀i : Fin n,
    m ((if which then (if slice then B.ySlices else B.scalar.payload) else (if slice then B.joinedX else B.xWords)).base+i.val)=
      DescentTerminalChipPins.column z which slice i.val
  high : ∀u : Word d,m (B.highField.base+u.val)=(offsets w (radix q (W*p)) (radix q (W*p)))[u.val]
  menu : ∀v : Fin (Menus q (W*p)),m (B.menuStart.base+v.val)=
    (offsets w (Menus q (W*p)) (radix q (W*p)*radix q (W*p)))[v.val]
  lookup : ∀(v : Fin (Menus q (W*p))) (lo hi : Word d),m (B.denseROM.base+
    (v.val*(radix q (W*p)*radix q (W*p))+(lo.val*radix q (W*p)+hi.val)))=
      DescentTerminalDenseWindow.entry w q (W*p) v lo hi
  ptr : ∀a : Fin (2^c),m (B.pointer.base+a.val)=(DescentTerminalBinSliceCheap.pointers w c (sliceWidth W q p))[a.val]'a.isLt
  route : ∀(a : Tagged.Row c) (b : Word (sliceWidth W q p)),
    m (B.routeROM.base+(a.val*2^(sliceWidth W q p)+b.val))=DescentTerminalBinReaddress.entry w p routes a b

theorem chips (A : Layout) (B : Banks) (s : Content K W q p) (m : Memory w) (z : DescentTerminalChipPins.Inputs K W q p→Bool)
    (room : d ≤ w) (f : ∀b∈[B.index,B.formats,B.raw,B.menuStart,B.highField,B.denseROM],b.Fits w A.first)
    (cap : n ≤ B.index.size ∧ n ≤ B.formats.size ∧ Menus q (W*p) ≤ B.menuStart.size ∧ radix q (W*p) ≤ B.highField.size ∧
      Menus q (W*p)*(radix q (W*p)*radix q (W*p)) ≤ B.denseROM.size)
    (seen : ∀i,s.first i+1<B.raw.size)
    (rf : B.gate.Fits w A.first ∧ B.joinedX.Fits w A.first ∧ B.pointer.Fits w A.first ∧ B.routeROM.Fits w A.first)
    (rc : 3*n ≤ B.gate.size ∧ n ≤ B.joinedX.size ∧ 2^c ≤ B.pointer.size ∧ 2^c*2^(sliceWidth W q p) ≤ B.routeROM.size)
    (t : Tapes B s m z) : Chips A B s m z := by
  have sized : sliceWidth W q p ≤ w := by simpa [sliceWidth_eq] using room
  refine ⟨f,cap,seen,⟨t.index,t.format,t.raw,t.menu,t.high,t.lookup⟩,rf,rc,
    ⟨t.gates,fun i=>?_,t.ptr,t.route⟩,fun i=>?_,fun i=>?_⟩
  · simpa [DescentTerminalChipPins.column,DescentTerminalChipPins.word,i.isLt] using t.pins false true i
  · simpa [DescentTerminalChipPins.column,DescentTerminalChipPins.word,i.isLt,wide_nat room] using t.pins false false i
  · simpa [DescentTerminalChipPins.column,DescentTerminalChipPins.word,i.isLt,wide_nat sized] using t.pins true true i

end
end Hierarchy.DescentTerminalChipSource

end OAI
