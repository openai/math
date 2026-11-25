import OAI.Hierarchy.DescentTerminalScalarPadded

namespace OAI
/-! # Full native word receipts for the two fixed terminal comparison banks -/
namespace Hierarchy.DescentTerminalScalarScanRead
open DescentTerminalDenseWindow DescentTerminalDenseWindowRAM DescentTerminalScalarTransposes
open DescentTerminalBinReaddress Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
noncomputable section

theorem dense_read {bits W q piece n out : ℕ} (ib cb raw ptr sh tab : Bank)
    (fits : ∀b∈[ib,cb,raw,ptr,sh,tab],b.Fits bits out)
    (indices : n ≤ ib.size) (ctl : n ≤ cb.size)
    (menuRoom : Menus q (W*piece) ≤ ptr.size) (shiftRoom : radix q (W*piece) ≤ sh.size)
    (tableRoom : Menus q (W*piece)*(radix q (W*piece)*radix q (W*piece)) ≤ tab.size)
    (idx : Fin n→ℕ) (valid : ∀i,idx i+1<raw.size) (fmt : Fin n→Format q (W*piece))
    (data : ℕ→Word (q*(W*piece))) (m : Memory bits) (input : Inputs ib cb raw ptr sh tab idx fmt data m)
    (room : q*(W*piece) ≤ bits) (i : Fin n) :
    (row ib cb raw ptr sh tab).eval m (i.val:Word bits)=
      wide (DescentTerminalScalarPadded.observed room idx fmt data m out i) := by
  rw [row_eval ib cb raw ptr sh tab fits indices ctl menuRoom shiftRoom tableRoom idx valid fmt data m input i,
    DescentTerminalScalarPadded.observed_at]
  simp only [DescentTerminalDenseWindow.entry,wide,Equiv.symm_apply_apply]

theorem route_read {bits c K W q piece : ℕ} (out : ℕ) (gate payload pointer table : Bank)
    (hg : gate.Fits bits out) (hx : payload.Fits bits out)
    (hp : pointer.Fits bits out) (ht : table.Fits bits out)
    (gs : 3*(K*W) ≤ gate.size) (xs : K*W ≤ payload.size) (ps : 2^c ≤ pointer.size)
    (ts : 2^c*2^(sliceWidth W q piece) ≤ table.size) (addr : Address c W q)
    (ctl : Fin K→Tagged.Row c) (X : Proposal K W q piece) (m : Memory bits)
    (inputs : DescentTerminalBinSliceCheap.Inputs gate payload pointer table addr ctl X m)
    (i : Fin (K*W)) :
    (sliceLookup gate payload pointer table).eval m (i.val:Word bits)=sliceOutput addr ctl X i :=
  sliceLookup_eval gate payload pointer table out hg hx hp ht gs xs ps ts
    (controls ctl) (chunks X) (DescentTerminalBinReaddress.entry bits piece addr) m
    inputs.1 inputs.2.1 (fun a=>by simpa [DescentTerminalBinSliceCheap.pointers] using inputs.2.2.1 a) inputs.2.2.2 i

end
end Hierarchy.DescentTerminalScalarScanRead

end OAI
