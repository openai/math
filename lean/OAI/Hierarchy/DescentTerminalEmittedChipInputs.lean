import OAI.Hierarchy.DescentTerminalEmitterInputFrames
import OAI.Hierarchy.DescentTerminalEmitterBoot

namespace OAI
/-! # Literal source words and numerical dictionaries of the fixed chip prefix -/
namespace Hierarchy.DescentTerminalEmitter
open DescentTerminalChipRuntime DescentTerminalChipPins DescentTerminalDenseWindow DescentTerminalDenseWindowRAM DescentTerminalScalarTransposes
open DescentTerminalBinReaddress DescentTerminalScalarPadded Computability.VPVNP.RAMSerialization
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {K W q p w : ℕ}
local notation "n" => K*W
local notation "c" => DescentTerminalBinFormat.controlBits W q
variable (S : Shape) (L : Layout)
theorem boot_read (B : Banks) (m : Memory w) (z : DescentTerminalChipPins.Inputs K W q p→Bool) (room : Room S L w)
    (init : Boot B m z)
    (before : ∀b∈[B.ySlices,B.scalar.payload,B.joinedX,B.xWords,B.highField,B.menuStart,B.denseROM,
        B.pointer,B.routeROM,B.scalar.pointer],∀j<b.size,BeforeKey S L (b.base+j) ∧ AfterFlights S L (b.base+j))
    (caps : (∀b∈[B.ySlices,B.scalar.payload,B.joinedX,B.xWords],n ≤ b.size) ∧
      radix q (W*p)≤B.highField.size ∧ Menus q (W*p)≤B.menuStart.size ∧
      Menus q (W*p)*(radix q (W*p)*radix q (W*p))≤B.denseROM.size ∧
      2^c≤B.pointer.size ∧ 2^c*2^(sliceWidth W q p)≤B.routeROM.size) :
    Boot B (result S L m) z := by
  have saved (b : Bank) (hb:b∈[B.ySlices,B.scalar.payload,B.joinedX,B.xWords,B.highField,B.menuStart,B.denseROM,
      B.pointer,B.routeROM,B.scalar.pointer]) (j : ℕ) (live : j<b.size) : result S L m (b.base+j)=m (b.base+j) :=
    printed_before S L m room (before b hb j live).1 (before b hb j live).2
  have offset_lt {rows stride i j : ℕ} (row : i < rows) (digit : j < stride) :
      i * stride + j < rows * stride := by
    have edge := Nat.mul_le_mul_right stride row
    rw [Nat.succ_mul] at edge
    exact (Nat.add_lt_add_left digit _).trans_le edge
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro which slice i
    let b := if which then (if slice then B.ySlices else B.scalar.payload)
      else (if slice then B.joinedX else B.xWords)
    have pin : b ∈ [B.ySlices,B.scalar.payload,B.joinedX,B.xWords] := by
      cases which <;> cases slice <;> simp [b]
    have listed : b ∈ [B.ySlices,B.scalar.payload,B.joinedX,B.xWords,B.highField,B.menuStart,
        B.denseROM,B.pointer,B.routeROM,B.scalar.pointer] := by
      cases which <;> cases slice <;> simp [b]
    exact (saved b listed i.val (i.isLt.trans_le (caps.1 b pin))).trans (init.pins which slice i)
  · intro u
    exact (saved B.highField (by simp) u.val (u.isLt.trans_le caps.2.1)).trans (init.high u)
  · intro v
    exact (saved B.menuStart (by simp) v.val (v.isLt.trans_le caps.2.2.1)).trans (init.menu v)
  · intro v lo hi
    have pair : lo.val * radix q (W*p) + hi.val < radix q (W*p) * radix q (W*p) :=
      offset_lt lo.isLt hi.isLt
    have entry := (offset_lt v.isLt pair).trans_le caps.2.2.2.1
    exact (saved B.denseROM (by simp) _ entry).trans (init.lookup v lo hi)
  · intro a
    exact (saved B.pointer (by simp) _ (a.isLt.trans_le caps.2.2.2.2.1)).trans (init.ptr a)
  · intro a b
    have entry := (offset_lt a.isLt b.isLt).trans_le caps.2.2.2.2.2
    exact (saved B.routeROM (by simp) _ entry).trans (init.route a b)

end
end Hierarchy.DescentTerminalEmitter

end OAI
