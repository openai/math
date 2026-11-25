import OAI.Hierarchy.TaggedWireHeaderBit
import OAI.Hierarchy.TaggedWideControlBoard
import OAI.Hierarchy.ProtocolRAMCalendarBootPins

namespace OAI
/-! # Original tag, chronological choice, and literal sockets of a native CPU header -/
noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.WordSlots
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.Diagonal
open Tagged Tagged.WideControlJoin ProtocolRAM ProtocolRAM.Calendar ProbeStage ProbeStage.Native
open scoped Fin.CommRing Classical
variable {X E : Type} {h d : ℕ} {slot : Event→Slot X}
local notation "W" => Native.wordBits h d Native.copies
variable (L : WordSlots slot (Native.wordBits h d Native.copies))
    (es : List Event) (tagPin : Row h×Fin h→E)

def exposed (a : E→Bool) (i : Row h) : Row h :=
  (Computability.VPVNP.RAMSerialization.wordBits h).symm (fun j=>a (tagPin (i,j)))

def entryPin (base : Boot.Tape h d) (addr : ℕ) (j : Fin (W+1)) : (E⊕Fin (bits slot es))⊕Bool :=
  if a : addr<2^h then
    if bit : j.val<h then .inl (.inl (tagPin (⟨addr,a⟩,⟨j.val,bit⟩))) else .inr false
  else if bit : j.val<W then
    match L.headerBit es addr ⟨j.val,bit⟩ with
    | some q => .inl (.inr q)
    | none => .inr ((base addr).val.testBit j.val)
  else .inr false

def tape (base : Boot.Tape h d) (e : E→Bool) (q : Bits (bits slot es)) :=
  Boot.tagRows (fun i=>(exposed tagPin e i).val) (L.header es q base)

theorem entryPin_read (base : Boot.Tape h d) (addr : ℕ) (j : Fin (W+1)) (e : E→Bool) (q : Bits (bits slot es)) :
    Sum.elim (Sum.elim e q) id (L.entryPin es tagPin base addr j)=
      TraceWords.bits (TraceBanks.wide (L.tape es tagPin base e q addr)) j := by
  change _=((L.tape es tagPin base e q addr).val.testBit j.val)
  have hw : h≤W:=by rw [Native.wordBits_linear];omega
  by_cases a:addr<2^h
  · let i : Row h:=⟨addr,a⟩
    have small:=(exposed tagPin e i).isLt.trans_le (Nat.pow_le_pow_right (by decide) hw)
    simp only [entryPin,tape,Boot.tagRows,dite_eq_left a]
    change _ = (((exposed tagPin e i).val : Word W).val).testBit j.val
    rw [Fin.val_cast_of_lt small]
    by_cases b:j.val<h
    · let bit : Fin h:=⟨j.val,b⟩
      have got:=congrFun ((Computability.VPVNP.RAMSerialization.wordBits h).apply_symm_apply (fun z=>e (tagPin (i,z)))) bit
      simp only [dite_eq_left b,Sum.elim_inl]
      exact ((Computability.VPVNP.LiveHeader.testBit_wordBits (exposed tagPin e i) bit).trans got).symm
    · simp only [dite_eq_right b,Sum.elim_inr,id_eq]
      exact (Nat.testBit_lt_two_pow ((exposed tagPin e i).isLt.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt b)))).symm
  · simp only [entryPin,tape,Boot.tagRows,dite_eq_right a]
    by_cases b:j.val<W
    · let bit : Fin W:=⟨j.val,b⟩
      have got:=L.headerBit_read es addr bit q base
      simp only [dite_eq_left b]
      cases hit:L.headerBit es addr bit with
      | none => simpa only [hit,Option.map_none,Option.getD_none,Sum.elim_inr,id_eq] using got.symm
      | some pin => simpa only [hit,Option.map_some,Option.getD_some,Sum.elim_inl,Sum.elim_inr] using got.symm
    · simp only [dite_eq_right b,Sum.elim_inr,id_eq]
      exact (Nat.testBit_lt_two_pow ((L.header es q base addr).isLt.trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt b)))).symm

theorem read_header {size : ℕ} (base : Boot.Tape h d) (e : E→Bool) (q : Bits (bits slot es)) :
    headerRead (fun i:Fin size×Fin (W+1)=>L.entryPin es tagPin base i.1.val i.2) e q=
      (fun i=>TraceWords.bits (TraceBanks.wide (L.tape es tagPin base e q i.1.val)) i.2) :=
  funext fun i=>L.entryPin_read es tagPin base i.1.val i.2 e q

end Hierarchy.WireTelescope.CalendarTape.WordSlots

end
end OAI
