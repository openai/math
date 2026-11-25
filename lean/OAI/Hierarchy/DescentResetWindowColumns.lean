import OAI.Hierarchy.DescentFallbackPacket
import OAI.Hierarchy.DescentProjectedResetShelves
import OAI.Hierarchy.DescentFallbackPeriodBanks

namespace OAI
/-! # The actual tagged shape and signed-slot columns consumed by every reset root -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedColony DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open DescentSharedCableNames DescentSharedCableNames.Stage DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap t H G M w field : ℕ}
local notation "b" => DescentSignedCableCodec.width D cap
def spec (shape : Bank) (signed : Fin (2*cap)→Bank) (t D : ℕ) : Column L cap→Query
  | .inl (which,i)=>⟨shape,t,L,i,which.val⟩
  | .inr (j,i)=>⟨signed j,DescentSignedCableCodec.width D cap,L,i,0⟩

def maxBits (t D cap L : ℕ) := max (t*L) (DescentSignedCableCodec.width D cap*L)

theorem word_bound (shape : Bank) (signed : Fin (2*cap)→Bank) (a : Column L cap) :
    (spec shape signed t D a).loBits≤ maxBits t D cap L := by
  rcases a with ⟨which,i⟩|⟨j,i⟩
  · exact le_max_left ..
  · exact le_max_right ..

def bankAt (shape : Bank) (signed : Fin (2*cap)→Bank) (t D base H G M : ℕ) (a : Column L cap) : Bank :=
  let beginAt:=start base (maxBits t D cap L) H G M ((column L cap) a).val
  ⟨(spec shape signed t D a).out beginAt H G M,Nat.clog 2 (H*chunks G M)⟩

theorem window_columns (shape : Bank) (signed : Fin (2*cap)→Bank) (base : ℕ) (mem : Memory w)
    (oldCodes : Fin H→Fin G→Fin L→Cell t)
    (chips : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (shapeRead : Reads shape (fun v hi=>encode t L (oldCodes v hi)) M mem)
    (chipRead : ∀j,Reads (signed j)
      (fun v hi=>encode b L (fun x=>DescentSignedCableCodec.encode (chips v hi x j))) M mem)
    (safe : ∀a : Column L cap,(spec shape signed t D a).Room
      (start base (maxBits t D cap L) H G M ((column L cap) a).val) H G M field w) :
    let startAt:=start base (maxBits t D cap L) H G M
    let job:=fun j=>let a:=(column L cap).symm j
            (spec shape signed t D a).job (startAt j.val) (by simpa only [a,Equiv.apply_symm_apply] using safe a)
    let phase:=series (catalog job)
    let bank:=bankAt shape signed t D base H G M
    phase.Runs mem ∧ phase.ticks=(∑j,(job j).ticks)+4 ∧
      (∀x : Fin L,Reads (bank (.inl (0,x))) (fun v hi=>((oldCodes v hi x).val:Cell field)) M (phase.image mem)) ∧
      (∀x : Fin L,Reads (bank (.inl (1,x))) (fun v hi=>((oldCodes v hi x).val+1:Cell field)) M (phase.image mem)) ∧
      (∀j x,Reads (bank (.inr (j,x)))
        (fun v hi=>((DescentSignedCableCodec.encode (chips v hi x j)).val:Cell field)) M (phase.image mem)) ∧
      ∀a,a<base ∨ base+stride (maxBits t D cap L) H G M*count L cap≤a→phase.image mem a=mem a := by
  let Q : Fin (count L cap)→Query:=fun j=>spec shape signed t D ((column L cap).symm j)
  let val (a : Column L cap) :
      Fin H→Fin G→Fin (spec shape signed t D a).slots→Cell (spec shape signed t D a).bytes :=
    match a with
    | .inl _=>oldCodes
    | .inr (j,_)=>fun v g x=>DescentSignedCableCodec.encode (chips v g x j)
  have resident (a : Column L cap) : Reads (spec shape signed t D a).source
      (fun v g=>encode _ _ (val a v g)) M mem := by
    rcases a with ⟨which,x⟩|⟨j,x⟩
    · exact shapeRead
    · exact chipRead j
  have room (j : Fin (count L cap)) : (Q j).Room (start base (maxBits t D cap L) H G M j.val) H G M field w:=
    by simpa [Q] using safe ((column L cap).symm j)
  obtain ⟨run,fee,read,hold⟩:=publish Q base (maxBits t D cap L)
    (fun j=>word_bound shape signed ((column L cap).symm j)) room (fun j=>val ((column L cap).symm j))
    mem (fun j=>resident ((column L cap).symm j))
  let values (a : Column L cap) (h : Fin H) (g : Fin G) : Cell field :=
    ((val a h g (spec shape signed t D a).index).val + (spec shape signed t D a).plus : Cell field)
  have readColumn (a : Column L cap) : Reads (bankAt shape signed t D base H G M a) (values a) M
      ((series (catalog fun j => (Q j).job (start base (maxBits t D cap L) H G M j.val) (room j))).image mem) := by
    have atIndex := read ((column L cap) a)
    change Reads ⟨(spec shape signed t D ((column L cap).symm ((column L cap) a))).out
        (start base (maxBits t D cap L) H G M ((column L cap) a).val) H G M, _⟩
      (values ((column L cap).symm ((column L cap) a))) M _ at atIndex
    rw [Equiv.symm_apply_apply] at atIndex
    exact atIndex
  refine ⟨run,fee,?_,?_,?_,hold⟩
  · intro x
    simpa [Q,values,val,spec] using readColumn (.inl (0,x))
  · intro x
    simpa [Q,values,val,spec] using readColumn (.inl (1,x))
  · intro j x
    simpa [Q,values,val,spec] using readColumn (.inr (j,x))

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
