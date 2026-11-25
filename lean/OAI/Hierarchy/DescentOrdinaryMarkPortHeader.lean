import OAI.Hierarchy.DescentOrdinaryMarkShape
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! Reuse the genuine old four-hop endpoint table at the incoming packed group width. -/
namespace Hierarchy.DescentOrdinaryMarkProject.Shape
open DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) (floor : ℕ) {w : ℕ}

def portColumn (j : ℕ) : Bank := ⟨floor+j*s.pitch,Nat.clog 2 (1+s.oldHosts+s.sourceRows)⟩
def portChart (visited : Bank) : Ports s.paths :=
  ⟨fun p=>s.portColumn floor (2+p.val),visited,s.portColumn floor 0,s.portColumn floor 1⟩
def portWord (i : ℕ) :=
  let col:=i/s.pitch
  let idx:=i%s.pitch
  let c:=chunks (s.groups*s.blocks) s.oldLanes
  if col=0 then c*idx else if col=1 then idx%c else idx/c*s.paths+(col-2)
def portPhase (w : ℕ) : DescentSixParty.Chronology.NativePhase w :=
  ⟨DescentStaticWordColumn.program w floor s.portWord s.portWords,4+10*s.portWords,
   fun m=>DescentStaticWordColumn.image floor s.portWord m s.portWords,DescentStaticWordColumn.cheap w floor s.portWord s.portWords⟩

theorem port_any (m : Memory w) (room : s.markStart floor<2^w) :
    (s.portPhase floor w).Runs m ∧
      ∀j,j<floor ∨ s.markStart floor≤j→(s.portPhase floor w).image m j=m j :=
  ⟨DescentStaticWordColumn.mount floor s.portWords s.portWord m room,
   fun j away => DescentStaticWordColumn.frame floor s.portWords s.portWord m j away⟩

private theorem port_read (m : Memory w) (j : Fin (s.paths+2)) (k : Fin s.pitch) :
    (s.portPhase floor w).image m ((s.portColumn floor j.val).base+k.val)=
      (s.portWord (j.val*s.pitch+k.val):Word w) := by
  have h : j.val*s.pitch+k.val<s.portWords := calc
    j.val*s.pitch+k.val < j.val*s.pitch+s.pitch := Nat.add_lt_add_left k.isLt _
    _ = (j.val+1)*s.pitch := (Nat.succ_mul _ _).symm
    _ ≤ (s.paths+2)*s.pitch := Nat.mul_le_mul_right _ j.isLt
  simpa only [portPhase,portColumn,Nat.add_assoc] using DescentStaticWordColumn.read floor s.portWords s.portWord m h

private theorem width (s : Shape) : 1+s.oldHosts+s.sourceRows≤ s.pitch :=span_ge _

private theorem port_word (j : ℕ) (k : Fin s.pitch) :
    s.portWord (j*s.pitch+k.val)=
      if j=0 then chunks (s.groups*s.blocks) s.oldLanes*k.val else if j=1 then
        k.val%chunks (s.groups*s.blocks) s.oldLanes else k.val/chunks (s.groups*s.blocks) s.oldLanes*s.paths+(j-2) := by
  have hp : 0<s.pitch := Nat.zero_lt_of_lt k.isLt
  have div : (j*s.pitch+k.val)/s.pitch=j :=by
    rw [Nat.mul_comm j s.pitch,Nat.mul_add_div hp,Nat.div_eq_of_lt k.isLt,Nat.add_zero]
  have md : (j*s.pitch+k.val)%s.pitch=k.val :=by
    rw [Nat.mul_comm j s.pitch,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt k.isLt]
  simp only [portWord,div,md]

theorem port_mounted (visited : Bank) (R : Fin s.oldHosts→Fin s.paths→Option (Fin s.oldHosts)) (m : Memory w)
    (fit : visited.Fits w floor) (size : s.oldHosts*s.paths≤visited.size)
    (seen : ∀v j,m (visited.base+(v.val*s.paths+j.val))=(target (R v j):Word w)) :
    Mounted (s.portChart floor visited) R ((s.portPhase floor w).image m) (s.groups*s.blocks) s.oldLanes := by
  let c:=chunks (s.groups*s.blocks) s.oldLanes
  have range := s.width
  have rowVal (p : Row s.oldHosts (s.groups*s.blocks) s.oldLanes) :
      (row _ _ _ p).val=p.1.val*c+p.2.val :=by
    simp [c,row,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  have qr (p : Row s.oldHosts (s.groups*s.blocks) s.oldLanes) :
      (row _ _ _ p).val/c=p.1.val ∧ (row _ _ _ p).val%c=p.2.val :=by
    have hp : 0<c := Nat.zero_lt_of_lt p.2.isLt
    rw [rowVal,Nat.mul_comm p.1.val c]
    constructor
    · rw [Nat.mul_add_div hp,Nat.div_eq_of_lt p.2.isLt,Nat.add_zero]
    · rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt p.2.isLt]
  have rowSmall (p : Row s.oldHosts (s.groups*s.blocks) s.oldLanes) : (row _ _ _ p).val<s.pitch :=
    (row _ _ _ p).isLt.trans_le ((Nat.le_add_left ..).trans range)
  constructor
  · intro p j
    have bound : 2+j.val<s.paths+2 :=by omega
    exact (port_read (s:=s) (floor:=floor) m ⟨2+j.val,bound⟩ ⟨_,rowSmall p⟩).trans (by
      rw [s.port_word (2+j.val) ⟨_,rowSmall p⟩]
      have nz : 2+j.val ≠ 0 := by omega
      have ne : 2+j.val ≠ 1 := by omega
      have sub : 2+j.val-2 = j.val := by omega
      simpa only [ite_eq_right nz,ite_eq_right ne,sub] using
        congrArg (fun n : ℕ => ((n*s.paths+j.val : ℕ) : Word w)) (qr p).1)
  · intro v j
    have e : v.val*s.paths+j.val<s.oldHosts*s.paths :=
      (Nat.add_lt_add_left j.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
    exact (DescentStaticWordColumn.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left (e.trans_le size) _).trans_le fit.2.2))).trans (seen v j)
  · intro v
    have small : v.val<s.pitch := (v.isLt.trans_le (by omega : s.oldHosts≤ s.pitch))
    exact (port_read (s:=s) (floor:=floor) m ⟨0,by omega⟩ ⟨_,small⟩).trans (by rw [s.port_word 0 ⟨_,small⟩];simp)
  · intro p
    exact (port_read (s:=s) (floor:=floor) m ⟨1,by omega⟩ ⟨_,rowSmall p⟩).trans (by
      rw [s.port_word 1 ⟨_,rowSmall p⟩]
      simpa using congrArg (fun n : ℕ => (n : Word w)) (qr p).2)

theorem port_access (visited prior : Bank) (vfit : visited.Fits w floor) (vs : s.oldHosts*s.paths≤visited.size)
    (pfit : prior.Fits w floor) (ps : s.sourceRows≤prior.size) (room : s.markStart floor<2^w) :
    Accessible (s.portChart floor visited) prior s.oldHosts (s.groups*s.blocks) s.oldLanes w (s.markStart floor) :=by
  have ranges := s.width
  have grow (B : Bank) (h : B.Fits w floor) : B.Fits w (s.markStart floor) :=
    ⟨h.1,h.2.1,h.2.2.trans (Nat.le_add_right ..)⟩
  have fit (j : ℕ) (lt : j<s.paths+2) : (s.portColumn floor j).Fits w (s.markStart floor) :=by
    change 0 < s.pitch ∧ s.pitch < 2^w ∧ floor+j*s.pitch+s.pitch ≤ s.markStart floor
    have k : (j+1)*s.pitch ≤ (s.paths+2)*s.pitch := Nat.mul_le_mul_right s.pitch lt
    rw [Nat.succ_mul] at k
    have end₀ : floor+j*s.pitch+s.pitch ≤ s.markStart floor := by
      simpa only [markStart,portWords,Nat.add_assoc] using Nat.add_le_add_left k floor
    have spanRoom : s.pitch < 2^w :=
      (Nat.le_add_left s.pitch (floor+j*s.pitch)).trans_lt (end₀.trans_lt room)
    exact ⟨Nat.two_pow_pos _,spanRoom,end₀⟩
  exact ⟨fun i=>fit _ (by omega),fun _=>by change s.sourceRows≤ s.pitch;omega,grow _ vfit,vs,
    fit 0 (by omega),by change s.oldHosts≤ s.pitch;omega,fit 1 (by omega),by change s.sourceRows≤ s.pitch;omega,
    grow _ pfit,ps⟩


end
end Hierarchy.DescentOrdinaryMarkProject.Shape

end OAI
