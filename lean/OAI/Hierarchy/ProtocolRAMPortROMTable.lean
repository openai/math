import OAI.Hierarchy.ProtocolRAMOccurrenceHeader
import OAI.Hierarchy.ProtocolRAMStaticSlabs

namespace OAI
/-! # Finite bank allocation for public row and port directories -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM StockCommit
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
noncomputable section
variable {jobs w : ℕ}

namespace PortROM

/-- Directories may be shared by all events of the same row shape. -/
structure Table (jobs : ℕ) where
  base : ℕ
  rows : Fin jobs→ℕ
  ports : ℕ
  maxRows : ℕ
  bounded : ∀ i,rows i ≤ maxRows

def Table.stride (s : Table jobs) := 12*(s.maxRows*s.ports)+8
def Table.stop (s : Table jobs) := s.base+jobs*s.stride
def Table.header (s : Table jobs) (i : Fin jobs) : PortHeader :=
  ⟨s.base+i.val*s.stride,s.rows i,s.ports⟩

theorem Table.bound (s : Table jobs) (i : Fin jobs) :
    (s.header i).stop ≤ s.base+(i.val+1)*s.stride := by
  have h := (s.header i).span
  have hc := Nat.mul_le_mul_right s.ports (s.bounded i)
  change _ ≤ s.base+i.val*s.stride+12*(s.rows i*s.ports)+8 at h
  rw [Nat.succ_mul]
  dsimp only [stride] at *
  omega

theorem Table.disjoint (s : Table jobs) :
    ProtocolRAMStaticSlabs.Disjoint (fun i=>(s.header i).start) (fun i=>(s.header i).stop) := by
  apply ProtocolRAMStaticSlabs.disjoint_of_order
  intro i j hij
  exact (s.bound i).trans (Nat.add_le_add_left (Nat.mul_le_mul_right s.stride hij) _)

def Table.words (s : Table jobs) (rest : Memory w) : Memory w :=
  ProtocolRAMStaticSlabs.mounted (fun i=>(s.header i).start) (fun i=>(s.header i).stop)
    (fun i=>(s.header i).load rest) rest

theorem Table.end_le (s : Table jobs) (i : Fin jobs) : (s.header i).stop ≤ s.stop :=
  (s.bound i).trans (Nat.add_le_add_left (Nat.mul_le_mul_right s.stride i.isLt) _)

theorem Table.loaded (s : Table jobs) (rest : Memory w) (wide : 0<w) (fit : s.stop<2^w)
    (i : Fin jobs) : (s.header i).Loaded (s.words rest) := by
  apply ((s.header i).load_ok rest wide ((s.end_le i).trans_lt fit)).frame
  intro x lo hi
  exact ProtocolRAMStaticSlabs.cell_on _ _ s.disjoint ⟨lo,hi⟩

theorem Table.frame (s : Table jobs) (rest : Memory w) (x : ℕ) (away : x < s.base ∨ s.stop≤x) :
    s.words rest x=rest x := by
  apply ProtocolRAMStaticSlabs.outside
  rintro i ⟨l,u⟩
  rcases away with lo|hi
  · exact Nat.not_lt_of_ge ((Nat.le_add_right s.base _).trans l) lo
  · exact Nat.not_lt_of_ge (s.end_le i |>.trans hi) u

theorem Table.linear (s : Table jobs) (z f : ℕ) (small : s.maxRows≤f*2^z) :
    s.stop ≤ s.base+(jobs*(12*(f*s.ports)+8))*2^z := by
  have le := Nat.mul_le_mul_right s.ports small
  have u : 1≤2^z := Nat.one_le_two_pow
  have row : s.stride≤(12*(f*s.ports)+8)*2^z := by
    dsimp only [stride]
    nlinarith only [le,u]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left jobs row) s.base).trans_eq (by ac_rfl)
end PortROM

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
