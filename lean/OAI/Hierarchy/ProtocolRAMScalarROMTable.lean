import OAI.Hierarchy.ProtocolRAMPrices
import OAI.Hierarchy.ProtocolRAMBinarySpan
import OAI.Hierarchy.ProtocolRAMStaticSlabs

namespace OAI
/-! # Finite width lookup for scalar phase-price entries -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
noncomputable section
variable {phases w : ℕ}

namespace ScalarROM

structure Table (phases : ℕ) where
  base : ℕ
  kinds : ℕ
  stride : ℕ
  phase : Fin phases→PhasePrice

def Table.size (t : Table phases) := ProtocolRAMPurchaseSampler.span (t.kinds*t.stride)
def Table.stop (t : Table phases) := t.base+phases*t.size
def Table.bank (t : Table phases) (i : Fin phases) : Bank :=
  ⟨t.base+i.val*t.size,ProtocolRAMPurchaseSampler.bits (t.kinds*t.stride)⟩

theorem Table.end_row (t : Table phases) (i : Fin phases) :
    (t.bank i).base+t.size=t.base+(i.val+1)*t.size := by simp [bank,Nat.succ_mul,add_assoc]

theorem Table.end_le (t : Table phases) (i : Fin phases) : (t.bank i).base+t.size≤t.stop :=
  (t.end_row i).le.trans (Nat.add_le_add_left (Nat.mul_le_mul_right t.size i.isLt) t.base)

theorem Table.disjoint (t : Table phases) :
    ProtocolRAMStaticSlabs.Disjoint (fun i=>(t.bank i).base) (fun i=>(t.bank i).base+t.size) := by
  apply ProtocolRAMStaticSlabs.disjoint_of_order
  intro i j lt
  exact (t.end_row i).le.trans (Nat.add_le_add_left (Nat.mul_le_mul_right t.size lt) t.base)

def Table.words (t : Table phases) (rest : Memory w) : Memory w :=
  ProtocolRAMStaticSlabs.mounted (fun i=>(t.bank i).base) (fun i=>(t.bank i).base+t.size)
    (fun i=>(t.phase i).advice (t.bank i) t.kinds t.stride rest) rest

/-- Every live kind and stock quantity reads its true quantized price word. -/
def Table.Resident (t : Table phases) (m : Memory w) : Prop :=
  ∀ i : Fin phases,∀ j : Fin t.kinds,∀ n : Fin t.stride,
    (t.bank i).read m ((j.val*t.stride+n.val:ℕ):Word w) = ((t.phase i).word j.val n.val:Word w)

theorem Table.resident (t : Table phases) (rest : Memory w) (room : t.kinds*t.stride<2^w) :
    t.Resident (t.words rest) := by
  intro i j n
  have cap : t.kinds*t.stride≤(t.bank i).size := (ProtocolRAMPurchaseSampler.lt_span _).le
  have addr : ∀ r : Word w, (t.bank i).read (t.words rest) r=
      (t.bank i).read ((t.phase i).advice (t.bank i) t.kinds t.stride rest) r := by
    intro r
    apply ProtocolRAMStaticSlabs.cell_on _ _ t.disjoint
    exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _⟩
  exact (addr _).trans ((t.phase i).read_advice (t.bank i) _ _ _ _ rest j.isLt n.isLt room cap)

theorem Table.frame (t : Table phases) (rest : Memory w) (x : ℕ) (away : x<t.base ∨ t.stop≤x) :
    t.words rest x=rest x := by
  apply ProtocolRAMStaticSlabs.outside
  rintro i ⟨lo,hi⟩
  rcases away with h|h
  · exact Nat.not_lt_of_ge ((Nat.le_add_right t.base _).trans lo) h
  · exact Nat.not_lt_of_ge ((t.end_le i).trans h) hi

theorem Table.Resident.frame {t : Table phases} {old new : Memory w} (h : t.Resident old)
    (same : ∀ x,t.base≤x → x<t.stop → new x=old x) : t.Resident new := by
  intro i j n
  let r := ((j.val*t.stride+n.val:ℕ):Word w)
  have lt : r.val%(t.bank i).size<t.size := Nat.mod_lt _ (Nat.two_pow_pos _)
  have keep : (t.bank i).read new r=(t.bank i).read old r :=
    same _ ((Nat.le_add_right t.base _).trans (Nat.le_add_right _ _))
      ((Nat.add_lt_add_left lt _).trans_le (t.end_le i))
  exact keep.trans (h i j n)

theorem Table.size_le (t : Table phases) (z f : ℕ) (bounded : t.stride≤f*2^z) :
    t.stop≤t.base+(phases*(2*(t.kinds*f+1)))*2^z := by
  have h := ProtocolRAMPurchaseSampler.span_le (t.kinds*t.stride)
  have le := Nat.mul_le_mul_left t.kinds bounded
  have u : 1≤2^z := Nat.one_le_two_pow
  have sc : t.size≤(2*(t.kinds*f+1))*2^z := by
    change ProtocolRAMPurchaseSampler.span _≤_
    nlinarith only [h,le,u]
  exact (Nat.add_le_add_left (Nat.mul_le_mul_left phases sc) t.base).trans_eq (by ac_rfl)

end ScalarROM

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
