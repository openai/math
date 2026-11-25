import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentPackedPorts

namespace OAI
/-! # Fixed native banks for the first matching stage

The first matching stage reads a packed actor word and a host directory even
at sites without a live cable. Its public bank has one row for each packed
group chunk. The peer and offset tables use the same padded host numbering.
-/
namespace Hierarchy.DescentSeedInitialTable
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section

def bits (H G M D : ℕ) := Nat.clog 2 (max H (max (H*D) (H*chunks G M)))
def stride (H G M D : ℕ) := 2^bits H G M D
def count (H G M D : ℕ) := (D+8)*stride H G M D
def endAddress (base H G M D : ℕ) := base+count H G M D

theorem capacities (H G M D : ℕ) :
    H≤ stride H G M D ∧ H*D≤ stride H G M D ∧ H*chunks G M≤ stride H G M D := by
  have bound : max H (max (H*D) (H*chunks G M))≤ stride H G M D := Nat.le_pow_clog (by decide) _
  exact ⟨(Nat.le_max_left ..).trans bound,
    ((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans bound,
    ((Nat.le_max_right ..).trans (Nat.le_max_right ..)).trans bound⟩

def bank (base H G M D col : ℕ) : Bank := ⟨base+col*stride H G M D,bits H G M D⟩

def ports (base H G M D : ℕ) : Ports D where
  ids i := bank base H G M D (8+i.val)
  roster := bank base H G M D 0
  offsets := bank base H G M D 1
  chunks := bank base H G M D 2

def literal {H G M D : ℕ} (values : ℕ→ℕ→ℕ) (n : ℕ) :=
  let r:=stride H G M D
  values (n/r) (n%r)

def program (w base H G M D : ℕ) (values : ℕ→ℕ→ℕ) :=
  DescentStaticWordColumn.program w base (literal (H:=H) (G:=G) (M:=M) (D:=D) values) (count H G M D)

def image {w : ℕ} (base H G M D : ℕ) (values : ℕ→ℕ→ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image base (literal (H:=H) (G:=G) (M:=M) (D:=D) values) m (count H G M D)

theorem run {w : ℕ} (base H G M D : ℕ) (values : ℕ→ℕ→ℕ) (m : Memory w)
    (room : endAddress base H G M D<2^w) :
    (program w base H G M D values).Exec m (image base H G M D values m) (4+10*count H G M D) :=
  DescentStaticWordColumn.mount _ _ _ m room

theorem control (w base H G M D : ℕ) (values : ℕ→ℕ→ℕ) :
    DescentStaticWordColumn.names (program w base H G M D values)=15*(count H G M D+1) ∧
      CheapCode (program w base H G M D values) :=
  by
    refine ⟨DescentStaticWordColumn.names_mount ..,?_⟩
    intro P R K pc reg pub exit i
    exact DescentStaticWordColumn.cheap w base _ (count H G M D) pc reg pub exit i

theorem frame {w : ℕ} (base H G M D : ℕ) (values : ℕ→ℕ→ℕ) (m : Memory w)
    (a : ℕ) (away : a<base ∨ endAddress base H G M D≤a) :
    image base H G M D values m a=m a := DescentStaticWordColumn.frame _ _ _ _ _ away

theorem read {w H G M D : ℕ} (base : ℕ) (values : ℕ→ℕ→ℕ) (m : Memory w)
    {c j : ℕ} (col : c<D+8) (row : j<stride H G M D) :
    image base H G M D values m ((bank base H G M D c).base+j)=(values c j : Word w) := by
  let r:=stride H G M D
  have pos : 0<r := Nat.two_pow_pos _
  have below : c*r+j<(D+8)*r :=
    (Nat.add_lt_add_left row _).trans_le (by
      simpa only [Nat.succ_mul] using Nat.mul_le_mul_right r col)
  change image base H G M D values m ((base+c*r)+j)=_
  rw [Nat.add_assoc]
  change DescentStaticWordColumn.image base (literal (H:=H) (G:=G) (M:=M) (D:=D) values) m ((D+8)*r) (base+(c*r+j))=_
  rw [DescentStaticWordColumn.read _ _ _ _ below]
  change (values ((c*r+j)/r) ((c*r+j)%r):Word w)=_
  rw [Nat.mul_comm c r,Nat.mul_add_div pos,Nat.div_eq_of_lt row,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt row]

theorem bank_fits {w base H G M D c : ℕ} (col : c<D+8)
    (room : endAddress base H G M D<2^w) :
    (bank base H G M D c).Fits w (endAddress base H G M D) := by
  have stop : c*stride H G M D+stride H G M D≤(D+8)*stride H G M D := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right (stride H G M D) col
  change 0<stride H G M D ∧ stride H G M D<2^w ∧
    base+c*stride H G M D+stride H G M D≤endAddress base H G M D
  unfold endAddress count at *
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

end
end Hierarchy.DescentSeedInitialTable

end OAI
