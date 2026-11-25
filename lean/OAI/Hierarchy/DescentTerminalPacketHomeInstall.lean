import OAI.Hierarchy.DescentTerminalPacketHomeRAM
import OAI.Hierarchy.DescentTerminalPrimitiveSpace
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Installing the original frozen-home lookup for every final public packet -/
namespace Hierarchy.DescentTerminalPacketHomeRAM
open ProtocolRAM DescentTerminalPrimitiveArena Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
namespace Expansion

/-- Both banks are full dyadic lookup banks. The source ancestry page remains
where the dated hop last wrote it. -/
def layout (base n : ℕ) (frozen : Bank) : Layout :=
  ⟨⟨base,Nat.clog 2 n⟩,frozen,⟨base+pad n,Nat.clog 2 n⟩⟩
def stop (base n : ℕ) := base+pad n+pad n

variable {n K H w : ℕ} (base : ℕ) (frozen : Bank) (number : Fin n→Fin K)
local notation "L" => layout base n frozen
def program := (DescentStaticWordColumn.program w base (literal number) n).seq
  (DescentTerminalPacketHomeRAM.program L w n)
def image (m : Memory w) := after L n (DescentStaticWordColumn.image base (literal number) m n)

theorem room (low : frozen.base+frozen.size≤base) (cap : K≤frozen.size) (word : stop base n<2^w) :
    Room L w n K := by
  have wide : base+pad n+pad n<2^w:=word
  have row := covered n
  have old : 0<frozen.size := Nat.two_pow_pos _
  exact ⟨⟨Nat.two_pow_pos _,by change pad n<_;omega,le_rfl⟩,
    ⟨old,by change frozen.size<2^w;omega,low.trans (Nat.le_add_right ..)⟩,
    row,cap,row,(Nat.add_le_add_left row (base+pad n)).trans_lt wide⟩

theorem install (m : Memory w) (low : frozen.base+frozen.size≤base) (cap : K≤frozen.size)
    (word : stop base n<2^w) :
    (program (w:=w) base frozen number).Exec m (image base frozen number m) (8+38*n) ∧
      CheapCode (program (w:=w) base frozen number) ∧
      ∀a,a<base ∨ stop base n≤a→image base frozen number m a=m a := by
  have fit := room base frozen low cap word
  have wide : base+pad n+pad n<2^w:=word
  have row:=covered n
  have put : (DescentStaticWordColumn.program w base (literal number) n).Exec m
      (DescentStaticWordColumn.image base (literal number) m n) (4+10*n) :=
    DescentStaticWordColumn.mount base n (literal number) m (by omega)
  have read_:=run L fit (DescentStaticWordColumn.image base (literal number) m n)
  have time_ : 4+10*n+(4+28*n)=8+38*n:=by omega
  refine ⟨time_ ▸ put.then read_.1,cheap_seq (DescentStaticWordColumn.cheap w base (literal number) n) read_.2,?_⟩
  intro a outside
  have out_ : a<base ∨ base+pad n+pad n≤a := outside
  have second : a<(L).dest.base ∨ (L).dest.base+n≤a := by change a<base+pad n ∨ base+pad n+n≤a;omega
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a second).trans
    (DescentStaticWordColumn.frame base n (literal number) m a (by omega))

theorem reads (m : Memory w) (low : frozen.base+frozen.size≤base) (cap : K≤frozen.size)
    (word : stop base n<2^w) (home : Fin K→Fin H)
    (written : ∀i:Fin K,m (frozen.base+i.val)=((home i).val:Word w))
    (i : Fin n) :
    (L).dest.read (image base frozen number m) (i.val:Word w)=((home (number i)).val:Word w) := by
  apply source L (room base frozen low cap word) number home
  · intro j
    change DescentStaticWordColumn.image base (literal number) m n (base+j.val)=_
    rw [DescentStaticWordColumn.read base n (literal number) _ j.isLt]
    simp only [literal,dite_eq_left j.isLt,Fin.eta]
  · intro j
    have small : frozen.base+j.val<base := (Nat.add_lt_add_left (j.isLt.trans_le cap) _).trans_le low
    exact (DescentStaticWordColumn.frame base n (literal number) _ _ (.inl small)).trans (written j)

/-- The index is installed once. Its native scan has just two nested reads
irrespective of how many frozen digits occurred in the dated execution. -/
theorem tariff :
    DescentStaticWordColumn.names (program (w:=w) base frozen number)+(8+38*n)=53*n+82 := by
  unfold program DescentTerminalPacketHomeRAM.program
  rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_scan]
  change 15*(n+1)+(11+4*12)+(8+38*n)=_;omega

/-- The actual ordinal ROM uses only tensor dimensions. In particular its
instruction words are independent of every chosen chronology. -/
def calendarWord (E j rest kept a : ℕ) : ℕ :=
  if h:a<E*2^(j+rest) then calendar E j rest kept ⟨a,h⟩ else 0

def fixedProgram (w base E j rest kept : ℕ) (frozen : Bank) :=
  let rows := E*2^(j+rest)
  (DescentStaticWordColumn.program w base (calendarWord E j rest kept) rows).seq
    (DescentTerminalPacketHomeRAM.program (layout base rows frozen) w rows)

theorem fixed_code {E j rest kept K : ℕ} (w base : ℕ) (frozen : Bank)
    (number : Fin (E*2^(j+rest))→Fin K)
    (coordinates : ∀i,(number i).val=calendar E j rest kept i) :
    fixedProgram w base E j rest kept frozen=program (w:=w) base frozen number := by
  have same : calendarWord E j rest kept=literal number := by
    funext a
    by_cases h:a<E*2^(j+rest)
    · simpa [calendarWord,literal,h] using (coordinates ⟨a,h⟩).symm
    · simp [calendarWord,literal,h]
  unfold fixedProgram program
  rw [same]

theorem extent_le (base n : ℕ) : stop base n≤base+4*n+2 := by
  have := pad_le n
  unfold stop;omega

end Expansion
end
end Hierarchy.DescentTerminalPacketHomeRAM

end OAI
