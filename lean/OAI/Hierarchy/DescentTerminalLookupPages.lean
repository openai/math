import OAI.Hierarchy.DescentTerminalPrimitiveSpace
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Installing three finite public columns before the dated program -/
namespace Hierarchy.DescentTerminalControlROMs
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentTerminalPrimitiveArena
open scoped Fin.CommRing
noncomputable section

structure Layout where
  bytes : ℕ
  binWidth : ℕ
  rows : ℕ
  start : ℕ
  count : Fin bytes → ℕ

namespace Layout
variable (t : Layout)
def total : Bank := ⟨t.start,Nat.clog 2 t.bytes⟩
def modulo : Bank := ⟨t.start+pad t.bytes,Nat.clog 2 t.rows⟩
def boundaries := t.start+(pad t.bytes+pad t.rows)
def words := pad t.bytes+pad t.rows+(t.rows+1)
def stop := t.start+t.words

def wordAt (j : ℕ) : ℕ :=
  if j<pad t.bytes then
    if h:j<t.bytes then t.count ⟨j,h⟩ else 0
  else if j<pad t.bytes+pad t.rows then (j-pad t.bytes)%t.binWidth
  else
    let u := j-(pad t.bytes+pad t.rows)
    u+(t.binWidth-u%t.binWidth)

def program (w : ℕ) := DescentStaticWordColumn.program w t.start t.wordAt t.words
def image {w : ℕ} (m : Memory w) := DescentStaticWordColumn.image t.start t.wordAt m t.words

structure Reads {w : ℕ} (m : Memory w) : Prop where
  counts : ∀i:Fin t.bytes,t.total.read m (i.val:Word w)=(t.count i:Word w)
  remainder : ∀i:Fin t.rows,t.modulo.read m (i.val:Word w)=((i.val%t.binWidth:ℕ):Word w)
  nextRow : ∀i:Fin (t.rows+1),m (t.boundaries+i.val)=((i.val+(t.binWidth-i.val%t.binWidth):ℕ):Word w)

theorem ranges :
    t.total.base+t.total.size≤t.stop ∧ t.modulo.base+t.modulo.size≤t.stop ∧
    t.boundaries+(t.rows+1)≤t.stop := by
  change t.start+pad t.bytes≤t.start+(pad t.bytes+pad t.rows+(t.rows+1)) ∧
    t.start+pad t.bytes+pad t.rows≤t.start+(pad t.bytes+pad t.rows+(t.rows+1)) ∧
    t.start+(pad t.bytes+pad t.rows)+(t.rows+1)≤t.start+(pad t.bytes+pad t.rows+(t.rows+1))
  omega

theorem read_image {w : ℕ} (m : Memory w) (room : t.stop<2^w) : t.Reads (t.image m) := by
  have rows := covered t.rows
  have chars := covered t.bytes
  have high : t.start+(pad t.bytes+pad t.rows+(t.rows+1))<2^w := room
  have in_ (j : ℕ) (hj : j<t.words) :
      t.image m (t.start+j)=(t.wordAt j:Word w) :=
    DescentStaticWordColumn.read t.start t.words t.wordAt m hj
  constructor
  · intro i
    have index := i.isLt
    have fits : i.val<2^w := by omega
    have small := index.trans_le chars
    change t.image m (t.start+(i.val:Word w).val%pad t.bytes)=_
    rw [Fin.val_cast_of_lt fits,Nat.mod_eq_of_lt small,in_ i.val (by unfold words;omega)]
    simp only [wordAt,ite_eq_left small,dite_eq_left index,Fin.eta]
  · intro i
    have index := i.isLt
    have fits : i.val<2^w := by omega
    have small := index.trans_le rows
    change t.image m (t.start+pad t.bytes+(i.val:Word w).val%pad t.rows)=_
    rw [Fin.val_cast_of_lt fits,Nat.mod_eq_of_lt small,Nat.add_assoc,in_ _ (by unfold words;omega)]
    have left : ¬pad t.bytes+i.val<pad t.bytes := by omega
    have right : pad t.bytes+i.val<pad t.bytes+pad t.rows := by omega
    simp only [wordAt,ite_eq_right left,ite_eq_left right,Nat.add_sub_cancel_left]
  · intro i
    have index := i.isLt
    change t.image m (t.start+(pad t.bytes+pad t.rows)+i.val)=_
    rw [Nat.add_assoc,in_ _ (by unfold words;omega)]
    have left : ¬(pad t.bytes+pad t.rows+i.val<pad t.bytes) := by omega
    have right : ¬(pad t.bytes+pad t.rows+i.val<pad t.bytes+pad t.rows) := by omega
    simp [wordAt,left,right]

theorem install {w : ℕ} (m : Memory w) (room : t.stop<2^w) :
    (t.program w).Exec m (t.image m) (4+10*t.words) ∧ CheapCode (t.program w) ∧
      t.Reads (t.image m) ∧ ∀a,a<t.start ∨ t.stop≤a→t.image m a=m a :=
  ⟨DescentStaticWordColumn.mount _ _ _ _ room,DescentStaticWordColumn.cheap w t.start t.wordAt t.words,t.read_image m room,
    DescentStaticWordColumn.frame t.start t.words t.wordAt m⟩

/-- The installer pays for the two genuinely padded address banks. The terminal
boundary tape then writes exactly one additional end marker. -/
theorem words_le : t.words≤2*t.bytes+3*t.rows+3 := by
  have b:=pad_le t.bytes
  have r:=pad_le t.rows
  unfold words;omega

theorem tariff (w : ℕ) :
    DescentStaticWordColumn.names (t.program w)+(4+10*t.words)=25*t.words+19 := by
  rw [program,DescentStaticWordColumn.names_mount];omega

theorem cost_le (w h : ℕ) (small : t.bytes≤2^(h/2)) :
    (DescentStaticWordColumn.names (t.program w)+(4+10*t.words))*(w+1)≤
      100*(2^(h/2)+t.rows+1)*(w+1) := by
  apply Nat.mul_le_mul_right
  rw [t.tariff]
  have cap:=t.words_le
  omega

theorem transfer {w : ℕ} {m m' : Memory w} (auth : t.Reads m)
    (retained : ∀j,t.start≤j→j<t.stop→m' j=m j) : t.Reads m' := by
  have read (b : Bank) (lo : t.start≤b.base) (hi : b.base+b.size≤t.stop) (u : Word w) :
      b.read m' u=b.read m u := by
    apply retained
    · exact lo.trans (Nat.le_add_right ..)
    · exact (Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le hi
  refine ⟨fun i=>(read t.total le_rfl t.ranges.1 _).trans (auth.counts i),
    fun i=>(read t.modulo (Nat.le_add_right ..) t.ranges.2.1 _).trans (auth.remainder i),
    fun i=>(retained _ (show t.start≤t.boundaries+i.val from (Nat.le_add_right ..).trans (Nat.le_add_right ..))
      ((Nat.add_lt_add_left i.isLt _).trans_le t.ranges.2.2)).trans (auth.nextRow i)⟩

end Layout
end
end Hierarchy.DescentTerminalControlROMs

end OAI
