import OAI.Hierarchy.DescentTerminalBookWeights
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # The six original field-weight dictionaries of a printed terminal book -/
namespace Hierarchy.DescentTerminalLocalPortBook.Book.WeightShelf
open DescentDyadicSpan DescentTerminalPrintedFieldsRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable (V A : ℕ)
local notation "M" => V*A
local notation "bits" => Book.tokenBits (V*A)
local notation "cap" => capacities 4 V M A bits
local notation "scale" => strides 4 V M A bits

def words := ∑ i : Fin 6,span (cap i)
def offset (j : ℕ) := ∑ i : Fin 6,if i.val<j then span (cap i) else 0
def finish (base : ℕ) := base+words V A
def banks (base : ℕ) (i : Fin 6) : Bank := ⟨base+offset V A i.val,Nat.clog 2 (cap i)⟩

theorem offset_mono : Monotone (offset V A) := by
  intro i j low
  apply Finset.sum_le_sum
  intro k _
  split_ifs <;> omega

theorem at_next (i : Fin 6) : offset V A (i.val+1)=offset V A i.val+span (cap i) := by
  have each (k : Fin 6) : (if k.val < i.val+1 then span (cap k) else 0) =
      (if k.val < i.val then span (cap k) else 0)+(if k=i then span (cap i) else 0) := by
    by_cases eqn : k=i
    · subst k;simp
    · have ne : k.val≠i.val:=fun h=>eqn (Fin.ext h)
      by_cases lt : k.val < i.val
      · simp only [ite_eq_left lt,ite_eq_left (show k.val < i.val+1 by omega),ite_eq_right eqn,Nat.add_zero]
      · simp only [ite_eq_right lt,ite_eq_right (show ¬k.val < i.val+1 by omega),ite_eq_right eqn,Nat.add_zero]
  unfold offset
  simp_rw [each]
  rw [Finset.sum_add_distrib]
  simp

theorem offset_end (n : ℕ) : offset V A n≤words V A := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

def data (j : ℕ) :=
  if hit : ∃i : Fin 6,offset V A i.val≤j ∧ j<offset V A (i.val+1) then
    ((weights (cap hit.choose) (scale hit.choose))[j-offset V A hit.choose.val]?).getD 0
  else 0

theorem at_word (i : Fin 6) (v : Fin (cap i)) :
    data V A (offset V A i.val+v.val)=v.val*scale i := by
  let x:=offset V A i.val+v.val
  have small:=v.isLt.trans_le (span_ge (cap i))
  have hit : ∃j : Fin 6,offset V A j.val≤x ∧ x<offset V A (j.val+1) := by
    refine ⟨i,Nat.le_add_right ..,?_⟩
    rw [at_next]
    exact Nat.add_lt_add_left small _
  have unique : hit.choose=i := by
    have found:=hit.choose_spec
    apply Fin.ext
    rcases lt_trichotomy hit.choose.val i.val with lt|eqn|gt
    · have prev:=offset_mono V A (show hit.choose.val+1 ≤ i.val by omega)
      dsimp only [x] at found
      omega
    · exact eqn
    · have prev:=offset_mono V A (show i.val+1≤hit.choose.val by omega)
      rw [at_next] at prev
      dsimp only [x] at found
      omega
  change data V A x=_
  rw [data,dite_eq_left hit,unique]
  simp [x,weights,v.isLt]

def program (base w : ℕ) := DescentStaticWordColumn.program w base (data V A) (words V A)
def memory {w : ℕ} (base : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (data V A) m (words V A)

theorem room (base out w : ℕ) (after : finish V A base≤out) (space : out<2^w) (i : Fin 6) :
    (banks V A base i).Fits w out := by
  have low:=offset_end V A (i.val+1)
  rw [at_next] at low
  change base+words V A≤out at after
  change 0<span (cap i) ∧ span (cap i)<2^w ∧ base+offset V A i.val+span (cap i)≤out
  exact ⟨span_pos _,by omega,by omega⟩

theorem execute {w : ℕ} (base : ℕ) (m : Memory w) (space : finish V A base<2^w) :
    (program V A base w).Exec m (memory V A base m) (4+10*words V A) ∧
    (∀(i : Fin 6) (v : Fin (cap i)), (banks V A base i).read (memory V A base m) (v.val:Word w)=
      ((v.val*scale i:ℕ):Word w)) ∧
    (∀a,a<base ∨ finish V A base≤a → memory V A base m a=m a) := by
  refine ⟨DescentStaticWordColumn.mount base _ _ m space,?_,DescentStaticWordColumn.frame base _ _ m⟩
  intro i v
  have endRow:=offset_end V A (i.val+1)
  rw [at_next] at endRow
  have small:=v.isLt.trans_le (span_ge (cap i))
  have fitted:=room V A base _ w le_rfl space i
  have narrow : v.val<2^w:=small.trans (fitted.2.1)
  rw [Bank.read,Fin.val_cast_of_lt narrow,Nat.mod_eq_of_lt (show v.val < (banks V A base i).size from small)]
  change memory V A base m (base+offset V A i.val+v.val)=_
  rw [Nat.add_assoc]
  exact (DescentStaticWordColumn.read base (words V A) (data V A) m (by omega)).trans
    (congrArg (fun n : ℕ=>(n:Word w)) (at_word V A i v))

theorem words_le (W q : ℕ) : words V A≤fixedWords V A W q := by
  apply le_trans _ (lookup_le_fixed V A W q)
  change _≤_+_+_+(∑i : Fin 6,span (cap i))
  exact Nat.le_add_left ..

theorem finish_le (W q base : ℕ) : finish V A base≤base+fixedWords V A W q :=
  Nat.add_le_add_left (words_le V A W q) base

theorem tariff (W q base w : ℕ) : CheapCode (program V A base w) ∧
    DescentStaticWordColumn.names (program V A base w)=15*(words V A+1) ∧
    4+10*words V A+7*DescentStaticWordColumn.names (program V A base w)≤
      115*(fixedWords V A W q+1) := by
  have names:=DescentStaticWordColumn.names_mount w base (data V A) (words V A)
  have total:=words_le V A W q
  exact ⟨DescentStaticWordColumn.cheap w base (data V A) (words V A),names,by
    change 4+10*words V A+7*DescentStaticWordColumn.names (DescentStaticWordColumn.program w base (data V A) (words V A))≤_
    rw [names]
    omega⟩

end
end Hierarchy.DescentTerminalLocalPortBook.Book.WeightShelf

end OAI
