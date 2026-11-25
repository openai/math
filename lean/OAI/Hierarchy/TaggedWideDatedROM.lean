import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.Hierarchy.TaggedWideDatedLayout
import OAI.Hierarchy.TaggedWideSiteNumber

namespace OAI
/-! # Public memory image for every role, candidate and coordinate page -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open ProbeStage.CoreBoard.HistoryRoles Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical BigOperators

/-- A read in an unmounted gap retains the underlying byte. Every initialized
entry carries its actual public value even when its literal value is zero. -/
def romAt {W : ℕ} (base : ℕ) (n : ℕ) (data : Fin n→ℕ) (a : ℕ) : Option (Word W) :=
  if h : base≤a ∧ a<base+n then some ((data ⟨a-base,by omega⟩):Word W) else none

theorem romAt_hit {W : ℕ} (base n : ℕ) (data : Fin n→ℕ) (i : Fin n) :
    romAt (W:=W) base n data (base+i.val)=some ((data i):Word W) := by
  simp [romAt,i.isLt]

theorem romAt_away {W : ℕ} {base n a : ℕ} (data : Fin n→ℕ) (disjoint : a<base ∨ base+n≤a) :
    romAt (W:=W) base n data a=none := by
  simp [romAt,show ¬(base≤a∧a<base+n) by omega]

private theorem allNone {α : Type*} (xs : List (Option α)) (none : ∀x∈xs,x=Option.none) :
    xs.findSome? id=Option.none := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    have h:=none x (List.mem_cons_self ..)
    rw [List.findSome?_cons,h]
    exact ih (fun y hy=>none y (List.mem_cons_of_mem _ hy))

private theorem emptyFn {α : Type*} {n : ℕ} (f : Fin n→Option α) (none : ∀i,f i=Option.none) :
    (List.ofFn f).findSome? id=Option.none := by
  apply allNone
  intro x hx
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hx
  exact none i

def Shape.word {W : ℕ} (p : Shape) (sites base a : ℕ) : Option (Word W) :=
  (List.ofFn fun i : Fin 3=>romAt (base+i.val*p.count) p.count
    (SiteScatter.directory p.candidates p.parties p.columns i) a).findSome? id <|>
      romAt (base+3*p.count) sites (fun i=>i.val*p.columns) a

theorem Shape.word_away {W : ℕ} (p : Shape) (sites base a : ℕ) (bounds : a<base ∨ base+p.advice sites≤a) :
    p.word (W:=W) sites base a=none := by
  have rest : a<base+3*p.count ∨ base+3*p.count+sites≤a := by
    rcases bounds with before|after
    · left;omega
    · right;simpa [Shape.advice,Nat.add_assoc] using after
  have fields (i : Fin 3) : a<base+i.val*p.count ∨ base+i.val*p.count+p.count≤a := by
    rcases bounds with before|after
    · left;omega
    · right
      have h : (i.val+1)*p.count≤3*p.count := Nat.mul_le_mul_right _ i.isLt
      rw [Nat.add_mul,one_mul] at h
      simp only [Shape.advice] at after
      omega
  have blank (i : Fin 3) : romAt (W:=W) (base+i.val*p.count) p.count
      (SiteScatter.directory p.candidates p.parties p.columns i) a=none := romAt_away _ (fields i)
  simp only [Shape.word,emptyFn _ blank,romAt_away _ rest]; rfl

variable {T : ℕ} (p : Dated T)

def Dated.words {W : ℕ} (rom : ℕ) (siteTable : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (m : Memory W) (a : ℕ) : Word W :=
 ((romAt rom p.sites (fun i=>i.val*p.roleCount) a) <|>
  (romAt (p.siteROM rom) p.siteDirectorySize siteTable a) <|>
  (List.ofFn fun j : Fin T=>(p.ballot j).word p.sites (p.ballotROM rom j) a).findSome? id <|>
  (List.ofFn fun j : Fin T=>(p.control j).word p.sites (p.controlROM rom j) a).findSome? id <|>
  romAt (p.maskROM rom) p.rawEdges (fun i=>(transport i).toNat) a).getD (m a)

theorem extent {T : ℕ} (base : ℕ) (sizes : Fin T→ℕ) (j : Fin T) :
    offset base sizes j+sizes j≤endOf base sizes := by
  have le : sizes j≤ stride sizes := Finset.single_le_sum (fun i _=>Nat.zero_le (sizes i)) (Finset.mem_univ j)
  have last:=Nat.mul_le_mul_right (stride sizes) j.isLt
  rw [Nat.succ_mul] at last
  dsimp [offset,endOf]
  omega

theorem Dated.words_frame {W : ℕ} (rom : ℕ) (siteTable : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (m : Memory W) (a : ℕ) (outside : a<rom ∨ p.romEnd rom≤a) :
    p.words rom siteTable transport m a=m a := by
  have old : rom≤p.siteROM rom := Nat.le_add_right ..
  have fixed : p.siteROM rom≤p.firstROM rom := Nat.le_add_right ..
  have main : p.firstROM rom≤p.controlROMStart rom := Nat.le_add_right ..
  have cut : p.controlROMStart rom≤p.maskROM rom := Nat.le_add_right ..
  have last : p.maskROM rom+p.rawEdges≤p.romEnd rom := le_rfl
  have b (j : Fin T) := extent (p.firstROM rom) (fun t : Fin T=>(p.ballot t).advice p.sites) j
  have c (j : Fin T) := extent (p.controlROMStart rom) (fun t : Fin T=>(p.control t).advice p.sites) j
  have bs (j : Fin T) : (p.ballot j).word (W:=W) p.sites (p.ballotROM rom j) a=none := by
    apply Shape.word_away
    have start : p.firstROM rom≤p.ballotROM rom j := Nat.le_add_right ..
    have hj : p.ballotROM rom j+(p.ballot j).advice p.sites≤p.controlROMStart rom := b j
    rcases outside with o|o
    · left;omega
    · right;exact hj.trans (by omega)
  have cs (j : Fin T) : (p.control j).word (W:=W) p.sites (p.controlROM rom j) a=none := by
    apply Shape.word_away
    have start : p.controlROMStart rom≤p.controlROM rom j := Nat.le_add_right ..
    have hj : p.controlROM rom j+(p.control j).advice p.sites≤p.maskROM rom := c j
    rcases outside with o|o <;> omega
  have r0 : a<rom ∨ rom+p.sites≤a := by change a<rom ∨ p.siteROM rom≤a;omega
  have r1 : a<p.siteROM rom ∨ p.siteROM rom+p.siteDirectorySize≤a := by
    change a<p.siteROM rom ∨ p.firstROM rom≤a;omega
  have r2 : a<p.maskROM rom ∨ p.maskROM rom+p.rawEdges≤a := by omega
  simp [Dated.words,romAt_away _ r0,romAt_away _ r1,emptyFn _ bs,emptyFn _ cs,romAt_away _ r2]

theorem Dated.words_before {W : ℕ} (rom : ℕ) (siteTable : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (m : Memory W) (a : ℕ) (before : a<rom) :
    p.words rom siteTable transport m a=m a := p.words_frame rom siteTable transport m a (Or.inl before)

theorem Dated.words_end {W : ℕ} (rom : ℕ) (siteTable : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (m : Memory W) (a : ℕ) (after : p.romEnd rom≤a) :
    p.words rom siteTable transport m a=m a := p.words_frame rom siteTable transport m a (Or.inr after)

theorem Dated.words_congr {W : ℕ} (rom : ℕ) (siteTable : Fin p.siteDirectorySize→ℕ)
    (transport : Fin p.rawEdges→Bool) (m m' : Memory W) (a : ℕ) (same : m a=m' a) :
    p.words rom siteTable transport m a=p.words rom siteTable transport m' a := by simp only [Dated.words,same]

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
