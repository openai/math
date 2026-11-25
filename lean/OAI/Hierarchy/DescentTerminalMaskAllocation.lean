import OAI.Hierarchy.DescentTerminalMaskedRAM
import OAI.Hierarchy.DescentTerminalHomeAllocation
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Literal terminal decoder next to the reached nine-channel physical row -/
namespace Hierarchy.DescentTerminalVertexFields.MaskAllocation
open DescentTerminalSiteShelves DescentTerminalRecipeRows ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {q t H N A p groups blocks V B bw : ℕ}
local notation "F" => Fin (channels blocks)
local notation "size" => channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "cap" => cohortSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
local notation "width" => span q t H N A p
local notation "P" => ∑f:F,2^(size f)
local notation "full" => P+cap
local notation "D" => (f:F)×Fin (2^(size f))
local notation "keys" => D⊕Fin cap
local notation "channelWeight" => weightAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups)

structure Channels (blocks : ℕ) where
  occupied : Fin blocks→Bank
  primitive : Fin blocks→Fin 8→Bank

def Channels.bank (R : Channels blocks) (j : F) : Bank :=
  let f:=finProdFinEquiv.symm j
  Fin.cases (R.occupied f.1) (R.primitive f.1) f.2

@[simp] theorem Channels.occupied_at (R : Channels blocks) (b : Fin blocks) :
    R.bank (finProdFinEquiv (b,(0:Fin 9)))=R.occupied b := by simp [Channels.bank]

@[simp] theorem Channels.primitive_at (R : Channels blocks) (b : Fin blocks) (f : Fin 8) :
    R.bank (finProdFinEquiv (b,f.succ))=R.primitive b f := by simp [Channels.bank]

def pageStart {n : ℕ} («size» : Fin n→ℕ) (f : Fin n) := ∑j:Fin f.val,2^(«size» (Fin.castLE f.isLt.le j))
def marks {n : ℕ} («size» : Fin n→ℕ) := ∑j:Fin n,2^(«size» j)

def shelf (R : Channels blocks) (base : ℕ) : MaskedShelf blocks where
  channel := R.bank
  weight f := ⟨base+pageStart size f,size f⟩
  table := ⟨base+marks size,∑f:F,size f⟩

def counter (R : Channels blocks) (base : ℕ) : PrivateCounter.Banks (blocks:=blocks) :=
  ⟨shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) R base,base+full⟩

def ordinal : keys≃Fin full := (finSigmaFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv

def cell (fit : V*width≤B) : keys→ℕ
  | .inl ⟨f,j⟩=>j.val*channelWeight f
  | .inr j=>(dictionary fit j).val

def literal (fit : V*width≤B) (j : ℕ) :=
  if h:j<full then cell (groups:=groups) (blocks:=blocks) fit (ordinal.symm ⟨j,h⟩) else 0
local notation "literal₀" => literal (groups:=groups) (blocks:=blocks)

def program (fit : V*width≤B) (bw base : ℕ) := DescentStaticWordColumn.program bw base (literal₀ fit) full
def image (fit : V*width≤B) (base : ℕ) (m : Memory bw) := DescentStaticWordColumn.image base (literal₀ fit) m full
local notation "menu" => shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
local notation "issued" => image (groups:=groups) (blocks:=blocks)
local notation "install" => program (groups:=groups) (blocks:=blocks)

private theorem index_left (x : D) : (ordinal (.inl x : keys)).val=pageStart size x.1+x.2.val := by
  simp [ordinal,pageStart,finSigmaFinEquiv_apply]
private theorem index_right (j : Fin cap) : (ordinal (.inr j : keys)).val=P+j.val := by
  simp [ordinal]

theorem install_at (R : Channels blocks) (base : ℕ) (fit : V*width≤B) (m : Memory bw)
    (room : base+full<2^bw) :
    (install fit bw base).Exec m (issued fit base m) (4+10*full) ∧
    MountedMask (groups:=groups) (menu R base) (issued fit base m) fit ∧
    (∀j,j<base ∨ base+full≤j→issued fit base m j=m j) ∧ CheapCode (install fit bw base) := by
  have atKey (j : keys) : issued fit base m (base+(ordinal j).val)=(cell fit j:Word bw) := by
    simpa only [image,literal,dite_eq_left (ordinal j).isLt,Fin.eta,Equiv.symm_apply_apply] using
      DescentStaticWordColumn.read base full (literal₀ fit) m (ordinal j).isLt
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ room,⟨?_,?_⟩,DescentStaticWordColumn.frame _ _ _ _,@DescentStaticWordColumn.cheap _ _ _ _⟩
  · intro f z
    let j:Fin (2^(size f)):=⟨z.val%2^(size f),Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    have row:=atKey (.inl ⟨f,j⟩)
    rw [index_left] at row
    simpa [shelf,Bank.read,Bank.size,j,cell,Nat.add_assoc] using row
  · intro j
    have fits : j.val<2^bw:=j.isLt.trans (by omega)
    have scale : 2^(∑f:F,size f)=cap := by symm;unfold cohortSize;rw [Finset.prod_pow_eq_pow_sum]
    have row:=atKey (.inr j)
    rw [index_right] at row
    simpa [shelf,Bank.read,Bank.size,marks,scale,Fin.val_cast_of_lt fits,Nat.mod_eq_of_lt j.isLt,cell,Nat.add_assoc] using row

theorem names (base : ℕ) (fit : V*width≤B) :
    DescentStaticWordColumn.names (install fit bw base)=15*(full+1) := DescentStaticWordColumn.names_mount ..

private theorem sum_pages {n : ℕ} (d : Fin n→ℕ) :
    (∑i:Fin n,2^(d i))+1≤(∏i:Fin n,2^(d i))+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have tail:=(ih (fun i=>d i.succ))
    rw [Fin.sum_univ_succ,Fin.prod_univ_succ]
    have x:=Nat.two_pow_pos (d 0)
    have y : 0<∏i:Fin n,2^(d i.succ):=Finset.prod_pos (fun i _=>Nat.two_pow_pos _)
    let a := 2^d 0
    let b := ∏i:Fin n,2^(d i.succ)
    have ax : a=(a-1)+1 := (Nat.sub_add_cancel x).symm
    have by₀ : b=(b-1)+1 := (Nat.sub_add_cancel y).symm
    have product : a+b≤a*b+1 := by
      calc
        a+b = ((a-1)+1)+((b-1)+1) := congrArg₂ (·+·) ax by₀
        _ ≤ ((a-1)+1)+((b-1)+1)+(a-1)*(b-1) := Nat.le_add_right ..
        _ = ((a-1)+1)*((b-1)+1)+1 := by ring
        _ = a*b+1 := by rw [←ax,←by₀]
    change a+_+1≤a*b+(n+1)
    omega

theorem bill : full≤2*cap+channels blocks := by
  have compact:=sum_pages size
  change P+1≤cap+channels blocks at compact
  omega

theorem room {homes : ℕ} (R : Channels blocks) (base : ℕ)
    (prior : ∀f,(R.bank f).base+(R.bank f).size≤base)
    (endAt : base+full+cap+homes+homes+3<2^bw) :
    PrivateCounter.Room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
      (counter (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) R base) bw := by
  refine ⟨fun f=>⟨?_,?_⟩,by change base+full+cap<_;omega⟩
  · change (R.bank f).Fits bw (base+full)
    have lim:=prior f
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  · let last:Fin (2^(size f)):=⟨2^(size f)-1,by have:=Nat.two_pow_pos (size f);omega⟩
    have endRow:pageStart size f+2^(size f)≤P := by
      have bound:=(finSigmaFinEquiv (n:=fun k=>2^(size k)) ⟨f,last⟩).isLt
      rw [finSigmaFinEquiv_apply] at bound
      change pageStart size f + (2^(size f)-1) < P at bound
      have := Nat.two_pow_pos (size f)
      omega
    exact ⟨Nat.two_pow_pos _,by change 2^(size f)<_;omega,by change base+pageStart size f+2^(size f)≤base+full;omega⟩

end
end Hierarchy.DescentTerminalVertexFields.MaskAllocation

end OAI
