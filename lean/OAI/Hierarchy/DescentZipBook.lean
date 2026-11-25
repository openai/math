import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # One literal CPU table for a finite family of packed binary gates -/
namespace Hierarchy.DescentPackedZip.Book
open DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Gate where
  left : ℕ
  right : ℕ
  output : ℕ
  eval : Cell left→Cell right→Cell output

variable {n w out : ℕ} (f : Fin n→Gate) (unit M : ℕ)
abbrev Index (n page : ℕ) := Fin n×(Fin 2×Fin page)
def ordinal (n page : ℕ) : Index n page≃Fin (n*(2*page)) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def address (base page : ℕ) (i tag : ℕ) := base+(i*2+tag)*page

local notation "page" => 2^(unit*M)

def tables (base : ℕ) (i : Fin n) : Tables :=
  ⟨⟨address base page i.val 0,(f i).left*M⟩,⟨address base page i.val 1,((f i).left+(f i).right)*M⟩⟩

def value (ix : Index n page) : ℕ :=
  let g:=f ix.1
  if ix.2.1.val=0 then 2^(g.right*M)*ix.2.2.val
  else (table g.eval (⟨ix.2.2.val%2^((g.left+g.right)*M),Nat.mod_lt _ (Nat.two_pow_pos _)⟩:Cell ((g.left+g.right)*M))).val

def data (j : ℕ) : ℕ :=
  if h:j<n*(2*page) then value f unit M ((ordinal n page).symm ⟨j,h⟩) else 0

def install (w base : ℕ) := DescentStaticWordColumn.program w base (data f unit M) (n*(2*page))
def image (base : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (data f unit M) m (n*(2*page))

theorem atOrdinal (base : ℕ) (ix : Index n page) :
    address base page ix.1.val ix.2.1.val+ix.2.2.val=base+((ordinal n page) ix).val := by
  simp [ordinal,address,finProdFinEquiv_apply_val]; ring

theorem at_cell (base : ℕ) (m : Memory w) (ix : Index n page) :
    image f unit M base m (address base page ix.1.val ix.2.1.val+ix.2.2.val)=(value f unit M ix:Word w) := by
  rw [atOrdinal]
  have cell:=DescentStaticWordColumn.read base (n*(2*page)) (data f unit M) m ((ordinal n page) ix).isLt
  simpa only [image,data,dite_eq_left ((ordinal n page) ix).isLt,Fin.eta,Equiv.symm_apply_apply] using cell

theorem mount (base : ℕ) (m : Memory w) (caps : ∀i,(f i).left+(f i).right≤unit)
    (fit : base+n*(2*page)<2^w) :
    (install f unit M w base).Exec m (image f unit M base m) (4+10*(n*(2*page))) ∧
    (∀i,Static (tables f unit M base i) (f i).eval M (image f unit M base m)) ∧
    (∀x,x<base ∨ base+n*(2*page)≤x→image f unit M base m x=m x) ∧ CheapCode (install f unit M w base) := by
  have admissible : CheapCode (install f unit M w base) := by
    intro P R K pc reg pub exit i
    exact DescentStaticWordColumn.cheap w base (data f unit M) (n*(2*page)) pc reg pub exit i
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ fit,?_,DescentStaticWordColumn.frame _ _ _ _,@admissible⟩
  intro i
  have total : 2^(((f i).left+(f i).right)*M)≤page:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right M (caps i))
  have first : 2^((f i).left*M)≤page:=Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right M ((Nat.le_add_right ..).trans (caps i)))
  constructor
  · intro j
    let ix : Index n page:=⟨i,(0:Fin 2),j.castLE first⟩
    simpa only [ix,tables,value,Fin.val_zero,ite_true,Fin.val_castLE] using at_cell f unit M base m ix
  · intro j
    let ix : Index n page:=⟨i,(1:Fin 2),j.castLE total⟩
    have same : (⟨j.val%2^(((f i).left+(f i).right)*M),Nat.mod_lt _ (Nat.two_pow_pos _)⟩ :
        Cell (((f i).left+(f i).right)*M))=j:=Fin.ext (Nat.mod_eq_of_lt j.isLt)
    simpa only [ix,tables,value,Fin.val_one,Fin.val_castLE,one_ne_zero,ite_false,same] using
      at_cell f unit M base m ix

/-- Once printed, later publishers need only preserve the one literal interval. -/
theorem retained (base : ℕ) (m old : Memory w) (caps : ∀i,(f i).left+(f i).right≤unit)
    (values : ∀i,Static (tables f unit M base i) (f i).eval M old)
    (saved : ∀x,base≤x→x<base+n*(2*page)→m x=old x) :
    ∀i,Static (tables f unit M base i) (f i).eval M m := by
  intro i
  have size (tag : Fin 2) (j : Fin page) :
      address base page i.val tag.val+j.val<base+n*(2*page) := by
    rw [atOrdinal (ix:=(i,tag,j))]
    exact Nat.add_lt_add_left ((ordinal n page) (i,tag,j)).isLt _
  have cut:=Nat.pow_le_pow_right (n:=2) (by decide) (Nat.mul_le_mul_right M (caps i))
  have first : 2^((f i).left*M)≤page:=Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right M ((Nat.le_add_right ..).trans (caps i)))
  constructor
  · intro j
    exact (saved _ (by dsimp [tables,address];omega) (size (0:Fin 2) (j.castLE first))).trans ((values i).1 j)
  · intro j
    exact (saved _ (by dsimp [tables,address];omega) (size (1:Fin 2) (j.castLE cut))).trans ((values i).2 j)

theorem geometry (base : ℕ) (i : Fin n) (before : base+n*(2*page)≤out) (fit : out<2^w)
    (hi : (f i).left+(f i).right≤unit) :
    (tables f unit M base i).shift.Fits w out ∧ (tables f unit M base i).apply.Fits w out := by
  have cap : 2^(((f i).left+(f i).right)*M)≤page:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right M hi)
  have capL : 2^((f i).left*M)≤page:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right M ((Nat.le_add_right ..).trans hi))
  have span : ((i.val+1)*2)*page≤n*(2*page):=by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (2*page) i.isLt
  have stop:= (Nat.add_le_add_left span base).trans before
  rw [Nat.succ_mul,Nat.add_mul,Nat.two_mul page] at stop
  have pos:0<page:=Nat.two_pow_pos _
  have one:base+(i.val*2)*page+2^((f i).left*M)≤out:=by omega
  have two:base+((i.val*2)*page+page)+2^(((f i).left+(f i).right)*M)≤out:=by omega
  constructor
  · refine ⟨Nat.two_pow_pos _,?_,?_⟩
    · change 2^((f i).left*M)<2^w;omega
    · simpa only [tables,address,Bank.size,Nat.add_zero] using one
  · refine ⟨Nat.two_pow_pos _,?_,?_⟩
    · change 2^(((f i).left+(f i).right)*M)<2^w;omega
    · simpa only [tables,address,Bank.size,Nat.succ_mul] using two


theorem names (w base : ℕ) : DescentStaticWordColumn.names (install f unit M w base)=15*(n*(2*page)+1) :=
  DescentStaticWordColumn.names_mount ..

end
end Hierarchy.DescentPackedZip.Book

end OAI
