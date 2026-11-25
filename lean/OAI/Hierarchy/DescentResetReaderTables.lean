import OAI.Hierarchy.DescentResetStencilSlots
import OAI.Hierarchy.DescentResetStencilTables
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Physical literal columns for every finite reset stencil reader -/
namespace Hierarchy.DescentPlainTerminal.Suffix.Stencil.ReaderTables
open DescentGL DescentColonies DescentPackedColony DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel
open DescentPacking.PackedMatch.Local DescentPackedColony.Phase
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

abbrev Key (r : ℕ) := Unit ⊕ ((Block r ⊕ (Fin r × Block r)) ⊕ (Block r × Block r))

def wordBits (r m n b M : ℕ) : Key r→ℕ
  | .inl _=>n
  | .inr (.inl (.inl _))=>(b*2^r)*M
  | .inr (.inl (.inr _))=>(1+r*2^r)*M
  | .inr (.inr _)=>PackedOrder.bits r m*M

def entry (r m n b M : ℕ) (j : Key r) : Cell (wordBits r m n b M j)→ℕ :=
  match j with
  | .inl _=>fun z=>(encode n M (fun _=>z)).val
  | .inr (.inl (.inl x))=>fun z=>(DescentSIMDLookup.table (M:=M) (Readers.amount (n:=n) (b:=b) x) z).val
  | .inr (.inl (.inr (d,x)))=>fun z=>(DescentSIMDLookup.table (M:=M) (Readers.vote (n:=n) d x) z).val
  | .inr (.inr (i,x))=>fun z=>(DescentSIMDLookup.table (M:=M) (PackedOrder.cmp (n:=n) (m:=m) i x) z).val

def largest (r m n b M : ℕ) := max n (max (b*2^r*M) (max ((1+r*2^r)*M) (PackedOrder.bits r m*M)))

theorem key_le (r m n b M : ℕ) (j : Key r) : wordBits r m n b M j≤largest r m n b M := by
  rcases j with _|((_|_)|_) <;> simp only [wordBits,largest] <;> omega

structure Chart where
  origin : ℕ
  H : ℕ
  c : ℕ
  m : ℕ
  n : ℕ
  b : ℕ
  M : ℕ

namespace Chart
variable (C : Chart)

def r := C.m-C.c

def rows := C.H*chunks (2^C.c) C.M
def mask : Bank := ⟨C.origin,Nat.clog 2 C.rows⟩
def first := C.origin+C.mask.size
def page := 2^(largest C.r C.m C.n C.b C.M)
def idx := Fintype.equivFin (Key C.r)
def column (j : Key C.r) : Bank := ⟨C.first+(C.idx j).val*C.page,wordBits C.r C.m C.n C.b C.M j⟩
def planeBase := C.first+Fintype.card (Key C.r)*C.page
def stop := StencilTables.start C.planeBase (2^C.r) C.m C.M (C.m+1)

def image : Arena.Image w :=
  ⟨C.origin,C.planeBase,fun z=>
    if t:z-C.origin<C.rows then
      let p:Row C.H (2^C.c) C.M:=(DescentSIMDLookup.row C.H (2^C.c) C.M).symm ⟨z-C.origin,t⟩
      (maskWord C.n C.M (2^C.c) p.2.val:Word w)
    else
      let q:=(z-C.first)/C.page
      let t:=(z-C.first)%C.page
      if h:q<Fintype.card (Key C.r) then
        let j:=C.idx.symm ⟨q,h⟩
        if h':t<2^(wordBits C.r C.m C.n C.b C.M j) then entry C.r C.m C.n C.b C.M j ⟨t,h'⟩ else 0
      else 0⟩

theorem mask_card : C.rows≤C.mask.size := Nat.le_pow_clog (by decide) _

theorem page_card (j : Key C.r) : (C.column j).size≤C.page :=
  Nat.pow_le_pow_right (by decide) (key_le _ _ _ _ _ j)

theorem column_end (j : Key C.r) : (C.column j).base+(C.column j).size≤C.planeBase := by
  have top:=Nat.mul_le_mul_right C.page (C.idx j).isLt
  have sub:=C.page_card j
  simp only [Nat.succ_mul] at top
  change C.first+(C.idx j).val*C.page+_≤C.first+_
  omega

theorem plane_le : C.planeBase≤C.stop:=Nat.le_add_right ..

theorem mask_read (mem : Memory w) (pub : C.image.Resident mem) (p : Row C.H (2^C.c) C.M) :
    mem (C.mask.base+(DescentSIMDLookup.row C.H (2^C.c) C.M p).val)=(maskWord C.n C.M (2^C.c) p.2.val:Word w) := by
  let t:=DescentSIMDLookup.row C.H (2^C.c) C.M p
  have h:t.val<C.rows:=t.isLt
  have h₁:=C.mask_card
  have rd:=pub (C.origin+t.val) (Nat.le_add_right ..) (by change C.origin+t.val<C.first+_;dsimp [first];omega)
  simpa only [mask,image,Nat.add_sub_cancel_left,dite_eq_left h,Fin.eta,t,Equiv.symm_apply_apply] using rd

theorem cell_read (j : Key C.r) (mem : Memory w) (pub : C.image.Resident mem)
    (z : Cell (wordBits C.r C.m C.n C.b C.M j)) :
    mem ((C.column j).base+z.val)=(entry C.r C.m C.n C.b C.M j z:Word w) := by
  let base:=(C.column j).base
  let i:=C.idx j
  have bound:z.val<(C.column j).size:=z.isLt
  have lt:z.val<C.page:=bound.trans_le (C.page_card j)
  have pos:0<C.page:=Nat.two_pow_pos _
  have delta : base+z.val-C.first=C.page*i.val+z.val:=by
    dsimp [base,column,i]
    rw [Nat.mul_comm (C.idx j).val]
    omega
  have large:¬base+z.val-C.origin<C.rows := by
    have rows:=C.mask_card
    dsimp [base,column,first]
    omega
  have lower : C.origin ≤ base+z.val := by
    change C.origin ≤ (C.origin+C.mask.size+(C.idx j).val*C.page)+z.val
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have word := pub (base+z.val) lower
    ((Nat.add_lt_add_left bound (C.column j).base).trans_le (C.column_end j))
  have readKey (key : Key C.r) (rem : ℕ) (hk : key=j) (hr : rem=z.val) :
      (if h' : rem<2^(wordBits C.r C.m C.n C.b C.M key) then
          (entry C.r C.m C.n C.b C.M key ⟨rem,h'⟩ : Word w) else 0) =
        (entry C.r C.m C.n C.b C.M j z : Word w) := by
    subst key rem
    rw [dite_eq_left z.isLt]
  have decode (quot rem : ℕ) (hq : quot=i.val) (hr : rem=z.val) :
      (if h : quot<Fintype.card (Key C.r) then
        let key := C.idx.symm ⟨quot,h⟩
        if h' : rem<2^(wordBits C.r C.m C.n C.b C.M key) then
          (entry C.r C.m C.n C.b C.M key ⟨rem,h'⟩ : Word w) else 0
      else 0) = (entry C.r C.m C.n C.b C.M j z : Word w) := by
    subst quot rem
    rw [dite_eq_left i.isLt]
    exact readKey _ _ (C.idx.symm_apply_apply j) rfl
  apply word.trans
  dsimp only [image]
  rw [dite_eq_right large]
  apply decode
  · rw [delta,Nat.mul_add_div pos,Nat.div_eq_of_lt lt,Nat.add_zero]
  · rw [delta,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt lt]

theorem cost (h : ℕ) (small : largest C.r C.m C.n C.b C.M≤h/2) (planes : (2^C.r*C.m+2^C.r)*C.M≤h/2) :
    C.stop-C.origin≤C.mask.size+(Fintype.card (Key C.r)+C.m+1)*2^(h/2) := by
  have lookup:=Nat.mul_le_mul_left (Fintype.card (Key C.r)) (Nat.pow_le_pow_right (by decide : 0<2) small)
  have ins:=StencilTables.footprint C.planeBase (2^C.r) C.m C.M h planes
  have prior:=C.plane_le
  change C.stop-C.planeBase≤_ at ins
  change Fintype.card (Key C.r)*C.page≤Fintype.card (Key C.r)*2^(h/2) at lookup
  dsimp only [planeBase,first] at ins prior
  simp only [Nat.add_mul,Nat.one_mul] at *
  omega

end Chart
end
end Hierarchy.DescentPlainTerminal.Suffix.Stencil.ReaderTables

end OAI
