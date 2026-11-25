import OAI.Hierarchy.DescentHaloRankRAM
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Roots, four bounded path digits, rank row starts, and the final live-lane mask -/
namespace Hierarchy.DescentRawCablePanel.RootTables
open DescentSIMDLookup DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (H G M D : ℕ) {w : ℕ}
local notation "P" => breadth D
local notation "q" => H*P
local notation "n" => H*chunks G M
def length := 6*q+n
abbrev Key := (Fin 6×Fin q)⊕Fin n
def order : Key H G M D ≃ Fin (length H G M D) :=
  (finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv
def addr (base : ℕ) : Key H G M D→ℕ
  | .inl (lane,pos) => base+lane.val*q+pos.val
  | .inr j => base+6*q+j.val
def data : Key H G M D→ℕ
  | .inl (lane,pos) =>
    let vp : Fin H×Fin P := finProdFinEquiv.symm pos
    if lane.val=0 then vp.1.val else
    if d : lane.val-1<4 then ((path vp.2) ⟨lane.val-1,d⟩).val else vp.1.val*P
  | .inr j => (DescentSIMDLookup.data (fun (_:Fin H) (_:Fin G)=>(1:Cell 1)) ((DescentSIMDLookup.row H G M).symm j)).val
def literal (x : ℕ) :=
  if hx:x<length H G M D then data H G M D ((order H G M D).symm ⟨x,hx⟩) else 0
def image (base : ℕ) (m : Memory w) := DescentStaticWordColumn.image base (literal H G M D) m (length H G M D)
def program (w base : ℕ) := DescentStaticWordColumn.program w base (literal H G M D) (length H G M D)
def bank (base lane : ℕ) : Bank := ⟨base+lane*q,Nat.clog 2 q⟩
def liveBank (base : ℕ) : Bank := ⟨base+6*q,Nat.clog 2 n⟩
def walks (base : ℕ) (neighbors : Bank) : DescentHaloWalkRAM.Banks :=
  ⟨neighbors,bank H D base 0,fun i=>bank H D base (i.val+1)⟩
def ranks (base : ℕ) (endpoints : Bank) : Ranks.Columns := ⟨endpoints,bank H D base 5⟩
structure Present (base : ℕ) (m : Memory w) : Prop where
  read : ∀j,m (addr H G M D base j)=(data H G M D j:Word w)

theorem mount (base : ℕ) (m : Memory w) (limit : base+length H G M D<2^w) :
    let result:=image H G M D base m
    (program H G M D w base).Exec m result (4+10*length H G M D) ∧ Present H G M D base result ∧
      (∀x,x<base ∨ base+length H G M D≤x → result x=m x) ∧ CheapCode (program H G M D w base) := by
  intro result
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ limit,⟨?_⟩,DescentStaticWordColumn.frame _ _ _ _,@DescentStaticWordColumn.cheap _ _ _ _⟩
  intro j
  have ix : addr H G M D base j=base+(order H G M D j).val:=by
    rcases j with ⟨i,x⟩|j
    · change base+i.val*q+x.val=base+(x.val+q*i.val)
      ring
    · change base+6*q+j.val=base+(6*q+j.val)
      omega
  rw [ix]
  have v:=DescentStaticWordColumn.read base (length H G M D) (literal H G M D) m
    (j:=(order H G M D j).val) (order H G M D j).isLt
  simpa only [result,image,literal,dite_eq_left (order H G M D j).isLt,Fin.eta,Equiv.symm_apply_apply] using v

theorem row_data (base : ℕ) (rs : Fin H→Fin D→Option (Fin H)) (adj : Bank) (m : Memory w)
    (fixed : Present H G M D base m) (near : ∀(h : Fin H) (j : Fin D),m (adj.base+(h.val*D+j.val))=(number (rs h j):Word w)) :
    DescentHaloWalkRAM.Reads (walks H D base adj) rs m ∧
    (∀(h:Fin H)(p:Fin P),m ((bank H D base 5).base+(Ranks.id h p).val)=((h.val*P:ℕ):Word w)) ∧
    (∀j : DescentSIMDLookup.Row H G M,m ((liveBank H G M D base).base+(DescentSIMDLookup.row H G M j).val)=
      ((DescentSIMDLookup.data (fun (_:Fin H) (_:Fin G)=>(1:Cell 1)) j).val:Word w)) := by
  refine ⟨⟨fun h j=>by simpa [walks,Nat.add_assoc] using near h j,?_,?_⟩,?_,?_⟩
  · intro h p
    simpa [walks,bank,addr,data,DescentHaloWalkRAM.row] using fixed.read (.inl (0,finProdFinEquiv (h,p)))
  · intro h p j
    have idx: j.val+1<6:=by have:=j.isLt;omega
    have nz : j.val+1≠0:=by omega
    simpa [walks,bank,addr,data,DescentHaloWalkRAM.row,nz,j.isLt] using
      fixed.read (.inl (⟨j.val+1,idx⟩,finProdFinEquiv (h,p)))
  · intro h p
    simpa [bank,addr,data,Ranks.id] using fixed.read (.inl (5,finProdFinEquiv (h,p)))
  · intro j
    simpa [liveBank,addr,data] using fixed.read (.inr (DescentSIMDLookup.row H G M j))

theorem keep {base : ℕ} {m new : Memory w} (fixed : Present H G M D base m)
    (early : ∀x,x<base+length H G M D→new x=m x) : Present H G M D base new := by
  refine ⟨fun i=>(early _ ?_).trans (fixed.read i)⟩
  rcases i with ⟨lane,pos⟩|j
  · change base+lane.val*q+pos.val<base+(6*q+n)
    have b:=Nat.mul_le_mul_right q (show lane.val+1≤6 from lane.isLt)
    have len:=pos.isLt
    rw [Nat.succ_mul] at b
    omega
  · exact Nat.add_lt_add_left j.isLt _ |>.trans_le (by simp [length,Nat.add_assoc])

end
end Hierarchy.DescentRawCablePanel.RootTables

end OAI
