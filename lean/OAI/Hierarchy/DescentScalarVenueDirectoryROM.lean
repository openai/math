import OAI.Hierarchy.DescentScalarVenueDirectory
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # The literal host, path, and offset pages for the scalar venue return test -/
namespace Hierarchy.DescentScalarVenueDirectory.ROM
open DescentSIMDLookup ProtocolRAM DescentStaticWordColumn Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H P : ℕ}

def width (H P : ℕ):=Nat.clog 2 (max H (H*P)+1)
def page (H P : ℕ):=2^width H P
def size (H P : ℕ):=3*page H P

def chart (sorted ends : Bank) (base H P : ℕ) : Chart:=⟨sorted,ends,⟨base,width H P⟩,⟨base+page H P,width H P⟩,⟨base+2*page H P,width H P⟩⟩

def shape (H P j : ℕ):=if j<page H P then j/P else if j<2*page H P then (j-page H P)%P else (j-2*page H P)*P

private theorem limits (H P : ℕ):H≤page H P ∧ H*P≤page H P:=by
  have lim:(max H (H*P)+1)≤page H P:=Nat.le_pow_clog (by decide) _
  have bound : max H (H*P) ≤ page H P := (Nat.le_succ _).trans lim
  exact ⟨(le_max_left H (H*P)).trans bound, (le_max_right H (H*P)).trans bound⟩

private theorem splitRow (h:Fin H) (p:Fin P) : (finProdFinEquiv (h,p)).val/P=h.val ∧ (finProdFinEquiv (h,p)).val%P=p.val:=by
  simp only [finProdFinEquiv_apply_val]
  constructor
  · rw [Nat.add_mul_div_left _ _ p.pos, Nat.div_eq_of_lt p.isLt, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.isLt]

/-- The two geometry-dependent arrays are the actual sorted donor roster
and the earlier four-hop terminal table. All remaining cells are public. -/
theorem mount (sorted ends : Bank) (base : ℕ) (m : Memory w) (walks : Fin H→Fin P→Option (Fin H))
    (sortedFit : sorted.Fits w base) (endFit : ends.Fits w base) (sortedSize : H*P≤ sorted.size) (endSize : H*P≤ends.size)
    (sortedRead : ∀h s,m (sorted.base+(h.val*P+s.val))=(number (DescentSortedRoster.indexed walks h s):Word w))
    (terminalRead : ∀h p,m (ends.base+(h.val*P+p.val))=(number (walks h p):Word w))
    (hi : base+size H P+P*(H*P)<2^w) :
    let out:=base+size H P;let C:=chart sorted ends base H P;let mid:=image base (shape H P) m (size H P)
    (DescentStaticWordColumn.program w base (shape H P) (size H P)).Exec m mid (4+10*size H P) ∧
      Room C out H P w ∧ Read C walks mid ∧ (∀a,a<base ∨ out≤a→mid a=m a) ∧ CheapCode (DescentStaticWordColumn.program w base (shape H P) (size H P)):=by
  intro out C mid
  have cap:=limits H P;have space:out<2^w:=(Nat.le_add_right ..).trans_lt hi
  have pos:0<page H P:=Nat.two_pow_pos _;have below:base≤out:=Nat.le_add_right ..
  have far:=DescentStaticWordColumn.frame base (size H P) (shape H P) m
  have fit {B:Bank} (fits:B.Fits w base):B.Fits w out:=⟨fits.1,fits.2.1,fits.2.2.trans below⟩
  have three (i : Fin 3) : (⟨base+i.val*page H P,width H P⟩:Bank).Fits w out:=by
    have total : base + 3*page H P < 2^w := space
    have span : page H P < 2^w := by omega
    refine ⟨pos, span, ?_⟩
    change base + i.val*page H P + page H P ≤ base + 3*page H P
    rw [Nat.add_assoc, ←Nat.succ_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _
  have idx (h:Fin H) (p:Fin P):h.val*P+p.val<H*P:=(Nat.add_lt_add_left p.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ h.isLt)
  refine ⟨DescentStaticWordColumn.mount base _ _ m space,⟨fit sortedFit,fit endFit,?_,?_,?_,sortedSize,endSize,cap.2,cap.2,cap.1,?_,hi⟩,⟨?_,?_,?_,?_,?_⟩,far,@DescentStaticWordColumn.cheap _ _ _ _⟩
  · simpa [C,chart] using three 0
  · simpa [C,chart] using three 1
  · simpa [C,chart] using three 2
  · exact cap.1.trans_lt (by dsimp [out,size] at space;omega)
  · intro h s;exact (far _ (.inl ((Nat.add_lt_add_left ((idx h s).trans_le sortedSize) _).trans_le sortedFit.2.2))).trans (sortedRead h s)
  · intro h p;exact (far _ (.inl ((Nat.add_lt_add_left ((idx h p).trans_le endSize) _).trans_le endFit.2.2))).trans (terminalRead h p)
  · intro h p;let j:=finProdFinEquiv (h,p);have jlt:j.val<page H P:=j.isLt.trans_le cap.2
    have read:=DescentStaticWordColumn.read base (size H P) (shape H P) m (show j.val<size H P by dsimp [size];omega)
    have entry : shape H P j.val = h.val := by
      rw [shape, ite_eq_left jlt]
      exact (splitRow h p).1
    change DescentStaticWordColumn.image base (shape H P) m (size H P) (base+j.val) = _
    exact read.trans (congrArg (fun n : ℕ => (n : Word w)) entry)
  · intro h p;let j:=finProdFinEquiv (h,p);have jlt:j.val<page H P:=j.isLt.trans_le cap.2
    have read:=DescentStaticWordColumn.read base (size H P) (shape H P) m (show page H P+j.val<size H P by dsimp [size];omega)
    have entry : shape H P (page H P+j.val) = p.val := by
      rw [shape, ite_eq_right (by omega : ¬page H P+j.val<page H P),
        ite_eq_left (by omega : page H P+j.val<2*page H P), Nat.add_sub_cancel_left]
      exact (splitRow h p).2
    change DescentStaticWordColumn.image base (shape H P) m (size H P) (base+page H P+j.val) = _
    rw [Nat.add_assoc]
    exact read.trans (congrArg (fun n : ℕ => (n : Word w)) entry)
  · intro h;have jlt:=h.isLt.trans_le cap.1
    have read:=DescentStaticWordColumn.read base (size H P) (shape H P) m (show 2*page H P+h.val<size H P by dsimp [size];omega)
    simpa only [C,chart,Nat.add_assoc,shape,ite_eq_right (show ¬2*page H P+h.val<page H P by omega),ite_eq_right (show ¬2*page H P+h.val<2*page H P by omega),Nat.add_sub_cancel_left] using read

end
end Hierarchy.DescentScalarVenueDirectory.ROM

end OAI
