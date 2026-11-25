import OAI.Hierarchy.DescentGLPackedRoutes
import OAI.Hierarchy.DescentPackedWalshRAM
import OAI.Hierarchy.DescentPackedWalshCube
import OAI.Hierarchy.DescentPackedRegroup

namespace OAI
/-! # Reuse the old packed census words as the physical reset Walsh input -/
namespace Hierarchy.DescentPackedResetSource
open DescentSIMDLookup DescentGL DescentColonies DescentPackedWalsh Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {h l H b w : ℕ}
local notation "Q" => DescentWalshPhysical.coordinates

/-- The incoming register with M consecutive old groups and r inner block
entries already contains M*r consecutive original-coordinate digits. -/
theorem ungroup {J M r : ℕ} (hm : 0<M) (hr : 0<r) (base : ℕ) (mem : Memory w)
    (X : Fin H→Fin (J*r)→Cell b)
    (old : ∀p : Row H J M,mem (base+(DescentSIMDLookup.row H J M p).val)=
      ((data (groupedRows X) p).val:Word w)) (p : Row H (J*r) (M*r)) :
    mem (base+(DescentSIMDLookup.row H (J*r) (M*r) p).val)=((data X p).val:Word w) := by
  have eq:=chunks_group J M r hm hr
  let before : Row H J M:=(p.1,Fin.cast eq p.2)
  have addrEq : (DescentSIMDLookup.row H _ _ p).val=(DescentSIMDLookup.row H J M before).val := by
    change p.2.val+chunks (J*r) (M*r)*p.1.val=p.2.val+chunks J M*p.1.val
    exact congrArg (fun n : ℕ => p.2.val + n * p.1.val) eq
  rw [addrEq,old,data_group hr X before p rfl rfl]

theorem ungroup_cast {J M r n t : ℕ} (size : n=J*r) (lanes : t=M*r)
    (hm : 0<M) (hr : 0<r) (base : ℕ) (mem : Memory w) (X : Fin H→Fin n→Cell b)
    (old : ∀p : Row H J M,mem (base+(DescentSIMDLookup.row H J M p).val)=
      ((data (fun v g=>encode b r (fun j=>X v (Fin.cast size.symm (finProdFinEquiv (g,j))))) p).val:Word w)) :
    ∀p : Row H n t,mem (base+(DescentSIMDLookup.row H n t p).val)=((data X p).val:Word w) := by
  subst n t
  exact ungroup hm hr base mem X old

theorem coordinates_append (p : Cube h) (q : Cube l) :
    (Q (h+l)).symm (addr p q)=Fin.append ((Q h).symm p) ((Q l).symm q) := by
  funext i
  refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.append_left]
    change (if addr p q (finSumFinEquiv (.inl j)) then _ else _)=_
    rw [addr_high];rfl
  · simp only [Fin.append_right]
    change (if addr p q (finSumFinEquiv (.inr j)) then _ else _)=_
    rw [addr_low];rfl

theorem flat_coordinate (p : Cube h) (q : Cube l) :
    (address (h+l) ((Q (h+l)).symm (addr p q))).val=
      (ordinal h p).val*2^l+(ordinal l q).val := by
  rw [coordinates_append,DescentGLPacked.address_append];rfl

private theorem chunkCount (h l : ℕ) : chunks (2^(h+l)) (2^l)=2^h := by
  have eq:=chunks_group (2^h) 1 (2^l) (by decide) (Nat.two_pow_pos _)
  simpa [pow_add,chunks,ThreeFlat.Routing.poolBatchCount] using eq

/-- The very same native address and word, with the Walsh input's actual
coordinate permutation. There are no transport instructions. -/
theorem installed (base : ℕ) (mem : Memory w) (X : Fin H→Block (h+l)→Cell b)
    (old : ∀p : Row H (2^(h+l)) (2^l),mem (base+(DescentSIMDLookup.row H _ _ p).val)=((data X p).val:Word w)) :
    Installed base (fun v=>shaped (fun z=>X v (address (h+l) ((Q (h+l)).symm z)))) mem := by
  intro v p
  let atRow : Row H (2^(h+l)) (2^l) := (v,⟨(ordinal h p).val,by rw [chunkCount];exact (ordinal h p).isLt⟩)
  have coord : (DescentPackedWalsh.row v p).val=(DescentSIMDLookup.row H _ _ atRow).val := by
    change (ordinal h p).val+2^h*v.val=(ordinal h p).val+chunks (2^(h+l)) (2^l)*v.val
    rw [chunkCount]
  rw [coord,old]
  apply congrArg (fun r : Cell (b*2^l)=>(r.val:Word w))
  apply congrArg (encode b (2^l))
  funext j
  have live : (ordinal h p).val*2^l+j.val<2^(h+l) := by
    rw [pow_add]
    calc _ < (ordinal h p).val*2^l+2^l:=Nat.add_lt_add_left j.isLt _
         _ = ((ordinal h p).val+1)*2^l := (Nat.succ_mul ..).symm
         _ ≤ _ := Nat.mul_le_mul_right _ (ordinal h p).isLt
  change (if ok : (ordinal h p).val*2^l+j.val<2^(h+l) then X v ⟨_,ok⟩ else 0)=
    X v (address _ ((Q _).symm (addr p ((ordinal l).symm j))))
  rw [dite_eq_left live]
  apply congrArg (X v)
  apply Fin.ext
  simp only [flat_coordinate,Equiv.apply_symm_apply]

/-- Reading the same original packed tape through the selected-GL block interface costs no instructions. -/
theorem original (base : ℕ) (mem : Memory w) (X : Fin H→Block (h+l)→Cell b)
    (old : Installed base (fun v=>shaped (fun z=>X v (address (h+l) ((Q (h+l)).symm z)))) mem)
    (p : Row H (2^(h+l)) (2^l)) :
    mem (base+(DescentSIMDLookup.row H _ _ p).val)=((data X p).val:Word w) := by
  let positions:=DescentSIMDLookup.row H (2^(h+l)) (2^l)
  let test : Memory w:=fun a=>if z:a-base<H*chunks (2^(h+l)) (2^l) then
    ((data X (positions.symm ⟨_,z⟩)).val:Word w) else 0
  have dictionary (i) : test (base+(positions i).val)=((data X i).val:Word w):=by
    simp [test,(positions i).isLt]
  have spelling:=installed base test X dictionary
  let hi:Cube h:=(ordinal h).symm ⟨p.2.val,(chunkCount h l) ▸ p.2.isLt⟩
  have digit : (ordinal h hi).val=p.2.val:=by simp [hi]
  have same : (DescentPackedWalsh.row p.1 hi).val=(positions p).val:=by
    change (ordinal h hi).val+2^h*p.1.val=p.2.val+chunks (2^(h+l)) (2^l)*p.1.val
    rw [digit]
    exact congrArg (fun n : ℕ => p.2.val + n * p.1.val) (chunkCount h l).symm
  rw [←dictionary,←same,old,spelling]

/-- An old histogram with r blocks per old group and M groups per word
is already in the Walsh RAM input format when the chosen lane count is M*r. -/
theorem from_grouped {J M r : ℕ} (size : 2^(h+l)=J*r) (lanes : 2^l=M*r)
    (hm : 0<M) (hr : 0<r) (base : ℕ) (mem : Memory w) (X : Fin H→Block (h+l)→Cell b)
    (old : ∀p : Row H J M,mem (base+(DescentSIMDLookup.row H J M p).val)=
      ((data (fun v g=>encode b r (fun j=>X v (Fin.cast size.symm (finProdFinEquiv (g,j))))) p).val:Word w)) :
    Installed base (fun v=>shaped (fun z=>X v (address (h+l) ((Q (h+l)).symm z)))) mem :=
  installed base mem X (ungroup_cast size lanes hm hr base mem X old)

end
end Hierarchy.DescentPackedResetSource

end OAI
