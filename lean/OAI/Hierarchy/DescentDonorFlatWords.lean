import OAI.Hierarchy.DescentDonorGatherRAM

namespace OAI
/-! # The grouped donor image is the priced meter's flat chronological source -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentSixParty ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w : ℕ} (s : Shape)

def flat (D : Fin H→Fin (G*s.blocks*s.cap)→Donor 3 s.names s.widths) (h : Fin H) (q : Fin (G*(s.blocks*s.cap))) :=
  packDonor (D h (Fin.cast (Nat.mul_assoc ..).symm q))

theorem sameBits (D : Fin H→Fin (G*s.blocks*s.cap)→Donor 3 s.names s.widths)
    (b : Fin s.blocks) (g : Fin G) (v : Fin H) (c : Fin s.cap) :
    flat s D v (finProdFinEquiv (g,finProdFinEquiv (b,c))) =
      packDonor (D v (finProdFinEquiv (finProdFinEquiv (g,b),c))) := by
  unfold flat
  congr 2
  apply Fin.ext
  simp only [Fin.val_cast,finProdFinEquiv_apply_val]
  ring

/-- A group contains `blocks*cap` physical donor seats. Their order is exactly
the prior global source-then-block-then-first-grain order. -/
theorem flat_read (B prof b slots out : ℕ) (x : Fin H→Fin G→Parts s) (m : Memory w)
    (hm : 0<M) (hr : 0<s.blocks*s.cap)
    (D : Fin H→Fin (G*s.blocks*s.cap)→Donor 3 s.names s.widths)
    (printed : ∀h g u t,(encode (bundleBits 3 s.names s.widths) (s.blocks*s.cap)).symm
      (chip s B prof b slots (x h g)) (finProdFinEquiv (u,t))=packDonor (D h (finProdFinEquiv (finProdFinEquiv (g,u),t))))
    (source : ∀q : Row H G M,m (out+(row H G M q).val)=((data (fun h g=>chip s B prof b slots (x h g)) q).val:Word w))
    (p : Row H (G*s.blocks*s.cap) (M*(s.blocks*s.cap))) :
    m (out+(row H (G*s.blocks*s.cap) (M*(s.blocks*s.cap)) p).val)=
      ((data (fun h g=>packDonor (D h g)) p).val:Word w) := by
  let n:=s.blocks*s.cap
  have eqn:G*s.blocks*s.cap=G*n:=Nat.mul_assoc ..
  let p' : Row H (G*n) (M*n) := (p.1,Fin.cast (congrArg (fun l=>chunks l (M*n)) eqn) p.2)
  let rowEq:=chunks_group G M n hm hr
  let q : Row H G M:=(p'.1,Fin.cast rowEq p'.2)
  have sameRow : (row H (G*s.blocks*s.cap) (M*n) p).val=(row H G M q).val := by
    change p.2.val+chunks (G*s.blocks*s.cap) (M*n)*p.1.val=q.2.val+chunks G M*q.1.val
    exact congrArg (fun z => p.2.val+z*p.1.val)
      ((congrArg (fun l => chunks l (M*n)) eqn).trans rowEq)
  have chart (h : Fin H) (g : Fin G) :
      chip s B prof b slots (x h g)=groupedRows (flat s D) h g := by
    apply (encode (bundleBits 3 s.names s.widths) n).symm.injective
    funext j
    obtain ⟨⟨u,t⟩,rfl⟩:=finProdFinEquiv.surjective j
    simpa only [n,groupedRows,Equiv.symm_apply_apply,sameBits] using printed h g u t
  have dataEq : (data (flat s D) p').val=(data (fun h g=>packDonor (D h g)) p).val := by
    apply congrArg Fin.val
    apply (encode (bundleBits 3 s.names s.widths) (M*n)).symm.injective
    funext i
    simp only [n,data,Equiv.symm_apply_apply]
    by_cases inside:p.2.val*(M*n)+i.val<G*s.blocks*s.cap
    · have inside':p'.2.val*(M*n)+i.val<G*n:=inside.trans_eq eqn
      dsimp only [p', n, Fin.val_cast] at inside inside' ⊢
      simp only [flat, dite_eq_left inside, dite_eq_left inside']
      rfl
    · have outside:¬p'.2.val*(M*n)+i.val<G*n:=fun h=>inside (h.trans_eq eqn.symm)
      dsimp only [p', n, Fin.val_cast] at inside outside ⊢
      simp only [dite_eq_right inside, dite_eq_right outside]
  rw [sameRow,source,←dataEq,data_group hr (flat s D) q p' rfl rfl]
  simp only [chart]
  rfl

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
