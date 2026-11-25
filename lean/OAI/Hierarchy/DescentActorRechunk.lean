import OAI.Hierarchy.DescentOverlapRAM
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Changing lane width on all reset actor sheets in one paid pass -/
namespace Hierarchy.DescentActorRaster
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {Q H G a s t w : ℕ} (x : Fin Q→Fin H→Fin G→Cell a)

def flatSheet (i : Fin (Q*H)) (g : Fin G) :=x (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 g

private theorem flat_read (bank : Bank) (m : Memory w) (slabs : ∀q(p : Row H G s),
    m (bank.base+q.val*(H*chunks G s)+(row H G s p).val)=((data (x q) p).val:Word w)) :
    ∀p : Row (Q*H) G s,m (bank.base+(row (Q*H) G s p).val)=((data (flatSheet x) p).val:Word w) := by
  rintro ⟨v,j⟩
  obtain ⟨⟨q,h⟩,rfl⟩:=finProdFinEquiv.surjective v
  have eq:(row (Q*H) G s (finProdFinEquiv (q,h),j)).val=q.val*(H*chunks G s)+(row H G s (h,j)).val:=by
    simp only [row,finProdFinEquiv_apply_val];ring
  rw [eq,←Nat.add_assoc,slabs]
  simp [data,flatSheet]

theorem change_pitch (base : ℕ) (src : Bank) (m : Memory w) (positive : 0<s) (prior : src.Fits w base)
    (size : Q*H*chunks G s ≤ src.size) (room : Overlap.finish base (Q*H) G s t a<2^w)
    (slabs : ∀q(p : Row H G s),m (src.base+q.val*(H*chunks G s)+(row H G s p).val)=((data (x q) p).val:Word w)) :
    let b:=Overlap.outputBank base (Q*H) G s t a
    let state:=Overlap.result base (Q*H) G s t a src m
    (Overlap.program base (Q*H) G s t a w src).Exec m state (Overlap.ticks base (Q*H) G s t a src) ∧
    (∀q(p:Row H G t),state (b.base+q.val*(H*chunks G t)+(row H G t p).val)=((data (x q) p).val:Word w)) ∧
    (∀n,n<base ∨ Overlap.finish base (Q*H) G s t a≤n→state n=m n) ∧
      CheapCode (Overlap.program base (Q*H) G s t a w src) := by
  obtain ⟨ran,frame,cheap⟩:=Overlap.any base (Q*H) G s t a src m prior room
  refine ⟨ran,?_,frame,cheap⟩
  rintro q ⟨h,j⟩
  have ix:(row (Q*H) G t (finProdFinEquiv (q,h),j)).val=q.val*(H*chunks G t)+(row H G t (h,j)).val:=by
    simp only [row,finProdFinEquiv_apply_val];ring
  have ok:=Overlap.read base src m (flatSheet x) positive prior size (flat_read x src m slabs) room (finProdFinEquiv (q,h),j)
  simpa only [Overlap.outputBank,ix,←Nat.add_assoc,data,flatSheet,Equiv.symm_apply_apply] using ok

end
end Hierarchy.DescentActorRaster

end OAI
