import OAI.Hierarchy.DescentResetStemProjectGather

namespace OAI
/-! # Gathering directly from evaluated expressions of the original window -/
namespace Hierarchy.DescentResetStemProjectExpr
open DescentSIMDLookup DescentPackedZip DescentResetStemProject ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {N H G A a w : ℕ}

def passes (src : Fin N→Expr) (H G A base : ℕ) :=
  ProbeStage.Native.columns (H*chunks G A) base (List.ofFn src)

/-- The same evaluator scans each source expression directly into a common host-major
bank, so computed operands can be projected without first issuing one source bank per field. -/
theorem gather_run (base : ℕ) (src : Fin N→Expr) (Y : Fin N→Fin H→Fin G→Cell a) (m : Memory w)
    (fit : ∀q,(src q).Fits w base) (read : ∀q,Source (src q) (Y q) A m)
    (space : base+N*(H*chunks G A)<2^w) :
    let ops:=passes src H G A base
    let last:=result ops m
    (program w ops).Exec m last (clock ops) ∧
      (∀p : Row (N*H) G A,last (base+(row (N*H) G A p).val)=((data (together Y) p).val:Word w)) ∧
      (∀u,u<base ∨ base+N*(H*chunks G A)≤u→last u=m u) := by
  let es:=List.ofFn src
  have size : es.length=N:=List.length_ofFn
  have fits : ∀e∈es,e.Fits w base := by
    intro _ inList
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp inList
    exact fit j
  refine ⟨ProbeStage.Native.columns_exec es m
    (ProbeStage.Native.columns_safe es (le_refl base) fits (by simpa only [size] using space)),?_,?_⟩
  · rintro ⟨v,c⟩
    obtain ⟨⟨q,h⟩,rfl⟩:=finProdFinEquiv.surjective v
    let p : Row H G A:=(h,c)
    have index : q.val<es.length := by rw [size];exact q.isLt
    have word:=ProbeStage.Native.columns_read es m (le_refl base) fits q.val index (row H G A p)
    have entry : es[q.val]'index=src q := by simp only [es,List.getElem_ofFn]
    rw [entry] at word
    rw [combine_row q p,←Nat.add_assoc]
    simpa only [passes,es,p,data,together,Equiv.symm_apply_apply] using word.trans (read q p)
  · intro u hu
    exact ProbeStage.Native.columns_frame es m (by simpa only [size] using hu)

theorem gather_clock (src : Fin N→Expr) (H G A base T : ℕ) (cost : ∀q,(src q).work≤T) :
    clock (passes src H G A base)≤4+N*(4+H*chunks G A*(2*T+4)) := by
  unfold passes
  apply le_trans (ProbeStage.Native.columns_clock _ _ T _ ?_)
  · simp only [List.length_ofFn,le_refl]
  · intro _ member
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp member
    exact cost q

theorem gather_names (src : Fin N→Expr) (H G A base w T : ℕ) (cost : ∀q,(src q).work≤T) :
    ProbeStage.Native.text (program w (passes src H G A base))≤15+N*(11+4*T) := by
  unfold passes
  apply le_trans (ProbeStage.Native.columns_text _ _ _ T _ ?_)
  · simp only [List.length_ofFn,le_refl]
  · intro _ member
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp member
    exact cost q

end
end Hierarchy.DescentResetStemProjectExpr

end OAI
