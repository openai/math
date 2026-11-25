import OAI.Hierarchy.DescentPackedLocalAtoms

namespace OAI
/-! The full predecessor mask is counted independently of the atom tariff. -/
namespace Hierarchy.DescentOrdinaryPopulation
open DescentSIMDLookup DescentPackedLocalAtoms
open scoped Classical Fin.CommRing
noncomputable section

def fill (K n : ℕ) : Cell (1*K) :=
  encode 1 K (fun j=>if j.val<n then 1 else 0)

def compress {N : ℕ} (K : ℕ) (x : Cell (1*N)) : Cell (1*K) :=
  fill K (present ((encode 1 N).symm x)).card

@[simp] theorem fill_zero (K : ℕ) : fill K 0=0 := by
  simp only [fill,Nat.not_lt_zero,ite_false]
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin K=>(0 : Cell 1))).val=0
  simp []

@[simp] theorem compress_zero {N : ℕ} (K : ℕ) : compress (N:=N) K 0=0 :=by
  have e : (encode 1 N).symm 0=fun _=>0 :=by
    apply (encode 1 N).injective
    rw [Equiv.apply_symm_apply]
    symm
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin N=>(0 : Cell 1))).val=0
    simp []
  simp [compress,e,present]

theorem compress_mask {X : Type*} [Fintype X] {N K : ℕ}
    (id_ : X↪Fin N) (mask : Fin N→Cell 1)
    (exact_ : ∀i,mask i≠0 ↔ ∃x,id_ x=i) :
    compress K (encode 1 N mask)=fill K (Fintype.card X) :=by
  have same : present mask=Finset.univ.map id_ :=by
    ext i
    simp [present,exact_,Finset.mem_map]
  simp [compress,same]

theorem live_iff (K n : ℕ) (j : Fin K) :
    (encode 1 K).symm (fill K n) j≠0 ↔ j.val<n :=by
  simp [fill]

end
end Hierarchy.DescentOrdinaryPopulation

end OAI
