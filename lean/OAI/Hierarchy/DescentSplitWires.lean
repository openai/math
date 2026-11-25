import OAI.Hierarchy.DescentSixPartySeed
import OAI.Computability.BorderVNP.CrossingNetwork

namespace OAI
/-! # Splitting selected actual old wires into ordered six-party demand endpoints -/

namespace Hierarchy.DescentSixParty
open Computability.VPVNP Computability.VPVNP.WireTensor Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)

abbrev Ends := N.Assignment × N.Assignment

def splitRead (T : N.Tables F) (pins : Ports bits) (a : Ends N) (v : N.Site) : F :=
  T v (fun e => if N.src e.val=v then a.1 e.val else a.2 e.val)
    (fun p => pins p.val)

def delta (a : Ends N) (e : N.Edge) : F := if a.1 e=a.2 e then 1 else 0

theorem split_all (T : N.Tables F) (pins : Ports bits) :
    N.value T pins=∑ a : Ends N,(∏v,splitRead N T pins a v)*(∏e,delta (F:=F) N a e) := by
  rw [Fintype.sum_prod_type]
  unfold Network.value
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · simp [splitRead,delta,Network.read]
  · intro b _ ne
    obtain ⟨e,he⟩ := Function.ne_iff.mp ne
    have zero : (∏ e,delta (F:=F) N (a,b) e)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right (Ne.symm he))
    simp [zero]

def bitsFin (w : ℕ) : (Fin w → Bool) ≃ Fin (2^w) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

variable {I : Type*} [Fintype I]

def demandInput (pick : I×Fin 2 ↪ N.Edge) (width : I → ℕ)
    (fit : ∀i s,N.width (pick (i,s))=width i) (a : Ends N) (i : I) :
    ∀j,(MotifBase.binaryWires (k:=F) demandSrc demandDst (fun _ => width i)).Basis j :=
  fun _ => (fun s _ => Fin.cast (congrArg (2^·) (fit i s)) (bitsFin _ (a.1 (pick (i,s)))),
    fun s _ => Fin.cast (congrArg (2^·) (fit i s)) (bitsFin _ (a.2 (pick (i,s)))))

omit [Fintype I] in
theorem demandInput_coeff (pick : I×Fin 2 ↪ N.Edge) (width : I → ℕ)
    (fit : ∀i s,N.width (pick (i,s))=width i) (a : Ends N) (i : I) :
    (MotifBase.binaryWires (k:=F) demandSrc demandDst (fun _ => width i)).coeff
        (demandInput N pick width fit a i) = ∏ s : Fin 2,delta (F:=F) N a (pick (i,s)) := by
  classical
  simp only [MotifBase.binaryWires,wireNetwork,demandInput]
  apply Finset.prod_congr (by ext s;simp only [Finset.mem_univ])
  intro s _
  simp [delta]

def untouched (T : N.Tables F) (pick : I×Fin 2 ↪ N.Edge) (pins : Ports bits) (a : Ends N) : F :=
  (∏ v,splitRead N T pins a v) * ∏ e∈(Finset.univ.map pick)ᶜ,delta N a e

/-- For each complete exposed assignment, the actual old graph is the exact
sum of the unmodified old tensors and cables multiplied by the selected
two-demand tensors. Distinctness of actual selected old wires is essential. -/
theorem expose_batch (T : N.Tables F) (pick : I×Fin 2 ↪ N.Edge) (width : I → ℕ)
    (fit : ∀i s,N.width (pick (i,s))=width i) (pins : Ports bits) :
    N.value T pins=∑ a : Ends N,untouched N T pick pins a *
      ∏ i,(MotifBase.binaryWires (k:=F) demandSrc demandDst (fun _ => width i)).coeff (demandInput N pick width fit a i) := by
  rw [split_all]
  apply Finset.sum_congr rfl
  intro a _
  simp only [untouched,demandInput_coeff,mul_assoc]
  congr 1
  have paid := Finset.prod_compl_mul_prod (Finset.univ.map pick) (delta (F:=F) N a)
  simpa only [Finset.prod_map,Function.comp_apply,Fintype.prod_prod_type] using paid.symm

end
end Hierarchy.DescentSixParty

end OAI
