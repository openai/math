import OAI.Hierarchy.TaggedWireSiteMatrix
import OAI.Hierarchy.ProbePlacedTerm

namespace OAI
/-! # The physical terminal edge-word basis of a prescribed signed contraction -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe
open scoped Classical BigOperators

variable {S n : ℕ} {F : Type*} [Field F]

/-- A one-row graph has exactly one nontrivial mixed-radix coordinate. -/
def oneRow (a : Chord S) (b : ℕ) : ((e : Chord S)→Index (b • unitChord a) e) ≃ Fin (2^b) where
  toFun x := Fin.cast (by simp [unitChord]) (x a)
  invFun x e := if h : e=a then Fin.cast (by subst e; simp [unitChord]) x else 0
  left_inv x := by
    funext e
    by_cases h : e=a
    · subst e
      apply Fin.ext
      simp; rfl
    · have tiny : (x e).val<1 := by
        simpa [unitChord,Finsupp.smul_apply,Finsupp.single_apply,h,Ne.symm h] using (x e).isLt
      apply Fin.ext
      simp only [dite_eq_right h,Fin.val_zero]
      omega
  right_inv x := by apply Fin.ext; simp; rfl

/-- Parallel and oppositely listed physical links keep separate words in
their native row order at both chord endpoints. -/
def edgeWords (ends : Fin n→Chord S) (bits : Fin n→ℕ) :
    ((e : Chord S)→Index (installedWidths ends bits) e) ≃ (∀r,Fin (2^(bits r))) :=
  let U (r : Fin n) := bits r • unitChord (ends r)
  (Equiv.piCongrRight (fun e=>blockWireIndex U e)).trans
    ((Equiv.piComm (fun e r=>Index (U r) e)).trans (Equiv.piCongrRight fun r=>oneRow (ends r) (bits r)))

def readEdges (ends : Fin n→Chord S) (bits : Fin n→ℕ) (data : ∀r,Fin (2^(bits r))) (i : Fin S) :
    State (installedWidths ends bits) i :=
  (portGraph S).atVertex ((edgeWords ends bits).symm data) i

@[instance_reducible]
private def wordEnumeration {E : Type} [Fintype E] (A : E→Type) [∀e,Fintype (A e)] :
    Fintype ((e:E)→A e) := inferInstance

@[instance_reducible]
private def stateEnumeration {V E : Type} [Fintype V] [Fintype E] (G : PortGraph V E) (A : E→Type)
    [∀e,Fintype (A e)] : Fintype ((v:V)→G.State A v) := inferInstance

/-- The grouped state sum and the edge-word sum are independent of the
specific finite enumerations of their two dependent function spaces. -/
private theorem independent_words {V E : Type} [Fintype V] [Fintype E] (G : PortGraph V E)
    (A : E→Type) [∀e,Fintype (A e)] (states : Fintype ((v:V)→G.State A v))
    (words : Fintype ((e:E)→A e)) (U : (v:V)→G.State A v→F) :
    (@Finset.univ _ states).sum (fun x=>G.wiring A x * ∏v,U v (x v))=
      (@Finset.univ _ words).sum (fun a=>∏v,U v (G.atVertex a v)) := by
  have statesEq : states=stateEnumeration G A := Subsingleton.elim _ _
  have wordsEq : words=wordEnumeration A := Subsingleton.elim _ _
  subst states
  subst words
  exact (G.contraction_eq_wiring A U).symm

/-- This is the pointwise target of the fixed physical universal host after
one common binary word is assigned per reported positive native edge. -/
theorem act_edge_words {A : Fin S→Type} (ends : Fin n→Chord S) (bits : Fin n→ℕ)
    (M : SiteMatrix A (State (installedWidths ends bits)) F) (v : ∀i,A i) :
    SiteMatrix.act M (raw F (installedWidths ends bits)).coeff v =
      ∑ e : ∀r,Fin (2^(bits r)), ∏ i,M i (v i) (readEdges ends bits e i) := by
  let U := installedWidths ends bits
  let f := fun (e : ∀j,Index U j)=>∏ i,M i (v i) ((portGraph S).atVertex e i)
  calc
    _ = ∑ e : (j:Chord S)→Index U j,f e :=
      independent_words (portGraph S) (Index U) inferInstance inferInstance (fun i y=>M i (v i) y)
    _ = _ := ((edgeWords ends bits).symm.sum_comp f).symm

end Hierarchy.WireTelescope

end
end OAI
