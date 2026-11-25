import OAI.Hierarchy.DescentPackedWords
import OAI.Hierarchy.DescentSparseWordOrder

namespace OAI
/-! # Physical packet digits in the chronological order of each true bundle cell -/

namespace Hierarchy.DescentRotor.Ordered
open DescentOrderedWords
open scoped BigOperators Classical
noncomputable section
variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] {N w u : ℕ}
variable (key : E↪Fin N) (src dst : E→V) (hw : 0<w)

abbrev At (s : V×V) := ↥(cell src dst s.1 s.2)
abbrev Count (s : V×V) := Fin (cell src dst s.1 s.2).card
abbrev Output := Packet w (fun i j=>(cell src dst i j).card) × Fin w

def cells : E≃Σs : V×V,At src dst s where
  toFun e := ⟨(src e,dst e),⟨e,by simp [cell]⟩⟩
  invFun p := p.2.val
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨a,b⟩,⟨e,hit⟩⟩
    obtain ⟨rfl,rfl⟩ : src e=a ∧ dst e=b := by simpa [cell] using hit
    rfl

def cellKey (s : V×V) : At src dst s ↪ Fin N := (Function.Embedding.subtype _).trans key

/-- The ordinal within an occupied cell is precisely the count of its earlier
input IDs. The inverse is used only to compare an existing physical encoding. -/
def ordinal (s : V×V) : At src dst s ≃ Count src dst s :=
  let one : At src dst s ≃ (Σ_:At src dst s,Fin 1) := {
    toFun := fun e=>⟨e,0⟩
    invFun := Sigma.fst
    left_inv := fun _=>rfl
    right_inv := by rintro ⟨e,j⟩;exact congrArg (Sigma.mk e) (Subsingleton.elim _ _) }
  (one.trans (address (cellKey key src dst s) (fun _=>1))).trans (finCongr (by simp [At]))

omit [Fintype V] in
@[simp] theorem ordinal_value (s : V×V) (e : At src dst s) :
    (ordinal key src dst s e).val =
      (Finset.univ.filter fun i : At src dst s=>key i.val<key e.val).card := by
  change offset (cellKey key src dst s) (fun _=>1) e+0=_
  simp [offset,before,cellKey]

def orderedCells := (cells src dst).trans (Equiv.sigmaCongrRight (ordinal key src dst))
def physicalCells := (cells src dst).trans (Equiv.sigmaCongrRight fun s=>(cell src dst s.1 s.2).equivFin)

def permutation : Equiv.Perm E := (orderedCells key src dst).trans (physicalCells src dst).symm

private def place (p : Σs : V×V,Count src dst s) : Output (w:=w) src dst :=
  let n := p.2.val
  have fits : (cell src dst p.1.1 p.1.2).card ≤ groups w (cell src dst p.1.1 p.1.2).card*w :=
    packet_fits hw
  (⟨p.1.1,p.1.2,⟨n/w,(Nat.div_lt_iff_lt_mul hw).2 (p.2.isLt.trans_le fits)⟩⟩,⟨n%w,Nat.mod_lt _ hw⟩)

def orderedAddress (e : E) : Output (w:=w) src dst :=
  place src dst hw (orderedCells key src dst e)

omit [Fintype V] in
theorem orderedAddress_read (e : E) :
    let n := (ordinal key src dst (src e,dst e) ((cells src dst e).2)).val
    (orderedAddress key src dst hw e).1.2.2.val=n/w ∧
    (orderedAddress key src dst hw e).2.val=n%w := ⟨rfl,rfl⟩

omit [Fintype V] in
private theorem legacy_place (e : E) :
    packetAddress src dst hw e=place src dst hw (physicalCells src dst e) := by
  have hit : e∈cell src dst (src e) (dst e) := by simp [cell]
  have image : physicalCells src dst e =
      ⟨(src e,dst e),(cell src dst (src e) (dst e)).equivFin ⟨e,hit⟩⟩ := rfl
  rw [image]
  simp only [packetAddress,serial,dite_eq_left hit,place]

omit [Fintype V] in
theorem packetAddress_permutation (e : E) :
    packetAddress src dst hw (permutation key src dst e)=orderedAddress key src dst hw e := by
  rw [legacy_place]
  exact congrArg (place src dst hw) ((physicalCells src dst).apply_symm_apply _)

omit [Fintype V] in
theorem orderedAddress_injective : Function.Injective (orderedAddress key src dst hw) := by
  intro a b eqn
  apply (permutation key src dst).injective
  apply packetAddress_injective src dst hw
  simpa only [packetAddress_permutation] using eqn

omit [Fintype V] in
/-- Pointwise equality of every packed row digit, including unused digits. -/
theorem packetWord_reindex (x : E→Fin u→Bool) (p : Packet w (fun i j=>(cell src dst i j).card)) :
    packetWord (orderedAddress key src dst hw) x p =
      packetWord (packetAddress src dst hw) (x ∘ (permutation key src dst).symm) p := by
  funext k
  unfold packetWord
  apply congrArg (bitWord w)
  funext j
  by_cases hit : ∃e,orderedAddress key src dst hw e=(p,j)
  · have raw : ∃e,packetAddress src dst hw e=(p,j) :=
      ⟨permutation key src dst hit.choose,(packetAddress_permutation key src dst hw _).trans hit.choose_spec⟩
    have found : permutation key src dst hit.choose=raw.choose :=
      packetAddress_injective src dst hw ((packetAddress_permutation key src dst hw _).trans
        (hit.choose_spec.trans raw.choose_spec.symm))
    simp only [dite_eq_left hit,dite_eq_left raw,Function.comp_apply,←found,Equiv.symm_apply_apply]
  · have raw : ¬∃e,packetAddress src dst hw e=(p,j) := by
      rintro ⟨e,arrives⟩
      apply hit
      refine ⟨(permutation key src dst).symm e,?_⟩
      rw [←packetAddress_permutation,Equiv.apply_symm_apply]
      exact arrives
    simp only [dite_eq_right hit,dite_eq_right raw]

end
end Hierarchy.DescentRotor.Ordered

end OAI
