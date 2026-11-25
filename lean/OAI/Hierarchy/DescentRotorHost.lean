import OAI.Hierarchy.DescentRotorFamily
import OAI.Hierarchy.DescentAttachmentGraph

namespace OAI
/-! # The rotor with one exposed tap for each incident edge and each row -/

namespace Hierarchy.DescentRotor
open LinearAlgebra.SpectralBooks ThreeFlat
open RouteUnits Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section

/-- Evaluate a named-port table on a real degree-three path, using an enumeration
chosen once from the local host incidence, independently of the permutation. -/
def pathRead {S : Type*} [Fintype S] {A : S → Type*} [∀ s, Fintype (A s)]
    {K : Type*} [CommSemiring K] (tab : (∀ s, A s) → K) (x : ∀ s,A s) : K :=
  let packed := Equiv.piCongrLeft' A (Fintype.equivFin S)
  (Attachment.path (Fintype.card S)).contraction (A:=fun _ => (i : Fin (Fintype.card S)) → A ((Fintype.equivFin S).symm i))
    (Attachment.localTable (tab ∘ packed.symm) (packed x))

theorem pathRead_eq {S : Type*} [Fintype S] {A : S → Type*} [∀ s,Fintype (A s)]
    {K : Type*} [CommSemiring K] (tab : (∀ s, A s) → K) (x : ∀ s,A s) :
    pathRead tab x=tab x := by simp [pathRead,Attachment.path_contraction]

variable {Y : ℕ}

abbrev Slot (c : Fin Y → Fin Y → ℕ) (v : Fin Y) := Bool ⊕ (supplyGraph c).Port v

def SlotWidth (c : Fin Y → Fin Y → ℕ) (C w : ℕ) (v : Fin Y) : Slot c v → ℕ
  | .inl _ => w
  | .inr _ => C*w

variable {c : Fin Y → Fin Y → ℕ} {C w : ℕ}

/-- All calls run on the same path graph, with the rotor's two actual row
terminals at two different taps and one tap for each host half-edge. -/
def attachedLayer {F : Type*} [Field F]
    (tab : (v : Fin Y) → Fin (2^w) → Fin (2^w) →
      (supplyGraph c).State (fun _ => Fin (2^(C*w))) v → F)
    (u : ℕ) (x y : Fin Y → Fin u → Fin (2^w)) : F :=
  (supplyGraph c).contraction (A:=fun _ => Fin u → Fin (2^(C*w)))
    (fun v state =>
      let A := fun s : Slot c v => Fin u → Fin (2^SlotWidth c C w v s)
      let args : ∀ s,A s := fun
        | .inl false => x v
        | .inl true => y v
        | .inr p => state p
      pathRead (fun entry : (s : Slot c v) → A s =>
        ∏ k, tab v (entry (.inl false) k) (entry (.inl true) k)
          (fun p => entry (.inr p) k)) args)

theorem attachedLayer_eq {F : Type*} [Field F]
    (tab : (v : Fin Y) → Fin (2^w) → Fin (2^w) →
      (supplyGraph c).State (fun _ => Fin (2^(C*w))) v → F)
    (u : ℕ) (x y : Fin Y → Fin u → Fin (2^w)) :
    attachedLayer tab u x y =
      (supplyGraph c).contraction (A:=fun _ => Fin u → Fin (2^(C*w)))
        (fun v state => ∏ k, tab v (x v k) (y v k) (fun p => state p k)) := by
  simp only [attachedLayer,pathRead_eq]

/-- Outgoing host arcs and incoming host arcs give disjoint local ports, also
when the host has parallel arcs. -/
private def arcPorts (c : Fin Y → Fin Y → ℕ) (v : Fin Y) :
    (supplyGraph c).Port v ≃ (Σ j, Fin (c v j)) ⊕ (Σ i, Fin (c i v)) where
  toFun p := by
    rcases p with ⟨⟨⟨⟨i,j⟩,k⟩,b⟩,hit⟩
    cases b
    · change i=v at hit
      subst i
      exact .inl ⟨j,k⟩
    · change j=v at hit
      subst j
      exact .inr ⟨i,k⟩
  invFun
    | .inl ⟨j,k⟩ => ⟨(⟨(v,j),k⟩,false),rfl⟩
    | .inr ⟨i,k⟩ => ⟨(⟨(i,v),k⟩,true),rfl⟩
  left_inv := by
    rintro ⟨⟨⟨⟨i,j⟩,k⟩,b⟩,hit⟩
    cases b
    · change i=v at hit
      subst i
      rfl
    · change j=v at hit
      subst j
      rfl
  right_inv := by rintro (⟨j,k⟩|⟨i,k⟩) <;> rfl

private theorem regular_ports {n h : ℕ} (G : Graph n h) (v : Fin (2^n)) :
    Fintype.card ((supplyGraph G.arcs).Port v)=2*h := by
  rw [Fintype.card_congr (arcPorts G.arcs v),Fintype.card_sum]
  simp only [Fintype.card_sigma,Fintype.card_fin,G.regular]
  rw [show (∑i, G.arcs i v)=h from (Finset.sum_congr rfl (fun i _ => G.symmetric i v)).trans (G.regular v)]
  omega

theorem regular_slots {n h : ℕ} (G : Graph n h) (v : Fin (2^n)) :
    Fintype.card (Slot G.arcs v)=2*h+2 := by simp [Slot,regular_ports,Nat.add_comm]

/-- Conservative total wire incidence of all the actual paths, with every
inter-site wire charged at both ends. The coefficient of Y*w*u depends only on
the common degree and the common per-edge expansion, as required by the reset. -/
theorem attached_bit_cost {n h : ℕ} (G : Graph n h) (C w u : ℕ) :
    (∑ v : Fin (2^n), Attachment.bitCost
      (fun i => SlotWidth G.arcs C w v ((Fintype.equivFin (Slot G.arcs v)).symm i)) u)
        = (2*h+4)*(2*h*C+2)*(2^n)*w*u := by
  have total (v : Fin (2^n)) :
      (∑ i, SlotWidth G.arcs C w v ((Fintype.equivFin (Slot G.arcs v)).symm i))=
        2*w+2*h*(C*w) := by
    rw [Equiv.sum_comp (Fintype.equivFin (Slot G.arcs v)).symm]
    rw [Fintype.sum_sum_type]
    simp [SlotWidth,regular_ports,two_mul]
  simp only [Attachment.bitCost_eq,total,regular_slots,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]
  ring

theorem attached_vertex_count {n h : ℕ} (G : Graph n h) :
    (∑ v : Fin (2^n), Fintype.card (Attachment.Site (Fintype.card (Slot G.arcs v)))) =
      (2*h+4)*(2^n) := by
  calc
    _ = ∑ _v : Fin (2^n), ((2*h+2)+2) := by
      apply Finset.sum_congr rfl
      intro v _
      exact (Attachment.card_sites _).trans (congrArg (· + 2) (regular_slots G v))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
      ring

end
end Hierarchy.DescentRotor

end OAI
