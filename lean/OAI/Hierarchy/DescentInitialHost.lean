import OAI.Computability.BorderVNP.BitVolume
import Mathlib.Tactic

namespace OAI
/-! # The initial trivalent core and the separate tether at every open bit -/

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section
variable {D : ℕ} {P : Type*} [Fintype P] (N : Network D P (fun _ => 1))

abbrev Site := N.Site ⊕ P
abbrev Wire := N.Edge ⊕ P
abbrev OldPort := P ⊕ (N.Edge × Bool)

def owner : OldPort N → N.Site :=
  Sum.elim N.attach (fun eb => if eb.2 then N.dst eb.1 else N.src eb.1)

def opposite : OldPort N → Site N :=
  Sum.elim Sum.inr (fun eb => .inl (if eb.2 then N.src eb.1 else N.dst eb.1))

def source : Wire N → Site N := Sum.elim (fun e => .inl (N.src e)) (fun p => .inl (N.attach p))
def target : Wire N → Site N := Sum.elim (fun e => .inl (N.dst e)) Sum.inr

def near : Site N → Finset (Site N)
  | .inl v => (Finset.univ.filter (fun e => owner N e=v)).image (opposite N)
  | .inr p => {.inl (N.attach p)}

theorem near_le_three (h : N.Trivalent) (v : Site N) : (near N v).card≤3 := by
  rcases v with v|p
  · exact Finset.card_image_le.trans (h.2 v)
  · simp [near]

theorem wire_near (e : Wire N) : target N e∈near N (source N e) ∧ source N e∈near N (target N e) := by
  rcases e with e|p
  · constructor
    · exact Finset.mem_image.mpr ⟨.inr (e,false),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,by simp [opposite,target]⟩
    · exact Finset.mem_image.mpr ⟨.inr (e,true),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,by simp [opposite,source]⟩
  · exact ⟨Finset.mem_image.mpr ⟨.inl p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩,Finset.mem_singleton_self _⟩

theorem near_iff (a b : Site N) :
    b∈near N a ↔ ∃ e : Wire N,
      (source N e=a ∧ target N e=b) ∨ (source N e=b ∧ target N e=a) := by
  constructor
  · intro h
    rcases a with v|p
    · obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp h
      have eqn := (Finset.mem_filter.mp hz).2
      rcases z with p|⟨e,bit⟩
      · exact ⟨.inr p,Or.inl ⟨congrArg Sum.inl eqn,rfl⟩⟩
      · cases bit
        · exact ⟨.inl e,Or.inl ⟨congrArg Sum.inl eqn,rfl⟩⟩
        · exact ⟨.inl e,Or.inr ⟨rfl,congrArg Sum.inl eqn⟩⟩
    · obtain rfl := Finset.mem_singleton.mp h
      exact ⟨.inr p,Or.inr ⟨rfl,rfl⟩⟩
  · rintro ⟨e,h|h⟩
    · rcases h with ⟨rfl,rfl⟩; exact (wire_near N e).1
    · rcases h with ⟨rfl,rfl⟩; exact (wire_near N e).2

theorem near_symm (a b : Site N) : b∈near N a ↔ a∈near N b := by
  rw [near_iff,near_iff]
  exact exists_congr fun _ => or_comm

/-- Old tables now read new tether bits y. Each new hub equates exactly its
own tether to the corresponding prescribed exterior bit. Contraction over
all tether labels and the unchanged core equals the original complete tensor. -/
theorem with_hubs {F : Type*} [CommSemiring F] (T : N.Tables F) (x : P → Fin 1 → Bool) :
    (∑ y : P → Fin 1 → Bool, ∑ a : N.Assignment,
      (∏ v, N.read T a y v) * (∏ p : P, if y p=x p then (1:F) else 0)) =
      N.value T x := by
  classical
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)]
  · simp [Network.value]
  · intro y _ diff
    obtain ⟨p,hp⟩ := Function.ne_iff.mp diff
    have zero : (∏ p : P, if y p=x p then (1:F) else 0)=0 :=
      Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right hp)
    simp [zero]

theorem host_card : Fintype.card (Site N)+Fintype.card (Wire N)=N.bitVolume+Fintype.card P := by
  simp [Site,Wire,Network.bitVolume];omega

end
end Hierarchy.DescentInitialHost

end OAI
