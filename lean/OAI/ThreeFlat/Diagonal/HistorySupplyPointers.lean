import OAI.ThreeFlat.Diagonal.HistoryGroupedFactor

namespace OAI
/-! # Numerical source selection at a surviving or absorbed motif edge -/

namespace ThreeFlat.Diagonal.MotifKernel

noncomputable section

open LinearAlgebra.SpectralBooks MotifBinaryPacking HistoryContraction
open scoped Classical BigOperators

variable {J G E : Type} [Fintype J] [Fintype G] [Fintype E] [DecidableEq G]
    (P : PortGraph J E) (placement : J → G) (v : G) (I : E → Type) [∀ e, Fintype (I e)]

abbrev ExternalAt := {a : {e // wireOwner P.tail P.head placement e = none} //
    placement (P.tail a.val) = v ∨ placement (P.head a.val) = v}

namespace PrivateOrder

variable {P placement v I} (D : PrivateOrder P placement v I)

/-- Prefix address of a bit on an actually absorbed edge at this site. -/
def privateBit (a : Absorbed P placement v) (t : Fin (D.width a.val)) : Fin D.bits :=
  let n := D.edge.symm a
  let eq : (D.edge n).val = a.val := congrArg Subtype.val (D.edge.apply_symm_apply a)
  finSigmaFinEquiv ⟨n, Fin.cast (congrArg D.width eq.symm) t⟩

omit [Fintype J] [Fintype G] [Fintype E] [(e : E) → Fintype (I e)] in
theorem privateBit_read (bits : Fin D.bits → Bool) (a : Absorbed P placement v) (t : Fin (D.width a.val)) :
    bits (D.privateBit a t) = D.binary a.val (D.decode bits a) t := by
  obtain ⟨i,rfl⟩ := D.edge.surjective a
  refine Eq.trans ?_ (D.packed_bit bits i t).symm
  unfold privateBit
  apply congrArg (fun z : (j : Fin D.count) × Fin (D.lengths j) => bits (finSigmaFinEquiv z))
  have same := D.edge.symm_apply_apply i
  exact Sigma.ext same ((Fin.heq_ext_iff (congrArg D.lengths same)).mpr rfl)

variable {p : ℕ}

/-- An incident party reads each internal wire's sole owner assignment. Its
other ports are relocated by the crossing-wire table. -/
def partySource (cross : (a : ExternalAt P placement v) → Fin (D.width a.val.val) → Fin p)
    (j : {j // placement j = v}) (a : P.Port j.val) (bit : Fin (D.width a.1.1)) : BitSource D.bits p := by
  obtain ⟨⟨e,side⟩,he⟩ := a
  cases side with
  | false =>
    change P.tail e = j.val at he
    by_cases eq : placement (P.tail e) = placement (P.head e)
    · exact .hidden (D.privateBit ⟨e,by rw [wireOwner,ite_eq_left eq,he,j.property]⟩ bit)
    · exact .pin (cross ⟨⟨e,ite_eq_right eq⟩,Or.inl ((congrArg placement he).trans j.property)⟩ bit)
  | true =>
    change P.head e = j.val at he
    by_cases eq : placement (P.tail e) = placement (P.head e)
    · exact .hidden (D.privateBit ⟨e,by simp [wireOwner,eq,he,j.property]⟩ bit)
    · exact .pin (cross ⟨⟨e,ite_eq_right eq⟩,Or.inr ((congrArg placement he).trans j.property)⟩ bit)

omit [Fintype J] [Fintype G] [Fintype E] [(e : E) → Fintype (I e)] in
theorem partySource_read (cross : (a : ExternalAt P placement v) → Fin (D.width a.val.val) → Fin p)
    (pin : Fin p → Bool) (hidden : Fin D.bits → Bool)
    (b : WiresAt P.tail P.head placement (I:=I) none)
    (hcross : ∀ a bit, pin (cross a bit) = D.binary a.val.val (b a.val) bit)
    (j : {j // placement j = v}) (a : P.Port j.val) (bit : Fin (D.width a.1.1)) :
    (D.partySource cross j a bit).read hidden pin = D.binary a.1.1
      (portAt P j.val (atParty P.tail P.head placement j.val b (j.property.symm ▸ D.decode hidden)) a) bit := by
  rcases j with ⟨j,rfl⟩
  rcases a with ⟨⟨e,side⟩,he⟩
  cases side
  · change P.tail e = j at he
    subst j
    by_cases eq : placement (P.tail e) = placement (P.head e) <;>
      simp only [partySource,portAt,atParty,eq,↓reduceDIte,BitSource.read]
    · exact D.privateBit_read hidden ⟨e,by simp [wireOwner,eq]⟩ bit
    · exact hcross ⟨⟨e,by simp [wireOwner,eq]⟩,Or.inl rfl⟩ bit
  · change P.head e = j at he
    subst j
    by_cases eq : placement (P.tail e) = placement (P.head e) <;>
      simp only [partySource,portAt,atParty,eq,↓reduceDIte,BitSource.read]
    · exact D.privateBit_read hidden ⟨e,by simp [wireOwner,eq]⟩ bit
    · exact hcross ⟨⟨e,by simp [wireOwner,eq]⟩,Or.inr rfl⟩ bit

end PrivateOrder
end

end ThreeFlat.Diagonal.MotifKernel

end OAI
