import OAI.Computability.BorderVNP.DiagonalExternalSewFieldCount
import OAI.Computability.BorderVNP.DiagonalExternalSewPortIndex

/-! # Public addresses of occupied intervals in the actual skipped-partner fields -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

/-- Both named ends of a processor's physical direct link, in the local field order. -/
def physicalEnds (R r : ℕ) : Bool × (Routing.Block (R+1) × Fin r) ↪ Fin (R+1) × (Fin r × Fin R) where
  toFun x := (fieldTeam x.2.1 x.1, x.2.2, fieldRank x.2.1 x.1)
  inj' := by
    rintro ⟨s,b,i⟩ ⟨t,c,j⟩ h
    have hr := congrArg (fun x : Fin (R+1) × (Fin r × Fin R) => (x.1,x.2.2)) h
    have hp := congrArg (fun x : Fin (R+1) × (Fin r × Fin R) => x.2.1) h
    have hs : (s,b) = (t,c) := (endpointEquiv R).injective hr
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hs
    exact congrArg (fun k => (s,b,k)) hp

variable {R r : ℕ}

/-- The address of offset zero of the field for the other team. -/
abbrev fieldStart (literal stride link : ℕ) :=
  endStart (physicalEnds R r) literal stride link

/-- The initial team and block hosting the indicated end of an occupied interval. -/
abbrev fieldBlock (literal stride link g : ℕ) :=
  endBlock (physicalEnds R r) literal stride link g

variable (literal stride link g : ℕ)

/-- Both original addresses use the same ordered offset within the physical field. -/
theorem fieldBlock_bit (c : Pieces (fieldStart (R := R) (r := r) literal stride link) g link) (s : Bool)
    (j : Fin (pieceWidth _ _ c)) :
    fieldBlock literal stride link g c s =
      (fieldTeam c.1.1 s, (c.1.2.val*stride + literal + (fieldRank c.1.1 s).val*link +
        (pieceOffset _ _ c j).val)/g) := by
  have h := pieceOffset_blocks _ _ c j
  cases s
  · exact Prod.ext rfl (congrArg Prod.fst h).symm
  · exact Prod.ext rfl (congrArg Prod.snd h).symm

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
