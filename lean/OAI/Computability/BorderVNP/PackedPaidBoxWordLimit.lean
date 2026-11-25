import OAI.Computability.BorderVNP.PackedBankPacketCharges
import OAI.Computability.BorderVNP.CellPacketGeometrySiteWords

/-! # A fixed public word bound for each paid box of a crossing identity -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.BoxRoster

open Crossing CellSparse CellPacketGeometry
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Maximum encoded length of a single known paid box. One word counts its
factor and the next three describe the truth table before its lanes and entries. -/
noncomputable def paidWordLimit : ℕ :=
  Finset.univ.sup fun a : Fin e.count => Finset.univ.sup fun v : (e.net a).Site =>
    (3 + PaidBox.arity e a v + 2^PaidBox.arity e a v) + 1

/-- The complete public one-copy factor stream obeys the fixed identity's
word bound for every numbering of its scalar table entries. -/
theorem paidBoxWords_le {Orig : Type} (number : e.Entry → ℕ) (a : Fin e.count) (v : (e.net a).Site) :
    (SiteWords.boxWords (Orig := Orig) [Sum.inl [PaidBox.tableFactor e number a v]]).length ≤ paidWordLimit e := by
  simp only [SiteWords.boxWords,List.map_cons,List.map_nil,Packet.Source.boxPart,List.flatMap_cons,
    Packet.Source.Part.publicBuffer,List.flatMap_nil,List.append_nil,Packet.fieldList,List.length_cons,
    BankCharges.factor_length]
  exact (Finset.le_sup (s := Finset.univ)
    (f := fun z : (e.net a).Site => (3 + PaidBox.arity e a z + 2^PaidBox.arity e a z) + 1)
    (Finset.mem_univ v)).trans (Finset.le_sup (s := Finset.univ)
      (f := fun b : Fin e.count => Finset.univ.sup fun z : (e.net b).Site =>
        (3 + PaidBox.arity e b z + 2^PaidBox.arity e b z) + 1) (Finset.mem_univ a))

end Packing.Inherited.BoxRoster

end BorderVNP
end Computability
end OAI
