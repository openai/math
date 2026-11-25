import OAI.Hierarchy.ProtocolRAMPortRanks

namespace OAI
/-! # The local ordinal of a genuine chronological birth event -/

namespace Hierarchy.DescentTerminalChronologicalBooks
open scoped Classical BigOperators
noncomputable section
/-- The address is the count in the physical, possibly sparse, event ledger. -/
def ordinal {I : Type} [Fintype I] (rank : I ↪ ℕ) : I≃Fin (Fintype.card I) :=
  let unit : I≃ProtocolRAMPortRanks.Units (fun _ : I=>1) :=
    { toFun:=fun a=>⟨a,0⟩,invFun:=fun a=>a.1,left_inv:=fun _=>rfl,
      right_inv:=fun ⟨a,b⟩=>by obtain rfl:=Subsingleton.elim b 0; rfl }
  unit.trans ((ProtocolRAMPortRanks.enumerate (fun _ : I=>1) rank rank.injective).trans
    (finCongr (by simp)))

theorem ordinal_val {I : Type} [Fintype I] (rank : I ↪ ℕ) (a : I) :
    (ordinal rank a).val=(Finset.univ.filter fun b=>rank b<rank a).card := by
  change ProtocolRAMPortRanks.prefix (fun _ : I=>1) rank a+0=_
  simp [ProtocolRAMPortRanks.prefix]

end
end Hierarchy.DescentTerminalChronologicalBooks

end OAI
