import OAI.Hierarchy.TaggedWideLeafBanks

namespace OAI
/-! # Native printed rows at the single retained supergroup stage -/

noncomputable section
namespace Hierarchy.Tagged.WideStack.Leaf.PrintedStage
open scoped Classical

universe v
variable {F : Type*} [Field F] {N m groups ports lanes w : ℕ}
    (W : ℕ) (positive : Fin N→Prop) (raw : Fin N→ProtocolRAMEmit.Row)

/-- The printer masks each row by its positive flag at stage zero. The receipt
applies exactly that flag at its public stage W for every dyadic width class. -/
theorem rows_eq :
    (fun _ : Fin (m+1)=>atScale positive (fun _=>0) 0 raw)=
      (fun _ : Fin (m+1)=>atScale positive (fun _=>W) W raw) := by
  funext t j
  simp [atScale]

abbrev Family (F : Type*) [Field F] (groups ports lanes w m : ℕ)
    (rows : Fin (m+1)→Fin N→ProtocolRAMEmit.Row) :=
  ∀t : Fin (m+1),Installed F groups ports lanes w m t.val (rows t)

private def changeRows {a b : Fin (m+1)→Fin N→ProtocolRAMEmit.Row} (same : a=b)
    (installed : Family F groups ports lanes w m a) : Family F groups ports lanes w m b :=
  same ▸ installed

private def changeFacts {a b : Fin (m+1)→Fin N→ProtocolRAMEmit.Row} (same : a=b)
    (installed : Family F groups ports lanes w m a)
    (P : (r : Fin (m+1)→Fin N→ProtocolRAMEmit.Row)→Family F groups ports lanes w m r→Sort v)
    (facts : P a installed) : P b (changeRows same installed) := by
  subst b
  exact facts

variable (printed : Family F groups ports lanes w m (fun _=>atScale positive (fun _=>0) 0 raw))

include printed in
def atStage : Family F groups ports lanes w m (fun _=>atScale positive (fun _=>W) W raw) :=
  changeRows (rows_eq (m:=m) W positive raw) printed

/-- Move the entire dependent receipt, including its concrete private numbering,
cut assignments and mask equations, across the one equality of row families. -/
def transport (P : (r : Fin (m+1)→Fin N→ProtocolRAMEmit.Row)→Family F groups ports lanes w m r→Sort v)
    (facts : P (fun _=>atScale positive (fun _=>0) 0 raw) printed) :
    P (fun _=>atScale positive (fun _=>W) W raw) (atStage W positive raw printed) :=
  changeFacts (rows_eq (m:=m) W positive raw) printed P facts

theorem banks_eq : banks (atStage W positive raw printed)=banks printed :=
  transport W positive raw printed (fun _ installed=>banks installed=banks printed) rfl

end Hierarchy.Tagged.WideStack.Leaf.PrintedStage
end

end OAI
