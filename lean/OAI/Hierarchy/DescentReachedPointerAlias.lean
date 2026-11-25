import OAI.Hierarchy.DescentReachedArgumentPointer

namespace OAI
/-! Extracting the archived private address from the operand at a real argument slot. -/
namespace Hierarchy.DescentOperandStateBanks.Pointer
def privateIndex : Pointer→Option ℕ
  | .privateWord j=>some j
  | .cable .. | .pin ..=>none
end Hierarchy.DescentOperandStateBanks.Pointer

namespace Hierarchy.DescentSixParty.Reached
open DescentKernelHistory DescentLocalArchiveOrder DescentLocalPrivateNames DescentBundleHistory
open DescentCompiler DescentOperandStateBanks
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits}
  {G:PoweredGadget F} {q ε:ℝ} {S:AtomSchedule} {k age grain degree wire hist p R:ℕ}
  (cap:Reached W G q ε S k age grain degree wire hist) (B:BitDescription W) (number:Local B)
  (shape:WorldShape p R B) (hp:0<p) (pin:P→ℕ) (arity:ℕ) (v:W.graph.Site)
local notation "r" => (shape.sites v).recipe hp

theorem slot_privateIndex {K : ℕ} (slots : Slot r↪Fin K)
    (addresses : ∀s : Slot r,(number v s.1).val*arity+s.2.val=(slots s).val) (s : Slot r) :
    (argumentPointer cap B number shape hp pin arity ⟨v,s.1⟩ s.2.val).privateIndex=
    (read r s).map (fun w=>(firstAlias r slots w).val):=by
  obtain ⟨n,j⟩:=s
  unfold argumentPointer
  rw [dite_eq_left j.isLt]
  simp only [Fin.eta,DescentLocalPrivateNames.read]
  cases now:(r).activePort n j with
  | inr hidden=>
    simp [Pointer.privateIndex,privateAddress_at r _ hidden slots addresses]
  | inl ref=>
    obtain ⟨edge|port,chunk,room⟩:=ref
    · rfl
    · rfl

end
end Hierarchy.DescentSixParty.Reached

end OAI
