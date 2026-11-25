import OAI.Hierarchy.DescentMetadataInputCore
import OAI.Hierarchy.DescentDatedResetOperands

namespace OAI
/-! # Authentic scalar span pages of the dated reset operand publisher -/
namespace Hierarchy.DescentResetMetadataInputs
open DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {N K H G M w a b c : ℕ}

/-- Exact original scalar page inside the post-reset state. Its node-major index is
the same one used by the seven pointer publishers. -/
def spanBank (v : DescentDatedAddressBook.ResetOutput) (s : v.OperandInputs) (base : ℕ)
    (x : Fin v.receiver.blocks) (node : Fin s.nodes) (arg : Fin s.slots) : Bank :=
  let rows:=v.receiver.hosts*chunks v.receiver.groups v.receiver.lanes
  ⟨v.operandDictionaryEnd base+(v.operandOrdinal s 6 arg x node).val*rows,Nat.clog 2 (rows+1)⟩

def spanLookup (v : DescentDatedAddressBook.ResetOutput) (s : v.OperandInputs) (base : ℕ)
    (x : Fin v.receiver.blocks) (node : Fin s.nodes) (arg : Fin s.slots) : Expr :=
  .lookup (spanBank v s base x node arg) .row

theorem span_prior_blank (v : DescentDatedAddressBook.ResetOutput) (s : v.OperandInputs) (r : v.RenderInputs) (base : ℕ)
    (x : Fin v.receiver.blocks) (node : Fin s.nodes) (arg : Fin s.slots) (j : Fin (2*v.receiver.candidates)) :
    v.previous s r base (v.operandOrdinal s 6 arg x node) j=.lit 0 := by
  simp [DescentDatedAddressBook.ResetOutput.previous,v.operandIndex_ordinal,
    DescentDatedAddressBook.ResetOutput.pointerField]

/-- The f6 page used by the count is literally the paid scalar terminal output present
before the node book was packed. Any intervening steps need preserve only this page. -/
theorem span_issued (v : DescentDatedAddressBook.ResetOutput) (s : v.OperandInputs) (r : v.RenderInputs)
    (base floor : ℕ) (m saved : Memory w) (early : v.OperandEarly s r w base) (room : v.scalarEnd base<2^w)
    (small : 2*v.receiver.candidates<2^v.receiver.queryBits)
    (q : Fin v.receiver.fields→Fin v.receiver.hosts→Fin v.receiver.groups→Option (Fin (2*v.receiver.candidates)))
    (raw : Fin v.receiver.fields→Fin (2*v.receiver.candidates)→Fin v.receiver.hosts→Fin v.receiver.groups→Cell v.receiver.signedBits)
    (kept value : Fin v.receiver.fields→Fin v.receiver.hosts→Fin v.receiver.groups→Cell s.coeff)
    (readQ : ∀i,Source (s.query i) (fun h g=>DescentOperandCandidateLookup.code small (q i h g)) v.receiver.lanes m)
    (keptAt : ∀i,Source (s.kept i) (kept i) v.receiver.lanes m)
    (readRaw : ∀i j,Source (v.previous s r base i j) (raw i j) v.receiver.lanes m)
    (combine : ∀i h g,(kept i h g).val+
      (DescentOperandCandidateLookup.selected (q i) (fun j h g=>((raw i j h g).val:Cell s.coeff)) h g).val=(value i h g).val)
    (x : Fin v.receiver.blocks) (node : Fin s.nodes) (arg : Fin s.slots)
    (fits : (spanBank v s base x node arg).Fits w floor)
    (frame : ∀j<v.receiver.hosts*chunks v.receiver.groups v.receiver.lanes,
      saved ((spanBank v s base x node arg).base+j)=v.operandMemory s r base m ((spanBank v s base x node arg).base+j)) :
    Source (spanLookup v s base x node arg) (value (v.operandOrdinal s 6 arg x node)) v.receiver.lanes saved :=by
  let b₀:=spanBank v s base x node arg
  have rows : v.receiver.hosts*chunks v.receiver.groups v.receiver.lanes≤b₀.size:=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  apply source_column b₀ floor fits saved _ rows
  intro t
  rw [frame _ (row _ _ _ t).isLt]
  exact v.operand_read s r base m early room small q raw kept value readQ keptAt readRaw combine
    (v.operandOrdinal s 6 arg x node) t

end
end Hierarchy.DescentResetMetadataInputs

end OAI
