import OAI.Hierarchy.DescentTerminalCellFrames
import OAI.Hierarchy.DescentTerminalRolePairProgram
import OAI.Hierarchy.DescentTerminalRoleChannel
import OAI.Hierarchy.DescentTerminalMaskAllocation
import OAI.Hierarchy.DescentTerminalPrimitiveReceipts

namespace OAI
/-! # Carrying the attained terminal primitive fields through subsequent fixed phases -/
namespace Hierarchy.DescentTerminalPrimitiveFrames
open DescentTerminalVertexFields DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {q t H N A p groups blocks shops wb:ℕ}
    (machine:MaskedShelf blocks) (before after:Memory wb) (b:Fin blocks) (i:Fin shops) (g:Fin groups)
local notation "dataAt" => measured (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups)
local notation "whereAt" => finProdFinEquiv (g,b)
local notation "valAt" => fun m k=>venueField (cellAt (dataAt machine m i) whereAt) k
local notation "bank" => fun f:Fin 8=>machine.channel (finProdFinEquiv (b,f.succ))

theorem bank_below (B:Bank) (threshold:ℕ) (low:B.base+B.size≤threshold) (same:∀j<threshold,after j=before j) (j:Word wb) :
    B.read after j=B.read before j := by
  apply same
  have h:=Nat.mod_lt j.val (Nat.two_pow_pos B.bits)
  change j.val%B.size<B.size at h
  omega

theorem field_below (threshold:ℕ) (k:Key H N A)
    (low:(bank (group k)).base+(bank (group k)).size≤threshold) (same:∀j<threshold,after j=before j) :
    valAt after k=valAt before k :=
  field_at machine before after b i g k (bank_below before after _ threshold low same _)

theorem occupation_below (threshold:ℕ)
    (low:(machine.channel (finProdFinEquiv (b,0))).base+(machine.channel (finProdFinEquiv (b,0))).size≤threshold)
    (same:∀j<threshold,after j=before j) :
    (blankAt (dataAt machine after i) whereAt).val=(blankAt (dataAt machine before i) whereAt).val := by
  simp only [presence_digit,measured,Fin.val_natCast,bank_below before after _ threshold low same]

/-- Reuse the genuine earlier occupation bank for the singleton scalar-presence bit. -/
theorem live_at (R:MaskAllocation.Channels blocks) (addr:ℕ) (m:Memory wb) (slot:Fin blocks) (h:Fin shops) (a:Fin groups)
    (alias_:R.primitive slot 1=R.occupied slot) :
    let P:=MaskAllocation.shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) R addr
    let z:=dataAt P m h
    venueField (cellAt z (finProdFinEquiv (a,slot))) (.inr (.inl ()))=(blankAt z (finProdFinEquiv (a,slot))).val := by
  dsimp only
  let P:=MaskAllocation.shelf (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) R addr
  let z:=dataAt P m h
  have same:((cellAt z (finProdFinEquiv (a,slot))) 1).val=(blankAt z (finProdFinEquiv (a,slot))).val := by
    rw [cell_digit,presence_digit]
    have bitWidth : familySize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (1 : Fin 8) = 1 := by
      simp [familySize, items, itemBits]
    let channelBits := channelSize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=blocks)
    have sameWidth : channelBits (finProdFinEquiv (slot,(1 : Fin 8).succ)) =
        channelBits (finProdFinEquiv (slot,(0 : Fin 9))) := by
      simp only [channelBits, channelSize, Equiv.symm_apply_apply, primitiveSize,
        Fin.cases_succ, Fin.cases_zero, bitWidth]
    have sameCast {w₁ w₂ : ℕ} (hw : w₁ = w₂) (x : ℕ) : (x : Word w₁).val = (x : Word w₂).val := by
      subst w₂
      rfl
    simp only [z, P, measured, MaskAllocation.shelf, MaskAllocation.Channels.primitive_at,
      MaskAllocation.Channels.occupied_at, alias_, bitWidth]
    exact congrArg (digit 1 a.val) (sameCast sameWidth _)
  rw [venue_digit]
  change digit 1 0 ((cellAt z (finProdFinEquiv (a,slot))) 1).val = (blankAt z (finProdFinEquiv (a,slot))).val
  rw [same]
  simp [digit,Nat.mod_eq_of_lt (blankAt z (finProdFinEquiv (a,slot))).isLt]

end
end Hierarchy.DescentTerminalPrimitiveFrames

end OAI
