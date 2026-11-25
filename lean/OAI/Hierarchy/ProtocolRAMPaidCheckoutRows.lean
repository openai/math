import OAI.Hierarchy.ProtocolRAMPaidWidthCore
import OAI.Hierarchy.ProtocolRAMBinarySpan
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # Reconstructing paid scatter loads from the occupied archive rows -/

namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing BigOperators
variable {W edges : ℕ}

/-- Rowwise agreement of edge addresses and credits determines the load. -/
theorem load_congr (s : Slice) (left right : Memory W) (e : Fin edges)
    (edge : ∀i : Fin s.count,s.edge.eval left (i.val:Word W)=s.edge.eval right (i.val:Word W))
    (amount : ∀i : Fin s.count,s.amount.eval left (i.val:Word W)=s.amount.eval right (i.val:Word W)) :
    s.load left e=s.load right e := by
  unfold Slice.load
  apply Finset.sum_congr rfl
  intro i _
  rw [edge i,amount i]

theorem total_congr (ss : List Slice) (left right : Memory W) (e : Fin edges)
    (same : ∀s∈ss,s.load left e=s.load right e) : total ss left e=total ss right e := by
  apply congrArg List.sum
  exact List.map_congr_left same

theorem total_congr_rows (ss : List Slice) (left right : Memory W) (e : Fin edges)
    (edge : ∀s∈ss,∀i : Fin s.count,s.edge.eval left (i.val:Word W)=s.edge.eval right (i.val:Word W))
    (amount : ∀s∈ss,∀i : Fin s.count,s.amount.eval left (i.val:Word W)=s.amount.eval right (i.val:Word W)) :
    total ss left e=total ss right e :=
  total_congr ss left right e (fun s h=>load_congr s left right e (edge s h) (amount s h))

/-- Only the selected archive word and the index's input fields have to lie
below the checkout flag. The dyadic bank can extend past the flag. -/
theorem lookup_congr_at (base rows flag : ℕ) (t : Expr) (left right : Memory W) (r : Word W)
    (fits : t.Fits W flag) (low : PrefixAgreement.Low flag left right)
    (hit : (t.eval left r).val<rows) (room : base+rows≤flag) :
    (Expr.lookup (⟨base,ProtocolRAMPurchaseSampler.bits rows⟩ : Bank) t).eval left r=(Expr.lookup (⟨base,ProtocolRAMPurchaseSampler.bits rows⟩ : Bank) t).eval right r := by
  have index:=PrefixAgreement.expr t left right flag (PrefixAgreement.inputEnd_of_fits t fits) low r
  have bank : rows≤(⟨base,ProtocolRAMPurchaseSampler.bits rows⟩ : Bank).size := (ProtocolRAMPurchaseSampler.lt_span rows).le
  simp only [Expr.eval,Bank.read,←index,Nat.mod_eq_of_lt (hit.trans_le bank)]
  exact low (base+(t.eval left r).val) (by omega)

end Hierarchy.ProtocolRAM.PaidWidths

end OAI
