import OAI.Hierarchy.TaggedShorterHistoryCost
import OAI.Hierarchy.TaggedShorterClockCost
import OAI.Hierarchy.TaggedShorterChronoCost
import OAI.Hierarchy.TaggedShorterControlHistory

namespace OAI
/-! # Size of the physical controller cut and all its exposed ports -/

noncomputable section
namespace Hierarchy
open ThreeFlat Routing Diagonal
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open Tagged
open scoped Classical BigOperators

namespace TaggedShorterControlHistory
open TaggedShorterCheapCPU
variable {F : Type*} [CommRing F] {w p r k f S u m a : ℕ}

theorem pins_count :
    Fintype.card (Pin S f u w r m a) =
    (S+f*(5+r)+u)*(w+1) + (2^m)*(3*a*m) := by
  let data : TaggedShorterChronoArray.Input S f u w r ≃ Fin (S*(w+1)+(f*((5+r)*(w+1))+u*(w+1))) :=
    (Equiv.sumCongr finProdFinEquiv ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv
  let layout : Pin S f u w r m a ≃ Fin ((S*(w+1)+(f*((5+r)*(w+1))+u*(w+1)))+a*(pins m m)) :=
    (Equiv.sumCongr data finProdFinEquiv).trans finSumFinEquiv
  rw [Fintype.card_congr layout,Fintype.card_fin]
  unfold pins
  ring

/-- Every gate belongs to a CPU-row check, a chronological row, or the
single stable-sort audit including its native predecessor checks. -/
theorem control_cells (M : Machine w p r k) (ok : ∀ i,Cheap (M.code i))
    (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1)) :
    (network (F:=F) (m:=m) (a:=a) M hw hp st hs ht addr).cells ≤
      (f+1)*TaggedShorterClock.unitPrice w p r +
      2^m*(20000*(w+1)+TaggedShorterHistoryOrder.rowPrice m (w+1) a) := by
  rw [network,TypedWiring.glue_cells,Fintype.sum_option,Fintype.sum_bool]
  change (TaggedShorterClock.network (F:=F) (f:=f) M hw hp st).cells +
    ((TaggedShorterHistoryOrder.audit (F:=F) (m:=m) (a:=a) (by omega : 2≤w+1)).cells+
    (TaggedShorterChronoArray.network (F:=F) (r:=r) (m:=m) hw hs ht addr).cells) ≤ _
  have hh := TaggedShorterClock.clock_cells (F:=F) (f:=f) M ok hw hp st
  have hc := TaggedShorterChronoArray.chrono_cells (F:=F) (r:=r) (m:=m) hw hs ht addr
  have hs' := TaggedShorterHistoryOrder.audit_cells (F:=F) (m:=m) (a:=a) (by omega : 2≤w+1)
  exact (Nat.add_le_add hh (Nat.add_le_add hs' hc)).trans_eq (by ring)

/-- After losslessly removing unused hidden bits, this counts the physical
checker cells, all internal memory/control wires, and every exposed bit.
The coefficient of (f+1)(w+1) depends only on the program dimensions. -/
theorem normalized_size (M : Machine w p r k) (ok : ∀ i,Cheap (M.code i))
    (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u → Word (w+1))
    (fits : S+(f+u)≤2^m) :
    let net := (network (F:=F) (m:=m) (a:=a) M hw hp st hs ht addr).compactHidden
    net.cells + net.internal + Fintype.card (Pin S f u w r m a) ≤
      (f+1)*(w+1)*(4*TaggedShorterClock.unitPrice 1 p r) +
      (2^m)*((100000+r)*(w+1)+(1000+400*a)*(m+1)) := by
  intro net
  let raw := network (F:=F) (m:=m) (a:=a) M hw hp st hs ht addr
  have compact : net.cells+net.internal ≤ 4*raw.cells+1 := BitNetwork.compactHidden_size _
  have hc := control_cells (F:=F) (m:=m) (a:=a) M ok hw hp st hs ht addr
  have cp := Nat.mul_le_mul_left (f+1) (TaggedShorterClock.unitPrice_le w p r)
  have allPins : (S+f*(5+r)+u)*(w+1)≤(2^m)*((5+r)*(w+1)) := by
    rw [←Nat.mul_assoc]
    apply Nat.mul_le_mul_right
    calc
      _ ≤ (S+(f+u))*(5+r) := by ring_nf; omega
      _ ≤ _ := Nat.mul_le_mul_right _ fits
  apply (Nat.add_le_add compact (le_of_eq (pins_count (S:=S) (f:=f) (u:=u) (w:=w) (r:=r) (m:=m) (a:=a)))).trans
  change 4*(network (F:=F) (m:=m) (a:=a) M hw hp st hs ht addr).cells+1+_≤_
  apply (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hc) 1) _).trans
  apply (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.add_le_add_right cp _)) 1)
    (Nat.add_le_add_right allPins _)).trans
  unfold TaggedShorterHistoryOrder.rowPrice
  ring_nf
  have power := (Nat.one_le_two_pow : 1≤2^m)
  omega

end TaggedShorterControlHistory
end Hierarchy

end
end OAI
