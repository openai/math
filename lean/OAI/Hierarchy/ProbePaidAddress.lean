import OAI.Hierarchy.ProtocolRAMCalendarInstalledCharge

namespace OAI
/-! # The paid toll of an original word address, with the true discarded-address convention -/
noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM PaidWidths
open ThreeFlat.RAM
open scoped BigOperators Classical Fin.CommRing

def addressPrice {n : ℕ} (len : Fin n→ℝ) (key : ℕ) : ℝ :=
  if ok : key<n then len ⟨key,ok⟩ else 0

@[simp] theorem addressPrice_fin {n : ℕ} (len : Fin n→ℝ) (e : Fin n) : addressPrice len e.val=len e := by
  simp [addressPrice,e.isLt]

theorem PaidWidths.actual_toll {W edges : ℕ} (s : Slice) (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) :
    s.toll m len payload=(∑ i : Fin s.count,((s.amount.eval m (i.val:Word W)).val:ℝ)*
      addressPrice len (s.edge.eval m (i.val:Word W)).val)/payload := by
  have raw : (∑ e : Fin edges, (s.load m e : ℝ) * len e) =
      ∑ i : Fin s.count, ((s.amount.eval m (i.val : Word W)).val : ℝ) *
        addressPrice len (s.edge.eval m (i.val : Word W)).val := by
    simp only [Slice.load,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    let key:=(s.edge.eval m (i.val:Word W)).val
    by_cases inside : key<edges
    · let e : Fin edges:=⟨key,inside⟩
      change (∑ j : Fin edges,if e.val=j.val then _ else 0)=_ * addressPrice len e.val
      simp [Fin.val_inj]
    · have absent (j : Fin edges) : key≠j.val := fun eq=>inside (eq ▸ j.isLt)
      change (∑ j : Fin edges,if key=j.val then _ else 0)=_ * addressPrice len key
      simp [absent,addressPrice,inside]
  rw [←raw,Finset.sum_div]
  exact Finset.sum_congr rfl (fun e _=>by ring)

namespace Calendar
variable {z d k q goods W edges r : ℕ}

theorem Format.address_direct (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) (width : p.occurrences≤2^W) :
    let l:=p.labelSource sink idBase role ids
    (PaidWidths.paidDirect p.pricedArea p.stockSource l).toll m len payload=
      (∑ i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*addressPrice len (l.edge.eval m (i.val:Word W)).val)/payload := by
  intro l
  rw [PaidWidths.actual_toll]
  apply congrArg (fun total : ℝ => total / payload)
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun amount : ℕ => (amount : ℝ) * addressPrice len (l.edge.eval m (i.val : Word W)).val)
    (PaidWidths.paidDirect_bits p.pricedArea p.stockSource l m i width)

theorem Format.address_mate (p : Format z d k q goods) (forest : Traversals) (mask second : Expr)
    (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) (width : p.occurrences≤2^W)
    (entry : forest.catalystMate=some (mask,second)) :
    ((p.mateSlices forest).map (fun s=>s.toll m len payload)).sum=
      (∑ i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*
        (if mask.eval m (i.val:Word W)=0 then 0 else addressPrice len (second.eval m (i.val:Word W)).val))/payload := by
  let s:=PaidWidths.paidMate p.pricedArea p.stockSource mask second
  simp only [mateSlices,entry,Option.toList_some,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [PaidWidths.actual_toll]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [PaidWidths.paidMate_bits _ _ _ _ m i width]
  split_ifs <;> simp [PaidWidths.paidMate]

end Calendar
end Hierarchy.ProtocolRAM
end

end OAI
