import OAI.Computability.BorderVNP.CubeScatterPaddingTail
import OAI.Computability.BorderVNP.CubeScatterPadding
import OAI.Computability.BorderVNP.CubeGroupLoad

/-! # Charging the actual native padding tests to the owned groups

Each checked suffix is contained in its bin's fixed capacity. At most two
endpoint traversals can charge the same padded slot to the same coordinate group.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open HostAddress Finset RoutingISA

variable {Team : Type*} {n d blocks b h K s : ℕ} {i : Fin (n+1)} {group : Fin d → Team}
  {number : Team ↪ ℕ} {t : Team} {l : Layout} {mem used : ℕ → ℕ}

/-- For a real team the sum of all native bit-loop lengths is bounded by twice
the raw group load assigned to that team, including pairs with colocated ends. -/
theorem TailHeader.assigned_le_raw (header : TailHeader i group number t l mem used blocks b h K s) :
    (∑ k ∈ range l.count, (l.assigned mem k false + l.assigned mem k true)) ≤
      2 * ∑ g : Fin d, if number (group g) = l.team then groupRaw (blocks*(h*b)) i g else 0 := by
  let P := Label (n+1) d × Label (n+1) d
  let key (p : P) := code p.1 * d^(n+1) + code p.2
  let S := blocks*(h*b)
  let charge (p : P) (g : Fin d) := if number (group g) = l.team ∧ (p.1 i = g ∨ p.2 i = g) then S else 0
  let eqv : P ≃ Fin l.count := ((finFunctionFinEquiv.prodCongr finFunctionFinEquiv).trans finProdFinEquiv).trans
    (finCongr (by simp [Layout.count,header.alphabet.1]))
  have value (p : P) : (eqv p).val = key p := by
    change code p.2 + d^(n+1)*code p.1 = code p.1*d^(n+1)+code p.2
    ac_rfl
  have endpoint_le (p : P) (side : Bool) : l.assigned mem (key p) side ≤ ∑ g, charge p g := by
    by_cases own : l.owner mem (key p) side = l.team
    · have cap : (l.fields mem (key p) side).width ≤ S := by
        simp [Layout.fields,Layout.stride,header.banks.1,header.banks.2.1,S]
      let g := if side then p.2 i else p.1 i
      have hs : number (group g) = l.team := (header.owner_eq p.1 p.2 side).symm.trans own
      have hit : p.1 i = g ∨ p.2 i = g := by cases side <;> simp [g]
      rw [Layout.assigned,ite_eq_left own]
      have one := Finset.single_le_sum (f := charge p) (fun g _ => Nat.zero_le _) (mem_univ g)
      exact cap.trans (by simpa only [charge,hs,hit,and_self,ite_true] using one)
    · simp [Layout.assigned,own]
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ p : P, (l.assigned mem (key p) false + l.assigned mem (key p) true) :=
      (Fintype.sum_equiv eqv _ _ (fun p => by rw [value])).symm
    _ ≤ ∑ p : P, 2 * ∑ g, charge p g := by
      apply sum_le_sum
      intro p _
      exact (Nat.add_le_add (endpoint_le p false) (endpoint_le p true)).trans_eq (two_mul _).symm
    _ = _ := by
      rw [← mul_sum,sum_comm]
      congr 1
      apply sum_congr rfl
      intro g _
      by_cases own : number (group g) = l.team
      · simp only [own,ite_true]
        rw [Fintype.sum_prod_type]
        simp [charge,own,groupRaw,S]
      · simp [charge,own]

/-- The complete native verification budget is linear in candidate pairs and the
physical raw load on this team. -/
theorem TailHeader.budget_le_raw (header : TailHeader i group number t l mem used blocks b h K s) :
    l.budget mem ≤ setup.slots+2+l.count*(2*overhead+2)+
      bitCost * (2 * ∑ g : Fin d, if number (group g) = l.team then groupRaw (blocks*(h*b)) i g else 0) :=
  Nat.add_le_add_left (Nat.mul_le_mul_left bitCost header.assigned_le_raw) _

end Cube.Padding

end BorderVNP
end Computability
end OAI
