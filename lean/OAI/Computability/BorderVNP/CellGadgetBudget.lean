import OAI.Computability.BorderVNP.CellGadgetRows
import OAI.Computability.BorderVNP.CellBoxCost

/-! # Native bytecode clocks for announced gadget subtotals

A separate local flag square checks each announced count against the full
occurrence scan. These bounds charge its allocation and disposal, every prefix
candidate, all digit checks, and the unary offsets of reads into the physical bank.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro

private theorem all_nodes (ts : List Term) : (Term.all ts).nodes = (ts.map Term.nodes).sum + ts.length + 1 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Term.all,Term.nodes] at ih ⊢; omega

private theorem all_bounded (ts : List Term) (e : List ℕ) (A : ℕ) (h : ∀ t ∈ ts, t.Bounded e A) :
    (Term.all ts).Bounded e A := by
  induction ts with
  | nil => trivial
  | cons t ts ih => exact ⟨h _ List.mem_cons_self, ih (fun t ht => h _ (.tail _ ht))⟩

/-- Each binary digit requires nine nodes in an equality and one conjunction. -/
theorem digitChecks_nodes (off : ℕ) (bits : List ℕ) (k : NatExpr) :
    (digitChecks off bits k).nodes = 10*bits.length+1 := by
  simp [digitChecks,all_nodes,List.map_map,Function.comp_def,Term.nodes,List.map_const']
  omega

/-- The digit comparisons read exactly the reported bit addresses behind the scratch bank. -/
theorem digitChecks_bounded (off : ℕ) (bits : List ℕ) (k : NatExpr) (e : List ℕ) {A : ℕ}
    (hb : ∀ b ∈ bits, off+b ≤ A) : (digitChecks off bits k).Bounded e A := by
  apply all_bounded
  intro t ht
  obtain ⟨bi,hbi,rfl⟩ := List.mem_map.mp ht
  exact (Term.bounded_equal ..).mpr ⟨hb _ (List.fst_mem_of_mem_zipIdx hbi),trivial⟩

/-- Charge the final announced-word comparison once per possible subtotal. -/
theorem finishCount_work_le (base off cap : ℕ) (bits : List ℕ) (e : List ℕ) {A N : ℕ}
    (hN : 10*bits.length+4 ≤ N) (hb : ∀ b ∈ bits, off+b ≤ A)
    (hf : ∀ k ≤ cap, Prefix.address base cap cap k ≤ A) :
    work (finishCount base off cap bits) e ≤ (cap+1)*guardCost A N := by
  apply work_loop_le
  intro k hk
  change k < cap+1 at hk
  change (stream (if _ = _ then _ else _)).length ≤ _
  have hflag := hf k (by omega)
  split <;> apply Term.work_guard_le
  · exact ⟨hflag,digitChecks_bounded off bits _ (k::e) hb⟩
  · simp only [Term.implies,Term.nodes,Prefix.nodes_flagTerm,digitChecks_nodes]; omega
  · exact hflag
  · simp [Term.nodes]; omega

private theorem cost_mono {A N N' : ℕ} (h : N ≤ N') : guardCost A N ≤ guardCost A N' := by
  unfold guardCost; gcongr

namespace Gadget

/-- A node cap covering both the occurrence transition test and final reported digits. -/
def nodeCap (M B : ℕ) := 4*factorNodeBound M+19 + (10*B+4)

/-- The scratch square contains every row/candidate address from zero to the final prefix. -/
theorem address_le_square {cap i k : ℕ} (hi : i ≤ cap) (hk : k ≤ cap) :
    Prefix.address 0 cap i k ≤ (cap+1)*(cap+1) := by
  calc
    _ ≤ cap*(cap+1)+cap := by unfold Prefix.address; rw [Nat.zero_add]; gcongr
    _ ≤ _ := by rw [Nat.succ_mul]; omega

/-- All initialization, occurrence transition and final-report guards for one ID. -/
theorem checker_work_le (D : Directory) (id : ℕ) (bits : List ℕ) (e : List ℕ) {M A B : ℕ}
    (h : D.BoxBounds M A) (hlen : bits.length ≤ B) (hbits : ∀ b ∈ bits, b ≤ A) :
    let c := D.visitCount
    let s := (c+1)*(c+1)
    work (checker D id bits) e ≤ (c+2)*((c+1)*guardCost (s+A) (nodeCap M B)) := by
  let c := D.visitCount
  let s := (c+1)*(c+1)
  let n := nodeCap M B
  have hf (i k : ℕ) (hi : i ≤ c) (hk : k ≤ c) : Prefix.address 0 c i k ≤ s+A :=
    (address_le_square hi hk).trans (Nat.le_add_right _ _)
  have h₀ := Prefix.initGen_work_le 0 c (s+A) n e (by dsimp [n,nodeCap]; omega) (fun k hk => hf 0 k (by omega) hk)
  have hs := steps_work_le D c s id e h (fun i hi k hk => hf i k hi hk)
  have hn : 4*factorNodeBound M+19 ≤ n := Nat.le_add_right _ _
  have h₁ := hs.trans (Nat.mul_le_mul_left c (Nat.mul_le_mul_left (c+1) (cost_mono hn)))
  have h₂ := finishCount_work_le 0 s c bits e (N := n) (A := s+A)
    (by dsimp [n,nodeCap]; omega) (fun b hb => Nat.add_le_add_left (hbits _ hb) _) (fun k hk => hf c k le_rfl hk)
  simp only [checker,work_seq]
  apply (Nat.add_le_add h₀ (Nat.add_le_add h₁ h₂)).trans
  change _ ≤ (c+2)*((c+1)*guardCost (s+A) n)
  rw [Nat.add_mul c 2, Nat.two_mul]
  omega

/-- Cost per ID, including both loops that allocate and discard the scratch flags. -/
def rowWork (cap M A B : ℕ) :=
  let s := (cap+1)*(cap+1)
  (cap+2)*((cap+1)*guardCost (s+A) (nodeCap M B))+13*s

theorem row_work_le (D : Directory) (id : ℕ) (bits : List ℕ) (e : List ℕ) {M A B : ℕ}
    (h : D.BoxBounds M A) (hlen : bits.length ≤ B) (hbits : ∀ b ∈ bits, b ≤ A) :
    work (row D id bits) e ≤ rowWork D.visitCount M A B := by
  rw [row,work_localFlags]
  exact Nat.add_le_add_right (checker_work_le D id bits e h hlen hbits) _

end Gadget

/-- Sum every reported gadget ID, charging the actual static list and the maximal digit width. -/
theorem Directory.subtotalGuards_work_le (D : Directory) (e : List ℕ) {M A B : ℕ} (h : D.BoxBounds M A)
    (hbits : ∀ bits ∈ D.reportedCounts, bits.length ≤ B ∧ ∀ b ∈ bits, b ≤ A) :
    work D.subtotalGuards e ≤ D.reportedCounts.length*Gadget.rowWork D.visitCount M A B := by
  rw [subtotalGuards,work_sequence,List.map_map]
  apply (sum_map_le D.reportedCounts.zipIdx _ _ ?_).trans_eq (by rw [List.length_zipIdx])
  intro z hz
  obtain ⟨hl,ha⟩ := hbits z.1 (List.fst_mem_of_mem_zipIdx hz)
  exact Gadget.row_work_le D z.2 z.1 e h hl ha

/-- A fixed degree-eight work bound allowing cubic physical bank addresses. -/
theorem Directory.subtotalGuards_work_polynomial (D : Directory) (e : List ℕ) {M A : ℕ}
    (h : D.BoxBounds M A) (hc : D.visitCount ≤ M) (hr : D.reportedCounts.length ≤ M) (ha : A ≤ 4*(M+1)^3)
    (hbits : ∀ bits ∈ D.reportedCounts, bits.length ≤ M ∧ ∀ b ∈ bits, b ≤ A) :
    work D.subtotalGuards e ≤ 5000*(M+2)^8 := by
  apply (D.subtotalGuards_work_le e h hbits).trans
  calc
    _ ≤ M*Gadget.rowWork M M (4*(M+1)^3) M := by dsimp [Gadget.rowWork,guardCost]; gcongr
    _ ≤ _ := by
      unfold Gadget.rowWork Gadget.nodeCap guardCost factorNodeBound
      nlinarith only [Nat.zero_le M, Nat.zero_le (M^2), Nat.zero_le (M^3), Nat.zero_le (M^4),
        Nat.zero_le (M^5), Nat.zero_le (M^6), Nat.zero_le (M^7), Nat.zero_le (M^8)]

/-- Private bytecode interpreter clock for every announced gadget subtotal combined. -/
theorem Directory.subtotalGuards_budget_polynomial (D : Directory) (e : List ℕ) {M A : ℕ}
    (h : D.BoxBounds M A) (hc : D.visitCount ≤ M) (hr : D.reportedCounts.length ≤ M) (ha : A ≤ 4*(M+1)^3)
    (hbits : ∀ bits ∈ D.reportedCounts, bits.length ≤ M ∧ ∀ b ∈ bits, b ≤ A) :
    budget (D.subtotalGuards.expand e) ≤ 25000*(M+2)^8+2 := by
  apply (budget_le _).trans
  change 5*work D.subtotalGuards e+2 ≤ _
  rw [show 25000 = 5*5000 by decide, Nat.mul_assoc]
  gcongr
  exact D.subtotalGuards_work_polynomial e h hc hr ha hbits

end CellSparse

end BorderVNP
end Computability
end OAI
