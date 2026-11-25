import OAI.Computability.BorderVNP.PackedGridLanes
import OAI.Computability.BorderVNP.CellPacketInputSize

/-! # Stored metadata and expanded visits of an initial private cell

The Boolean table at a trivalent site has at most eight rows and three arguments.
A unary source uses one wire address and one external report port. The actual sparse
packet stores the one-copy factors once and the repeated physical box as one record.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse Finset
open scoped Classical
variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable {C : Type} (cell : N.Site → C) (c : C) {m n s : ℕ}
variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable (rules : ∀ v : {v : N.Site // cell v = c}, Rule N v.val)

/-- Bounding the three actual fields of a reported-use port is sufficient for a unary
descriptor. Boolean truth tables have no named report fields. -/
def Rule.reportBound {N : Network D P bits} {v : N.Site} (U : ℕ) : Rule N v → Prop
  | .truth _ => True
  | .unary _ p => p.base ≤ U ∧ p.copyStride ≤ U ∧ p.laneStride ≤ U

/-- At degree three the one-copy comparison matrix has at most `(3+1)*(8+1)` entries. -/
theorem rule_staticMass_le (v : {v : N.Site // cell v = c})
    (order : CellBox.Lane N v.val ≃ Fin (Fintype.card (CellBox.Lane N v.val)))
    (degree : Fintype.card (CellBox.Lane N v.val) ≤ 3) (a : Rule N v.val) :
    (ruleFactor N cell c edgeID portID v order a).staticMass ≤ 36 := by
  cases a with
  | unary => change 1 ≤ 36; decide
  | truth =>
    simp only [ruleFactor,Factor.staticMass,boolRows,List.length_ofFn]
    exact Nat.mul_le_mul (Nat.succ_le_succ degree)
      (Nat.succ_le_succ (Nat.pow_le_pow_right (by decide : 0 < 2) degree))

/-- Every transported field of one stored factor is bounded by the actual cell stride,
the bounds on its report port and the constant eight for table row counts. -/
theorem rule_factorFields (v : {v : N.Site // cell v = c})
    (order : CellBox.Lane N v.val ≃ Fin (Fintype.card (CellBox.Lane N v.val)))
    (degree : Fintype.card (CellBox.Lane N v.val) ≤ 3) {U : ℕ}
    (h8 : 8 ≤ U) (hs : stride N cell c ≤ U) (a : Rule N v.val) (hp : a.reportBound U) :
    Packet.FactorFields (ruleFactor N cell c edgeID portID v order a) U := by
  cases a with
  | unary l p =>
    exact ⟨⟨trivial,(lane N cell c edgeID portID v l).isLt.le.trans hs,hp⟩,trivial⟩
  | truth f =>
    have hr := Nat.pow_le_pow_right (by decide : 0 < 2) degree
    refine ⟨⟨⟨?_,?_⟩,?_⟩,trivial⟩
    · simpa only [List.length_ofFn] using degree.trans (by omega : 3 ≤ U)
    · simpa only [boolRows,List.length_ofFn] using hr.trans h8
    · intro i hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      exact (lane N cell c edgeID portID v (order.symm j)).isLt.le.trans hs

/-- The sole box block has its original base, copy count, full cell stride and stored
factor list. Its expanded visit count is copies times the number of fine sites. -/
theorem directory_blocks (b : ℕ) :
    (directory N cell c siteID edgeID portID rules b).blocks =
      [⟨0,b,stride N cell c,factors N cell c siteID edgeID portID rules⟩] := rfl

/-- Number of expanded visits is exact for every copy count, including zero. -/
theorem directory_visitCount (b : ℕ) :
    (directory N cell c siteID edgeID portID rules b).visitCount =
      b*Fintype.card {v : N.Site // cell v = c} := by
  simp only [Directory.visitCount,directory_blocks,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,Nat.add_zero,factors,List.length_map,siteList_length]

set_option maxRecDepth 8000 in
/-- Static sweep size charges the one-copy factors only; copy repetition remains a
single public record. -/
theorem directory_boxMass (b : ℕ)
    (deg : ∀ v : {v : N.Site // cell v = c}, Fintype.card (CellBox.Lane N v.val) ≤ 3) :
    (directory N cell c siteID edgeID portID rules b).boxMass ≤
      5 + 360001*Fintype.card {v : N.Site // cell v = c} := by
  let vs := siteList N cell c siteID
  let fs := factors N cell c siteID edgeID portID rules
  have hh : (fs.map (fun f => 10000*f.staticMass)).sum ≤ 360000 * vs.length := by
    unfold fs factors
    rw [List.map_map]
    have hi := List.sum_le_sum (l := vs) (g := Function.const _ 360000)
      (fun v _ => Nat.mul_le_mul_left 10000 (rule_staticMass_le N cell c edgeID portID v
        (Fintype.equivFin _) (deg v) (rules v)))
    simp only [List.map_const,List.sum_replicate,nsmul_eq_mul,Nat.cast_id] at hi
    rw [Nat.mul_comm 360000]
    exact hi
  simp only [Directory.boxMass,sweepMass,directory_blocks,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,Nat.add_zero]
  change 4 + fs.length + (fs.map (fun f => 10000*f.staticMass)).sum + 1 ≤ _
  have hf : fs.length = vs.length := List.length_map _
  have hv : vs.length = Fintype.card {v : N.Site // cell v = c} := siteList_length N cell c siteID
  omega

/-- All original natural fields in the serialized directory, including headers of
empty boxes, meet the bound. -/
theorem directory_rawFields (b wires U : ℕ) (h8 : 8 ≤ U) (hb : b ≤ U) (hw : wires ≤ U)
    (hs : stride N cell c ≤ U) (hv : Fintype.card {v : N.Site // cell v = c} ≤ U)
    (deg : ∀ v : {v : N.Site // cell v = c}, Fintype.card (CellBox.Lane N v.val) ≤ 3)
    (hr : ∀ v, (rules v).reportBound U) :
    Packet.RawFields (directory N cell c siteID edgeID portID rules b) wires U := by
  refine ⟨hw,by simp [directory]; omega,?_,?_,?_⟩
  · intro fs hfs
    simp only [directory,List.mem_singleton] at hfs
    subst fs
    refine ⟨by simpa only [factors,List.length_map,siteList_length] using hv,?_⟩
    intro f hf
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hf
    exact rule_factorFields N cell c edgeID portID v (Fintype.equivFin _) (deg v) h8 hs (rules v) (hr v)
  · intro rec hrec
    simp only [directory,List.mem_singleton] at hrec
    subst rec
    exact ⟨trivial,Nat.zero_le _,Nat.zero_le _,hb,hs⟩
  · simp [directory]

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
