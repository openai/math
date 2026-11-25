import OAI.Hierarchy.DescentTerminalGraphPurchase
import OAI.Hierarchy.DescentExteriorTokenLedger
import OAI.Hierarchy.DescentIntegralSiteLoad

namespace OAI
/-! # Site-local terminal arity from the two real cable ledgers -/
namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing DescentResetTrunks DescentTerminalGraphPositions DescentTerminalGraphVolume
open DescentKernelHistory DescentCompiler ThreeFlat.Routing
open scoped BigOperators Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} (W : MarkedWorld F d P bits)

omit [Field F] in
theorem grain_width {p : ℕ} (live : 0<p) (edges : ∀e,p∣W.graph.width e)
    (ports : ∀z,p∣bits z) (v : W.graph.Site) :
    DescentTerminalGraphRows.arity W.graph p v*p=GadgetNetwork.siteLoad W.graph v+W.exteriorWidth v := by
  unfold DescentTerminalGraphRows.arity
  rw [Finset.sum_mul,Fintype.sum_sum_type]
  have first : ∀e:Incident W.graph v,poolBatchCount (W.graph.width e.val) p*p=W.graph.width e.val :=
    fun e=>exact_pieces p _ live (edges e.val)
  have last : ∀z:Attached W.graph v,poolBatchCount (bits z.val) p*p=bits z.val :=
    fun z=>exact_pieces p _ live (ports z.val)
  simp only [DescentTerminalGraphRows.width,Sum.elim_inl,Sum.elim_inr,first,last]
  congr 1
  · unfold GadgetNetwork.siteLoad
    rw [←Finset.sum_filter,Finset.sum_subtype
      (p:=fun e : W.graph.Edge => W.graph.src e=v ∨ W.graph.dst e=v)
      _ (fun _=>by simp) W.graph.width]
  · unfold exteriorWidth bin
    rw [←Finset.sum_filter,Finset.sum_subtype
      (p:=fun z : P => W.graph.attach z=v) _ (fun _=>by simp) bits]

variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {G : PoweredGadget F} {cost ε : ℝ} {k : ℕ} (A : GroupStage W G cost ε J V k)
theorem local_grain {p : ℕ} (unit : A.z=p) (hp : 0<p)
    (edges : ∀e,p∣W.graph.width e) (ports : ∀z,p∣bits z)
    (balance : W.HubExterior (fun z=>A.hub (A.pos z).2))
    (owns : ∀z,A.hub (A.pos (W.graph.attach z)).2=true) (v : W.graph.Site) :
    DescentTerminalGraphRows.arity W.graph p v≤2*(G.b*A.cap) := by
  let flag := fun z : W.graph.Site => A.hub (A.pos z).2
  let T:=W.siteUnits flag A.records A.wire 256 A.hist v
  have upper : T≤A.wire*p*(G.b*A.cap):=by
    simpa only [T,flag,unit,Nat.mul_assoc] using A.site_units_room v
  have inside : A.wire*GadgetNetwork.siteLoad W.graph v≤T:=W.siteUnits_cover flag A.records A.wire 256 A.hist (by decide) v
  have exterior : A.wire*W.exteriorWidth v≤T := by
    cases h:A.hub (A.pos v).2 with
    | false=>
      have zero : W.exteriorWidth v=0 := by
        apply Finset.sum_eq_zero
        intro z _
        apply ite_eq_right
        intro hx
        have oz:=owns z
        rw [hx] at oz
        simp [h] at oz
      simp [zero]
    | true=>
      have empty:=A.noHubAtoms v h
      have scale : T=A.wire*(W.siteUnits flag (fun _=>([] : List Unit)) 1 256 0 v) := by
        simp only [T,siteUnits,empty,Nat.mul_zero,List.length_nil,Nat.add_zero,Nat.one_mul,Nat.mul_add,
          Finset.mul_sum,mul_ite,Nat.mul_zero,Nat.mul_assoc]
      rw [scale,balance v h]
      exact Nat.mul_le_mul_left _ (by omega)
  apply Nat.le_of_mul_le_mul_left _ (Nat.mul_pos A.wirePos hp)
  calc
    _ = A.wire*(DescentTerminalGraphRows.arity W.graph p v*p) := by ring
    _ = A.wire*GadgetNetwork.siteLoad W.graph v+A.wire*W.exteriorWidth v := by rw [W.grain_width hp edges ports,Nat.mul_add]
    _ ≤ T+T := Nat.add_le_add inside exterior
    _ ≤ A.wire*p*(G.b*A.cap)+A.wire*p*(G.b*A.cap) := Nat.add_le_add upper upper
    _ = _ := by ring

end
end Hierarchy.DescentSixParty.MarkedWorld

namespace Hierarchy.DescentTerminalGraphVolume
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions
open scoped BigOperators Classical
noncomputable section
variable {D S p : ℕ} {P : Type} [Fintype P] {bits:P→ℕ} {G:Network D P bits} (L:Order G S p)
theorem home_rows (q V d : ℕ) (alive:0<q) (arity:∀v,DescentTerminalGraphRows.arity G p v≤q)
    (live:∀i,Fintype.card (L.Nodes i)≤V) (neighbors:∀i,(L.site i).groups≤d+1) (i:Fin S) :
    (L.site i).rows q≤3*V+d+3 := by
  have localCap : ∑v,(L.site i).arity v≤V*q := by
    calc
      _ ≤ ∑_ : Fin (Fintype.card (L.Nodes i)),q :=
        Finset.sum_le_sum (fun v _=>arity (L.node i v))
      _ = Fintype.card (L.Nodes i)*q := by simp
      _ ≤ V*q := Nat.mul_le_mul_right q (live i)
  have group:=Nat.mul_le_mul_right q (neighbors i)
  have names:=source_budget L i
  have paid:=(L.site i).rows_bound alive
  apply Nat.le_of_mul_le_mul_right _ alive
  calc _ ≤ (V*q)+(d+1)*q+2*(V*q)+2*q := by omega
       _ = (3*V+d+3)*q := by ring
end
end Hierarchy.DescentTerminalGraphVolume

end OAI
