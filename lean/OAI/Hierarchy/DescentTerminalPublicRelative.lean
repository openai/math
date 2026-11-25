import OAI.Hierarchy.DescentTerminalCableSlots
import OAI.Hierarchy.DescentTerminalExteriorPackets
import OAI.Hierarchy.DescentTerminalGraphPurchase

namespace OAI
/-! # The exact public operand slot inside its receiving home after stable packet sorting -/
namespace Hierarchy.DescentTerminalExteriorPackets
open DescentTerminalCableOrder DescentTerminalGraphPositions DescentTerminalPorts
open Computability.BorderVNP.FragmentBucket Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
variable {P : Type} [Fintype P] {n Q H : ℕ} (rows : P ≃ Fin n × Fin Q) (owner : Fin n → Fin H)

omit [Fintype P] in
private theorem code_same_home (f z : P) (atHome : owner (rows f).1=owner (rows z).1) :
    code rows owner f < code rows owner z ↔
      (rows f).1 < (rows z).1 ∨ ((rows f).1=(rows z).1 ∧ (rows f).2 < (rows z).2) := by
  rw [code_val,code_val,digit_lt (rows f).2.isLt (rows z).2.isLt,ProtocolRAMPortRanks.dest_lt_iff,
    ProtocolRAMPortRanks.bySite_lt_iff]
  have eqn : (dest owner (rows f).1).val=(dest owner (rows z).1).val ↔ (rows f).1=(rows z).1 := by
    constructor
    · intro eq
      exact (dest owner).injective (Fin.ext eq)
    · exact fun e=>congrArg (fun x=>(dest owner x).val) e
  simp only [atHome,lt_self_iff_false,true_and,false_or,eqn]
  rfl

private theorem lane_count (z : Fin n × Fin Q) (a : Fin n) :
    (∑ b : Fin Q, if owner a=owner z.1 ∧ (a<z.1 ∨ (a=z.1 ∧ b<z.2)) then 1 else 0) =
      (if owner a=owner z.1 ∧ a<z.1 then Q else 0)+(if a=z.1 then z.2.val else 0) := by
  by_cases same : a=z.1
  · subst a
    simp only [true_and,lt_self_iff_false,false_or,and_false,ite_false,ite_true,zero_add]
    rw [←Finset.sum_filter]
    have eqn : Finset.univ.filter (fun b : Fin Q => b<z.2) = Finset.Iio z.2 := by ext; simp
    simp [eqn,Fin.card_Iio]
  · by_cases earlier : owner a=owner z.1 ∧ a<z.1
    · simp [same,earlier.1,earlier.2]
    · simp [same,earlier]

theorem local_pin_count (z : P) :
    (Finset.univ.filter (fun f => owner (rows f).1=owner (rows z).1 ∧ code rows owner f<code rows owner z)).card =
      prior owner (rows z).1.val (owner (rows z).1)*Q+(rows z).2.val := by
  let before : P → Prop := fun f =>
    owner (rows f).1=owner (rows z).1 ∧ ((rows f).1<(rows z).1 ∨ ((rows f).1=(rows z).1 ∧ (rows f).2<(rows z).2))
  have eqn : Finset.univ.filter (fun f=>owner (rows f).1=owner (rows z).1 ∧ code rows owner f<code rows owner z) =
      Finset.univ.filter before := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,before]
    exact and_congr_right (fun same => code_same_home rows owner f z same)
  have indicator : (Finset.univ.filter before).card =
      ∑ _a ∈ Finset.univ.filter before,(1:ℕ) := by simp
  rw [eqn,indicator,Finset.sum_filter,←rows.symm.sum_comp,Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  simp_rw [lane_count owner (rows z)]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  congr 1
  have count : (Finset.univ.filter (fun a : Fin n =>
      owner a = owner (rows z).1 ∧ a < (rows z).1)).card =
      prior owner (rows z).1.val (owner (rows z).1) := by
    apply congrArg Finset.card
    ext a
    simp only [Computability.BorderVNP.Crossing.Profile.positions,Finset.mem_filter,Finset.mem_univ,true_and,
      Fin.lt_def]
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,count]; simp

variable {D p : ℕ} {bits : P→ℕ} (N : Network D P bits) (home : N.Site → Fin H)
    (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (nodes : N.Site ↪ ℕ)
    (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
local notation "ext" => code rows owner
local notation "L" => order N home native p ext nodes ops

theorem inGroup_public_slot (hp : 0<p) (firstWidth : ℕ) (divides : p∣firstWidth)
    (width : ∀z,bits z=firstWidth) (homes : ∀z,home (N.attach z)=owner (rows z).1)
    (i : Fin H) (g : Order.Group L i) (external : g.val=none)
    (nm : Order.At L i g) (z : P) (k : Fin (poolBatchCount (bits z) p)) (label : nm.val=.inr ⟨z,k⟩) :
    (Order.inGroup L i g nm).val =
      (prior owner (rows z).1.val i * Q + (rows z).2.val)*(firstWidth/p)+k.val := by
  have used : Order.Used L i (.inr ⟨z,k⟩) := label ▸ nm.2.1
  have which : owner (rows z).1=i := (homes z).symm.trans ((Order.used_port L i z k).mp used)
  have split : poolBatchCount firstWidth p=firstWidth/p := by
    have packed := DescentTerminalGraphVolume.exact_pieces p firstWidth hp divides
    exact (Nat.mul_div_cancel _ hp).symm.trans (congrArg (fun x=>x/p) packed)
  rw [exterior_local_ordinal N home native ext nodes ops i g external nm z k label]
  simp_rw [width,split,homes,←which]
  rw [Finset.sum_const,nsmul_eq_mul,local_pin_count]
  simp

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
