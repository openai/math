import OAI.Hierarchy.TaggedWidePrivateOrdinals
import OAI.Hierarchy.TaggedWidePadding
import OAI.Hierarchy.TaggedWideCalendarLeaf

namespace OAI
/-! # Original private catalogue switches and their two low-width padding guards -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage ProbeStage.CoreBoard TaggedShorterZero Computability.VPVNP.BurstRAM
open ThreeFlat Routing Diagonal TraceWords
open Tagged WidePadding WideCalendarSites WideStack WideStack.Leaf
open scoped Classical BigOperators
variable {F : Type*} [Field F] {h W k : ℕ} {S : PurchaseSampler}
    (b : Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    {address wordBits width : ℕ} {V : Type} [Fintype V]
    (fits : siteLast h (2^W) k+1≤2^address) (room : width≤2^wordBits)
    (ep : Fin b.rows→Bool→Fin address→V) (cut : Fin b.rows→Fin wordBits→V)
    (data : Bool→b.Private order→Fin width→V)

local notation "Q" => Bool × (b.Private order × Fin width)
local notation "N" => Fintype.card Q
local notation "read" => (Fintype.equivFin Q).symm
local notation "gates" => fun i : b.Private order=>privateSwitch (F:=F) ((b.freeOrdinal order).symm i) fits room
local notation "eqNet" => WideHost.localFamily gates (b.privatePin order fits ep cut data)

def Board.privatePaddingPorts : Ports (V⊕Bool) N wordBits where
  col i := (read i).2.2.castLE room
  live _ := .inr true
  width i j := .inl (cut (read i).2.1.val j)
  payload i := .inl (data (read i).1 (read i).2.1 (read i).2.2)

local notation "ports" => b.privatePaddingPorts order room cut data

def Board.privatePadding : Net F V :=
  WideHost.localFamily (fun _ : Unit=>(ports).network (F:=F)) (fun _ j=>j)

local notation "pad" => b.privatePadding (F:=F) order room cut data

def Board.privateChecked : Net F V := attach pad eqNet

theorem Board.privatePadding_value (x : V→Bool) (size : Fin b.rows→Word wordBits)
    (word : ∀i j,x (cut i j)=bits (size i) j) :
    TypedWiring.value pad x = if EndsPadded (fun i=>(size i.val).val) (fun _ : b.Private order=>width)
      (fun side i j=>x (data side i j)) then 1 else 0 := by
  rw [Board.privatePadding,WideHost.localFamily_eval,Fintype.prod_unique]
  change TypedWiring.value (ports).network (Sum.elim x id) = _
  rw [(ports).eval (Sum.elim x id) (fun i=>size (read i).2.1.val) (fun i j=>word _ j)]
  congr 1
  apply propext
  constructor
  · intro has side i j high
    cases value : x (data side i j) with
    | false => exact value
    | true =>
      have hit := has (Fintype.equivFin Q (side,i,j))
      simp only [Board.privatePaddingPorts,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,
        id_eq,value,true_implies,Fin.lt_def,Fin.val_castLE] at hit
      change (size i.val).val ≤ j.val at high
      omega
  · intro padded t live
    let q := read t
    have on : x (data q.1 q.2.1 q.2.2)=true := live
    have small : q.2.2.val<(size q.2.1.val).val := by
      by_contra! large
      exact Bool.noConfusion (on.symm.trans (padded q.1 q.2.1 q.2.2 large))
    exact ⟨rfl,small⟩

local notation "names" => fun (f : Free S h (2^W) k) side=>privateNames f fits side 0

/-- Every literal terminal observation is an endpoint, a paid width digit,
or one of the two private common-data pins. -/
theorem Board.privateChecked_value (x : V→Bool) (ends : Fin b.rows→Bool→Word address)
    (size : Fin b.rows→Word wordBits)
    (record : ∀i side j,x (ep i side j)=bits (ends i side) j)
    (word : ∀i j,x (cut i j)=bits (size i) j)
    (printed : ∀i : b.Private order,0<(size i.val).val→
      let f := (b.freeOrdinal order).symm i
      (ends i.val false).val=min (names f false).val (names f true).val ∧
      (ends i.val true).val=max (names f false).val (names f true).val) :
    TypedWiring.value (b.privateChecked (F:=F) order fits room ep cut data) x =
      if EndsPadded (fun i=>(size i.val).val) (fun _ : b.Private order=>width) (fun side i j=>x (data side i j))
      then ∏i : b.Private order,if ∀j : Fin width,j.val<(size i.val).val→
        x (data false i j)=x (data true i j) then 1 else 0 else 0 := by
  rw [Board.privateChecked,attach_value,b.privatePadding_value order room cut data x size word,
    b.private_values order fits room ep cut data x ends size record word printed]
  split_ifs <;> simp_all

theorem Board.privateChecked_cost :
    let net:=b.privateChecked (F:=F) order fits room ep cut data
    net.cells+net.internal ≤ N*(200*wordBits+65)+b.rows*(2+2*(2*(100*address+100)+width*(100*wordBits+100))) := by
  dsimp only
  rw [Board.privateChecked,attach_cost]
  apply Nat.add_le_add _ (b.private_cost (F:=F) order fits room ep cut data)
  rw [Board.privatePadding,WideHost.localFamily_size]
  simpa using (ports).cost (F:=F)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
