import OAI.Hierarchy.DescentStageAtoms
import OAI.Hierarchy.DescentHubCoalescence

namespace OAI
/-! # The literal retained record array of a merged hub or an ordinary survivor -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentHostDirectory StarKeys
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] {d : ℕ} {P V Atom : Type} [DecidableEq V] {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (key : W.graph.Site↪Key V) (hub : V→Bool) (k g : ℕ)
variable (rec : W.graph.Site→List Atom)
local notation "addr" => address W key hub k g
local notation "post" => coalesced W key hub k g

def coalescedRecords (v : (post).graph.Site) :=
  gather (fun u : {u : W.graph.Site // addr u=v}=>rec u.val)

theorem coalescedRecords_length (v : (post).graph.Site) :
    (coalescedRecords W key hub k g rec v).length=∑u : {u // addr u=v},(rec u.val).length := gather_length _

omit [Field F] in
theorem address_row (u : W.graph.Site) : (addr u).val.1=(key u).1 := by
  change (mergeHub hub k g (key u)).1=(key u).1
  unfold mergeHub
  split <;> rfl

theorem ordinary_unique (x y : W.graph.Site) (no : hub (key x).1=false) (same : addr x=addr y) :
    x=y := by
  have rowx := address_row W key hub k g x
  have rowy := address_row W key hub k g y
  have common : (key x).1=(key y).1 := rowx.symm.trans ((congrArg (fun z : (post).graph.Site => z.val.1) same).trans rowy)
  have ny : hub (key y).1=false := common ▸ no
  apply key.injective
  have data := congrArg Subtype.val same
  simpa only [address,mergeHub,no,ny,Bool.false_eq_true,ite_false] using data

theorem coalescedRecords_ordinary (x : W.graph.Site) (no : hub (key x).1=false) :
    coalescedRecords W key hub k g rec (addr x)=rec x := by
  let T := {u : W.graph.Site // addr u=addr x}
  let entry : T := ⟨x,rfl⟩
  have only (u : T) : u=entry := Subtype.ext (ordinary_unique W key hub k g x u.val no u.property.symm).symm
  have single (enumeration : Fintype T) : @Finset.univ T enumeration = {entry} := by
    let : Fintype T := enumeration
    ext u
    simpa only [Finset.mem_univ,Finset.mem_singleton,true_iff] using only u
  unfold coalescedRecords gather
  rw [single]
  simp [entry]

theorem coalescedRecords_empty (empty : ∀u,hub (key u).1=true→ rec u=[])
    {v : (post).graph.Site} (yes : hub v.val.1=true) : coalescedRecords W key hub k g rec v=[] := by
  apply List.length_eq_zero_iff.mp
  rw [coalescedRecords_length]
  apply Finset.sum_eq_zero
  intro u _
  apply List.length_eq_zero_iff.mpr
  apply empty
  rw [←address_row W key hub k g u.val,u.property]
  exact yes

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
