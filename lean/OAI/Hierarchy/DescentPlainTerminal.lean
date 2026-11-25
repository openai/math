import OAI.Hierarchy.DescentFineRows
import OAI.Hierarchy.DescentColonyLoads

namespace OAI
/-! # The original-host numeric fields of every selected reset endpoint -/

namespace Hierarchy.DescentPlainTerminal
open DescentColonies DescentGL DescentFineTerminals DescentContacts
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k : ℕ}

def fields {Y : ℕ} (z : Endpoint Y) : (ℕ×ℕ)×Option ℕ := (z.1,z.2.map Fin.val)

def baseSum (b : V→ℕ) (L : Layout k) (weight : V→Block k→ℕ) (v : V) (x : Block k) :=
  ∑i∈Finset.univ.filter (fun i : Block k=>i<x ∧
    group (b v) (rearrange L i)=group (b v) (rearrange L x)),weight v i

def leafSum (b : V→ℕ) (near : V→Finset V) (raw : V→Block k→ℕ) (f D B : ℕ)
    (safe : ∀v x,raw v x≤B) (v : V) (x : Block k) :=
  let groupAt:=leafKey (D:=D) (f:=f) near raw safe b v
  ∑y∈Finset.univ.filter (fun y : Block k=>y<x ∧ groupAt y=groupAt x),raw v y

/-- A hub carries one stack. At a nonhub v, the selected true exceptional
flag determines which cumulative table supplies the input row. -/
def endpoint (near : V→Finset V) (b : V→ℕ) (L : Layout k) (weight : V→Block k→ℕ)
    (f D B g Y : ℕ) (room : ∀v x,weight v x≤B) (bad : V→ℕ→Prop)
    (hub : V→Bool) (v : V) (x : Block k) : (ℕ×ℕ)×Option ℕ :=
  let y:=rearrange L x
  let raw:=rearrangedLoad weight L
  let safe (v) (i) : raw v i≤B := room v _
  if hub v then ((k-g,group (k-g) y),none) else
    let code:=leafKey (D:=D) (f:=f) near raw safe b v y
    let mass:=if bad v (group (b v) y) then leafSum b near raw f D B safe v y else baseSum b L weight v x
    (code,some (min (Y*mass/(2*(2^f*B))) (Y-1)))

end
end Hierarchy.DescentPlainTerminal

end OAI
