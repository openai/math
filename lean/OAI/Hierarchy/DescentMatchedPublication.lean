import OAI.Hierarchy.DescentMatchedPairGraph
import OAI.Hierarchy.DescentMatchedPairSweep
import OAI.Hierarchy.DescentPackingBalanceWords
import OAI.Hierarchy.DescentMatchedTableOrder

namespace OAI
/-! # Actual native color-pair records in the complete final nine-word table -/

namespace Hierarchy.DescentPacking.PairRAM
open Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {D w n : ℕ} {P : Type*} {bits : P→ℕ} (N : Network D P bits)
    {C : Type} [Fintype C] [DecidableEq C] (core : Finset N.Edge) (home : N.Site→C)
    (color : N.Site→Bool) (B : ℕ)
local notation "T" => nativeTraffic N core home
local notation "packAt" => fun c=>slabPacking T B (thinList home color c) (thickList home color c)
local notation "mass" => amount (live T)

/-- The table number used by the successor's six atom refs and venue resolver. -/
def globalNumber :=
  tableNumber mass (fun c=>(packAt c).decisions)

def groupStart (c : C) :=
  ProtocolRAMPortRanks.«prefix» (fun d=>Fintype.card (Pairs mass (packAt d).decisions))
    (fun v=>(Fintype.equivFin C v).val) c

theorem group_order (c : C) (e : Pairs mass (packAt c).decisions) :
    (globalNumber N core home color B ⟨c,e⟩).val=
      groupStart N core home color B c+(pairNumber mass (packAt c).decisions e).val := rfl

/-- The machine scans a dimensioned schedule. All geometric data and branch
profiles are read from the pre-stage memory, while the structural interpretation
of each accepted unit uses its actual parent edge in the network. -/
theorem published (rank : C↪ℕ) (src : ℕ→Inputs) (z dest dead scratch t count : ℕ) (m : Memory w)
    (space : ∀i,t≤ i→i<t+count→Space w n (src i) (Fintype.card C) dest dead scratch m)
    (sort : ordered src (Fintype.card C) t count m) (a : ℕ) (first : t≤a) (last : a<t+count)
    (c : C) (e : Pairs mass (packAt c).decisions) (edge : N.Edge→ℕ) (site : N.Site→ℕ)
    (h : Contents) (source : OriginalRows N core home color B c h edge site)
    (read : Loaded (src a) h m) (pos : Position N core home color B c h e (groupStartBy N core home color B rank c))
    (chosen : h.choice=(Fintype.equivFin C e.1).val)
    (inWord : h.need=mass ((packAt c).decisions.get e.2.1.val).1) (size : h.need≤n)
    (indices : InRange (src a) h e.2.2.val) (f : Fin 9) :
    let i := (globalNumberBy N core home color B rank ⟨c,e⟩).val
    output n src z (Fintype.card C) dest dead scratch t count m (dest+9*i+f.val)=
      (actual N core home color B c edge site i z (h.profile i) e f:Word w) := by
  have accept := read.choice.trans chosen
  have less := e.2.2.isLt
  let q : Fin n := ⟨e.2.2.val,(less.trans_eq inWord.symm).trans_le size⟩
  have store := sweep_read (z:=z) src t count m space sort a first last f q
    (accept.trans_lt (Fintype.equivFin C e.1).isLt) (by rw [read.amount,inWord];exact less)
  have loc := space a first last
  have cols := field_values (z:=z) loc.toEarly read e.2.2.val indices f
  have eqn := actual_values N core home color B c source e pos z f
  have index : (m (src a).acceptedBefore).val+q.val=(globalNumberBy N core home color B rank ⟨c,e⟩).val := by
    rw [read.dense,pos.dense,group_order_by,pairNumber_prefix,Nat.add_assoc]
  rw [index] at store
  exact store.trans (cols.trans (congrArg (fun x : ℕ=>(x:Word w)) eqn))

end
end Hierarchy.DescentPacking.PairRAM

end OAI
