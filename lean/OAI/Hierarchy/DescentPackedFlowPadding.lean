import OAI.Hierarchy.DescentPackedFlowStage
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Prefix-padded numeric neighbor IDs and the genuine reverse-pair sum -/
namespace Hierarchy.DescentPackedFlowPair.Padded
open DescentSIMDLookup DescentPackedFlowReturn
open scoped Classical BigOperators
noncomputable section
variable {H N n r R D d : ℕ}

def project (n : ℕ) (i : Fin N) : Option (Fin n) := if inRange:i.val<n then some ⟨i.val,inRange⟩ else none

@[simp] theorem project_cast (pad : n≤N) (i : Fin n) : project n (i.castLE pad)=some i := by simp [project,i.isLt]

theorem project_some {i : Fin N} {j : Fin n} (ok : project n i=some j) (pad : n≤N) : i=j.castLE pad := by
  unfold project at ok
  split at ok
  · cases ok;rfl
  · contradiction

theorem sum_project (pad : n≤N) (f : Fin n→ℕ) : ∑j : Fin N,(project n j).elim 0 f=∑i : Fin n,f i := by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le pad
  rw [Fin.sum_univ_add]
  have left (i : Fin n) : (project n (i.castAdd t)).elim 0 f=f i := by simp [project,i.isLt]
  have right (i : Fin t) : (project n (Fin.natAdd n i)).elim 0 f=0 := by
    simp [project,show ¬n+i.val<n by omega]
  simp [left,right]

def next (ph : H≤N) (src : Fin H→Fin d→Option (Fin H)) (v : Fin N) (i : Fin D) : Option (Fin N) :=
  (project H v).bind fun u=>(project d i).bind fun j=>(src u j).map (Fin.castLE ph)

def cells (src : Fin H→Fin R→Fin d→Fin r→ℕ) (v : Fin N) (g : Fin R) (j : Fin D) (x : Fin r) :=
  (project H v).elim 0 (fun u=>(project d j).elim 0 (fun t=>src u g t x))

theorem back_live (ph : H≤N) (pd : d≤D) (src : Fin H→Fin d→Option (Fin H))
    (v : Fin H) (i j : Fin d) :
    back (next ph src) (v.castLE ph) (i.castLE pd) (j.castLE pd)=(back src v i j).map (Fin.castLE ph) := by
  simp only [back,next,project_cast,Option.bind_some]
  cases first : src v i with
  | none=>rfl
  | some z=>
    simp only [Option.map_some,Option.bind_some,project_cast]
    cases second : src z j with
    | none=>simp
    | some u=>
      by_cases eq : u=v
      · subst u; simp
      · have different : u.val≠v.val := fun same=>eq (Fin.ext same)
        simp [Fin.ext_iff,different]

theorem paid_live (ph : H≤N) (pd : d≤D) (src : Fin H→Fin d→Option (Fin H))
    (X : Fin H→Fin R→Fin d→Fin r→ℕ) (v : Fin H) (g : Fin R) (i : Fin d) (x : Fin r) :
    paid (next ph src) (cells X) (v.castLE ph) g (i.castLE pd) x=paid src X v g i x := by
  unfold paid
  simp only [cells,project_cast,Option.elim_some]
  congr 1
  rw [←sum_project pd (fun j=>(back src v i j).elim 0 (fun z=>X z g j x))]
  apply Finset.sum_congr rfl
  intro t _
  cases found : project d t with
  | none=>
    simp only [Option.elim_none]
    cases z:back (next ph src) (v.castLE ph) (i.castLE pd) t with
    | none=>rfl
    | some u=>cases atHost:project H u <;> simp [atHost]
  | some j=>
    have same:=project_some found pd
    subst t
    rw [back_live]
    cases z:back src v i j <;> simp [project_cast,z]

theorem paid_at_ghost (ph : H≤N) (_pd : d≤D) (src : Fin H→Fin d→Option (Fin H))
    (X : Fin H→Fin R→Fin d→Fin r→ℕ) (v : Fin N) (g : Fin R) (j : Fin D) (x : Fin r)
    (missing : project H v=none ∨ project d j=none) :
    paid (next ph src) (cells X) v g j x=0 := by
  have ghost : next ph src v j=none := by
    rcases missing with a|a
    · simp [next,a]
    · cases z:project H v <;> simp [next,z,a]
  have empty:cells X v g j x=0 := by
    rcases missing with a|a
    · simp [cells,a]
    · cases z:project H v <;> simp [cells,z,a]
  simp [paid,empty,back,ghost]

end
end Hierarchy.DescentPackedFlowPair.Padded

end OAI
