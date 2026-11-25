import OAI.Hierarchy.DescentColonyScanLeaves

namespace OAI
/-! # Executable colony scoring on addressed finite site arrays -/

namespace Hierarchy.DescentColonies.Scan.FinRows
open scoped BigOperators
variable {H k : ℕ}

abbrev Packed (H k : ℕ) := Vector (Vector Bool (2^k)) H
abbrev Layers (H k : ℕ) := List (ℕ × Packed H k)

def read : Layers H k → ℕ → Fin H → Block k → Bool
  | [], _, _, _ => false
  | (d,t)::rs, j, v, x => if j=d then (t[v.val])[x.val] else read rs j v x

private def key (d : ℕ) (x : Block k) := x.val/2^(k-d)

private def value (incoming : Fin H → List (Fin H)) (load : Fin H → Block k → ℕ)
    (get : ℕ → Fin H → Block k → Bool) (D cap d : ℕ) (v : Fin H) (x : Block k) :=
  let data := List.ofFn (fun y : Block k => if key d y=key d x then load v y else 0)
  let marked := fun z (w : Fin H) => (List.ofFn (fun y : Block k =>
    decide (key d y=key d x) && get z w y)).any id
  decide (cap<data.sum) || (marked (d+1) v :: (incoming v).map (marked (d+D))).any id

private theorem value_spec (incoming : Fin H → List (Fin H)) (load : Fin H → Block k → ℕ)
    (get : ℕ → Fin H → Block k → Bool) (D cap d : ℕ) (v : Fin H) (x : Block k) :
    value incoming load get D cap d v x=Scan.rowValue incoming load get D cap d v x := rfl

def tabulate (incoming : Fin H → List (Fin H)) (load : Fin H → Block k → ℕ)
    (D cap : ℕ) : ℕ → Layers H k
  | 0 => []
  | s+1 =>
    let rows := tabulate incoming load D cap s
    let d := k-(s+1)
    (d,Vector.ofFn (fun v => Vector.ofFn (value incoming load (read rows) D cap d v))) :: rows

private theorem read_spec (incoming : Fin H → List (Fin H)) (load : Fin H → Block k → ℕ)
    (D cap s : ℕ) (d : ℕ) (v : Fin H) (x : Block k) :
    read (tabulate incoming load D cap s) d v x =
      Scan.lookup (Scan.build incoming load D cap s) d v x := by
  induction s generalizing d v x with
  | zero => rfl
  | succ s ih =>
    rw [Scan.lookup_build_succ]
    simp only [tabulate,read,Vector.getElem_ofFn,Fin.eta,value_spec]
    rw [show read (tabulate incoming load D cap s) = Scan.lookup (Scan.build incoming load D cap s) from
      funext fun d => funext fun v => funext fun x => ih d v x]

/-- Materialize the entire layer buffer once, then scan site IDs in their
actual integer order. Every operation on weights, depths, block IDs, and
neighbor lists is executable, including duplicate removal within each row. -/
def score (incoming : Fin H → List (Fin H)) (load : Fin H → Block k → ℕ) (D cap : ℕ) : ℕ :=
  let rows := tabulate incoming load D cap k
  let atSite := fun v : Fin H =>
    let ids := List.ofFn (fun x : Block k =>
      let d := (Scan.seek (fun d=>read rows d v x) k 0).1
      (d,key d x))
    (Scan.uniqueIDs ids).1
  (List.ofFn atSite).sum

theorem score_eq_leafScore (incoming : Fin H → List (Fin H)) (load : Fin H → Block k → ℕ)
    (D cap : ℕ) : score incoming load D cap = Scan.leafScore incoming load D cap := by
  simp only [score,List.sum_ofFn,Scan.leafScore,Scan.keyList,Scan.leafDepth,read_spec]; rfl

end Hierarchy.DescentColonies.Scan.FinRows

end OAI
