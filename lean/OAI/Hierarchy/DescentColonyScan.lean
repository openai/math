import OAI.Hierarchy.DescentColonies
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Buffered finite evaluator for every propagated dyadic split -/

namespace Hierarchy.DescentColonies.Scan
open scoped BigOperators Classical
noncomputable section
variable {k : ℕ} {V : Type*}

private theorem mass_same (load : V → Block k → ℕ) (v : V) {d : ℕ} {x y : Block k}
    (eq : group d x=group d y) : mass load v d x=mass load v d y := by
  simp [mass,interval,eq]

/-- A mark lies in the interval of a heavy node, or is inherited from the
next own layer or the D-th subsequent layer at an actual incoming site. -/
theorem split_cases (load : V → Block k → ℕ) (adj : V → V → Prop) (D cap : ℕ)
    (v : V) (d : ℕ) (x : Block k) :
    Split load adj D cap v d x ↔ cap<mass load v d x ∨
      (∃ y,group d y=group d x ∧ Split load adj D cap v (d+1) y) ∨
      (∃ w,adj w v ∧ ∃ y,group d y=group d x ∧ Split load adj D cap w (d+D) y) := by
  constructor
  · intro sp
    induction sp with
    | heavy h => exact .inl h
    | parent h _ => exact .inr (.inl ⟨_,rfl,h⟩)
    | neighbor edge h _ => exact .inr (.inr ⟨_,edge,_,rfl,h⟩)
    | @same v d x y eq _ ih =>
      rcases ih with h | ⟨z,grouped,yes⟩ | ⟨w,edge,z,grouped,yes⟩
      · exact .inl ((mass_same load v eq) ▸ h)
      · exact .inr (.inl ⟨z,grouped.trans eq,yes⟩)
      · exact .inr (.inr ⟨w,edge,z,grouped.trans eq,yes⟩)
  · rintro (h | ⟨y,eq,h⟩ | ⟨w,edge,y,eq,h⟩)
    · exact .heavy h
    · exact .same eq (.parent h)
    · exact .same eq (.neighbor edge h)

private def anyBlock (f : Block k → Bool) := (List.ofFn f).any id

private theorem anyBlock_spec (f : Block k → Bool) : anyBlock f=true ↔ ∃ y,f y=true := by
  simp [anyBlock,List.mem_ofFn]

/-- Two actual sequences of cache reads per site and block: one's own
deeper row, then one row at each incoming neighbor. -/
def readRows (incoming : V → List V) (get : ℕ → V → Block k → Bool) (D d : ℕ)
    (v : V) (x : Block k) : List Bool :=
  let found := fun e w => anyBlock (fun y => decide (group d y=group d x) && get e w y)
  found (d+1) v :: (incoming v).map (found (d+D))

def readWeights (load : V → Block k → ℕ) (d : ℕ) (v : V) (x : Block k) :=
  List.ofFn (fun y => if group d y=group d x then load v y else 0)

theorem weight_sum (load : V → Block k → ℕ) (d : ℕ) (v : V) (x : Block k) :
    (readWeights load d v x).sum=mass load v d x := by
  rw [readWeights,List.sum_ofFn,mass,interval,Finset.sum_filter]

def rowValue (incoming : V → List V) (load : V → Block k → ℕ)
    (get : ℕ → V → Block k → Bool) (D cap d : ℕ) (v : V) (x : Block k) : Bool :=
  decide (cap<(readWeights load d v x).sum) || (readRows incoming get D d v x).any id

theorem rowValue_spec (incoming : V → List V) (load : V → Block k → ℕ)
    (get : ℕ → V → Block k → Bool) (D cap d : ℕ) (v : V) (x : Block k) :
    rowValue incoming load get D cap d v x=true ↔ cap<mass load v d x ∨
      (∃ y, group d y=group d x ∧ get (d+1) v y=true) ∨
      (∃ w,w∈incoming v ∧ ∃ y,group d y=group d x ∧ get (d+D) w y=true) := by
  simp [rowValue,weight_sum,readRows,List.any_cons,List.any_map,anyBlock_spec,List.any_eq_true]

/-- A level is an array of site rows, each of which is a packed vector of all
block bits. The order enumerating sites is shared with its load/adjacency arrays. -/
abbrev Level (V : Type*) [Fintype V] (k : ℕ) := Vector (Vector Bool (2^k)) (Fintype.card V)

variable [Fintype V]

private def makeLevel (label : V → Block k → Bool) : Level V k :=
  Vector.ofFn (fun i => Vector.ofFn (label ((Fintype.equivFin V).symm i)))

private def readLevel (t : Level V k) (v : V) (x : Block k) : Bool :=
  (t[(Fintype.equivFin V v).val])[x.val]

private theorem read_makeLevel (label : V → Block k → Bool) (v : V) (x : Block k) :
    readLevel (makeLevel label) v x=label v x := by
  simp only [readLevel,makeLevel,Vector.getElem_ofFn,Fin.eta,Equiv.symm_apply_apply]

abbrev Buffer (V : Type*) [Fintype V] (k : ℕ) := List (ℕ × Level V k)

def lookup : Buffer V k → ℕ → V → Block k → Bool
  | [], _, _, _ => false
  | (d,t)::rows, wanted, v, x =>
    if wanted=d then readLevel t v x else lookup rows wanted v x

/-- Construct all rows in descending depth and reuse the already-materialized
deeper layers at every cell in the newly tabulated row. -/
def build (incoming : V → List V) (load : V → Block k → ℕ) (D cap : ℕ) : ℕ → Buffer V k
  | 0 => []
  | s+1 =>
    let rows := build incoming load D cap s
    let d := k-(s+1)
    (d,makeLevel (rowValue incoming load (lookup rows) D cap d)) :: rows

theorem lookup_build_succ (incoming : V → List V) (load : V → Block k → ℕ)
    (D cap s d : ℕ) (v : V) (x : Block k) :
    lookup (build incoming load D cap (s+1)) d v x =
    if d=k-(s+1) then rowValue incoming load (lookup (build incoming load D cap s)) D cap (k-(s+1)) v x
    else lookup (build incoming load D cap s) d v x := by
  simp [build,lookup,read_makeLevel]

theorem build_length (incoming : V → List V) (load : V → Block k → ℕ) (D cap s : ℕ) :
    (build incoming load D cap s).length=s := by
  induction s with
  | zero => rfl
  | succ s ih => simp [build,ih]

private theorem build_read (incoming : V → List V) (adj : V → V → Prop)
    (incoming_spec : ∀w v,w∈incoming v ↔ adj w v) (load : V → Block k → ℕ)
    {D cap : ℕ} (hD : 0<D) (limit : ∀v x,load v x≤cap) (s : ℕ) (sk : s≤k)
    (d : ℕ) (inRange : k-s≤d) (v : V) (x : Block k) :
    lookup (build incoming load D cap s) d v x=true ↔ Split load adj D cap v d x := by
  induction s generalizing d v x with
  | zero =>
    simp only [build,lookup,Bool.false_eq_true,false_iff]
    intro h
    have shallow := split_shallow load adj D 0 cap (by simpa using limit) (by simpa using h)
    omega
  | succ s ih =>
    by_cases now : d=k-(s+1)
    · simp only [build,lookup,ite_eq_left now,read_makeLevel]
      rw [rowValue_spec,split_cases]
      subst d
      have parent (w : V) (y : Block k) := ih (by omega) (k-(s+1)+1) (by omega) w y
      have neighbor (w : V) (y : Block k) := ih (by omega) (k-(s+1)+D) (by omega) w y
      simp_rw [parent,neighbor,incoming_spec]
    · simp only [build,lookup,ite_eq_right now]
      exact ih (by omega) d (by omega) v x

theorem lookup_split (incoming : V → List V) (adj : V → V → Prop)
    (incoming_spec : ∀w v,w∈incoming v ↔ adj w v) (load : V → Block k → ℕ)
    {D cap : ℕ} (hD : 0<D) (limit : ∀v x,load v x≤cap) (d : ℕ) (v : V) (x : Block k) :
    lookup (build incoming load D cap k) d v x=true ↔ Split load adj D cap v d x :=
  build_read incoming adj incoming_spec load hD limit k le_rfl d (by omega) v x

/-- Number of stored Boolean cells, counted from the materialized depth buffers. -/
theorem stored_bits (incoming : V → List V) (load : V → Block k → ℕ) (D cap : ℕ) :
    (build incoming load D cap k).length*Fintype.card V*2^k=k*Fintype.card V*2^k := by
  rw [build_length]

/-- An upper bound counting every list lane before short circuiting. Each
buffer cell scans the raw weights and the one own and all incoming deeper
site rows. Every lookup compares at most k stored depth keys. -/
def cellReads (incoming : V → List V) (v : V) : ℕ := (2+(incoming v).length)*2^k

omit [Fintype V] in
theorem cellReads_eq (incoming : V → List V) (load : V → Block k → ℕ)
    (get : ℕ → V → Block k → Bool) (D d : ℕ) (v : V) (x : Block k) :
    (readWeights load d v x).length + (readRows incoming get D d v x).length * 2^k =
      cellReads (k:=k) incoming v := by
  simp [readWeights,readRows,cellReads]; ring

def lookupProbes : Buffer V k → ℕ → ℕ
  | [],_ => 0
  | (d,_)::rs,wanted => if wanted=d then 1 else 1+lookupProbes rs wanted

theorem lookupProbes_le (rows : Buffer V k) (wanted : ℕ) : lookupProbes rows wanted≤rows.length := by
  induction rows with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨d,t⟩
    by_cases eq : wanted=d <;> simp [lookupProbes,eq]; omega

def readBudget (incoming : V → List V) (s : ℕ) : ℕ :=
  s*∑ v,∑ _x : Block k,cellReads (k:=k) incoming v

theorem scan_cost (incoming : V → List V) (Δ : ℕ) (degree : ∀v,(incoming v).length≤Δ) :
    readBudget (k:=k) incoming k≤Fintype.card V*k*(2+Δ)*(2^k)^2 := by
  unfold readBudget
  have bound (v : V) : (∑ _x : Block k,cellReads (k:=k) incoming v)≤2^k*((2+Δ)*2^k) := by
    simpa [cellReads,Block] using degree v
  calc
    _ ≤ k * ∑ _v : V, 2^k*((2+Δ)*2^k) := Nat.mul_le_mul_left k (Finset.sum_le_sum (fun v _ => bound v))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul];ring

end
end Hierarchy.DescentColonies.Scan

end OAI
