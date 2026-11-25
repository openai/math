import OAI.ThreeFlat.Diagonal.HistoryReplayCost

namespace OAI
/-! # Tape allocation for the actual ordered history tree

The addresses of a node's immediate child streams, the newly produced
stream, its map table, and its task/node record are all computed from prefix
sums over the immediate children. Parent writes occur after all child rows.
-/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree

open scoped BigOperators

variable {F : Type*} {p : ℕ}

/-- The charge accounts separately for a freshly allocated row-stream word,
a stored map pointer, one fixed-size node, and one fixed-size command. -/
structure Counts where
  streams : ℕ
  pins : ℕ
  records : ℕ
  tasks : ℕ
  deriving DecidableEq

def Counts.prefix {n : ℕ} (C : Fin n → Counts) (j : Fin n) : Counts :=
  ⟨∑ i : Fin j.val, (C (Fin.castLE j.isLt.le i)).streams,
   ∑ i : Fin j.val, (C (Fin.castLE j.isLt.le i)).pins,
   ∑ i : Fin j.val, (C (Fin.castLE j.isLt.le i)).records,
   ∑ i : Fin j.val, (C (Fin.castLE j.isLt.le i)).tasks⟩

def footprint : {p : ℕ} → Tree F p → Counts
  | _, .atom N => ⟨4*N.cells,0,1,0⟩
  | _, .join _ n arity _ child =>
      ⟨(∑ i, (footprint (child i)).streams)+4*(∑ i, (child i).rows),
       (∑ i, (footprint (child i)).pins)+(∑ i, arity i),
       (∑ i, (footprint (child i)).records)+1,
       (∑ i, (footprint (child i)).tasks)+n⟩

structure Addresses where
  stream : ℕ
  maps : ℕ
  nodes : ℕ
  tasks : ℕ
  deriving DecidableEq

/-- A node occupies four words, a generating relation occupies five words,
and an emitted command occupies seven words on the separate driver tape. -/
def Addresses.after (b : Addresses) (z : Counts) : Addresses :=
  ⟨b.stream+z.streams,b.maps+z.pins,b.nodes+4*z.records,b.tasks+5*z.tasks⟩

def within (b : Addresses) (T : Tree F p) := b.after (footprint T)

def rootStream (b : Addresses) (T : Tree F p) := (within b T).stream-4*T.rows

def rootNode (b : Addresses) (T : Tree F p) := (within b T).nodes-4

def childStart {n : ℕ} {arity : Fin n → ℕ} (b : Addresses) (child : ∀ i, Tree F (arity i)) (i : Fin n) : Addresses :=
  b.after (Counts.prefix (fun i => footprint (child i)) i)

def before {n : ℕ} (x : Fin n → ℕ) (i : Fin n) := ∑ j : Fin i.val, x (Fin.castLE i.isLt.le j)

/-- One postorder relation emitted by the scheduler. It carries only actual
values of the sequential node fields and per-child prefixes. -/
structure Copy where
  childNode : ℕ
  parentNode : ℕ
  map : ℕ
  rowPrefix : ℕ
  bitPrefix : ℕ
  command : ℕ
  source : ℕ
  dest : ℕ
  count : ℕ
  deriving DecidableEq

def copy {h n : ℕ} {arity : Fin n → ℕ} (b : Addresses) (wire : ∀ i, Fin (arity i) → BitSource h p)
    (child : ∀ i, Tree F (arity i)) (i : Fin n) : Copy :=
  let T := Tree.join h n arity wire child
  let start := childStart b child i
  let rows := before (fun z => (child z).rows) i
  ⟨rootNode start (child i),rootNode b T,
   b.maps+(∑ j, (footprint (child j)).pins)+before arity i,
   rows,before (fun z => (child z).bits) i,b.tasks+5*((∑ j, (footprint (child j)).tasks)+i.val),
   rootStream start (child i),rootStream b T+4*rows,4*(child i).rows⟩

def copies : {p : ℕ} → (T : Tree F p) → Addresses → List Copy
  | _, .atom _, _ => []
  | _, .join _ _ _ wire child, b =>
    (List.ofFn fun i => copies (child i) (childStart b child i)).flatten ++ List.ofFn (copy b wire child)

theorem prefix_next_le {n : ℕ} (x : Fin n → ℕ) (i : Fin n) : before x i + x i ≤ ∑ j, x j := by
  let f (v : ℕ) := if pos : v<n then x ⟨v,pos⟩ else 0
  have initial : before x i = ∑ v ∈ Finset.range i.val, f v := by
    rw [before,← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f,dite_eq_left (j.isLt.trans i.isLt)]
    rfl
  have total : (∑ v ∈ Finset.range n, f v) = ∑ j, x j := by
    rw [←Fin.sum_univ_eq_sum_range]
    simp only [f,dite_eq_left (Fin.isLt _)]
  calc
    _ = ∑ z ∈ Finset.range (i.val+1), f z := by rw [Finset.sum_range_succ,initial]; simp [f,i.isLt]
    _ ≤ ∑ z ∈ Finset.range n, f z := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono i.isLt) (by intros; omega)
    _ = _ := total

/-- Two different child copy intervals in the same physical parent stream
are ordered even when some children have no records. -/
theorem before_end_le {n : ℕ} (counts : Fin n→ℕ) {i j : Fin n} (lt : i<j) :
    before counts i+counts i≤before counts j := by
  let values := fun a : Fin j.val => counts (Fin.castLE j.isLt.le a)
  let x : Fin j.val := ⟨i.val,lt⟩
  exact prefix_next_le values x


theorem streams_ge (T : Tree F p) : 4*T.rows ≤ (footprint T).streams := by cases T <;> simp [footprint,rows]

theorem childStream_end {n h : ℕ} {arity : Fin n → ℕ} (b : Addresses)
    (wire : ∀ i, Fin (arity i) → BitSource h p) (child : ∀ i, Tree F (arity i)) (i : Fin n) :
    (copy b wire child i).source+(copy b wire child i).count ≤ rootStream b (.join h n arity wire child) := by
  have hp := prefix_next_le (fun j => (footprint (child j)).streams) i
  have hs := streams_ge (child i)
  simp only [copy,rootStream,within,Addresses.after,childStart,Counts.prefix,footprint,rows,before] at *
  omega

theorem dest_end {n h : ℕ} {arity : Fin n → ℕ} (b : Addresses)
    (wire : ∀ i, Fin (arity i) → BitSource h p) (child : ∀ i, Tree F (arity i)) (i : Fin n) :
    (copy b wire child i).dest+(copy b wire child i).count ≤ (within b (.join h n arity wire child)).stream := by
  have hp := Nat.mul_le_mul_left 4 (prefix_next_le (fun j => (child j).rows) i)
  simp only [copy,rootStream,within,Addresses.after,footprint,rows,Nat.mul_add] at *
  omega

theorem copies_length (T : Tree F p) (b : Addresses) : (copies T b).length = T.commands := by
  induction T generalizing b with
  | atom => rfl
  | join h n a wire child ih =>
    simp only [copies,List.length_append,List.length_flatten,List.map_ofFn,List.length_ofFn,commands]
    simp [Function.comp_def,ih,List.sum_ofFn,Finset.sum_add_distrib]

/-- Actual tape space for all row streams. Each copied row incurs four
more words past its original leaf occurrence. -/
theorem footprint_streams (T : Tree F p) : (footprint T).streams = 4*(T.copiedRows+T.rows) := by
  induction T with
  | atom => simp [footprint,copiedRows,rows]
  | join h n a wire child ih =>
    simp only [footprint,copiedRows,rows,ih,Nat.mul_add,Finset.sum_add_distrib,←Finset.mul_sum]

end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
