import OAI.Hierarchy.DescentHistoryLanes
import OAI.Hierarchy.DescentTerminalPorts
import OAI.Hierarchy.DescentTerminalRecipeRows

namespace OAI
/-! # Real graph reads from the terminal row's ordered bundle arguments -/

namespace Hierarchy.DescentTerminalGraphRows
open Computability.BorderVNP.Crossing DescentKernelHistory DescentTerminalRecipeRows
open ThreeFlat.Routing
open scoped BigOperators Classical
noncomputable section

/-- Clipping applies to the original operand lengths, after a tuple's
final payload slice has been reassembled. Private words retain their exact
width inside the contraction. -/
def clipScalar {Tag F : Type} (scalar : Tag→List (List Bool)→F) (d : Tag×List ℕ)
    (xs : List (List Bool)) := scalar d.1 (List.zipWith List.take d.2 xs)

def clipped {Tag B : Type} (r : Recipe Tag B) (width : B→ℕ) : Recipe (Tag×List ℕ) B :=
  {r with tag := fun v=>(r.tag v,List.ofFn (fun j=>(r.operand v j).elim width r.width))}

private theorem zip_ofFn {A B C : Type} {n : ℕ} (f : A→B→C) (g : Fin n→A) (h : Fin n→B) :
    List.zipWith f (List.ofFn g) (List.ofFn h)=List.ofFn (fun i=>f (g i) (h i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem clipped_value {Tag B F : Type} [CommSemiring F] (r : Recipe Tag B) (width : B→ℕ)
    (scalar : Tag→List (List Bool)→F) (x : B→List Bool) :
    (clipped r width).value (clipScalar scalar) x=r.value scalar (fun b=>(x b).take (width b)) := by
  simp only [Recipe.value,clipped,clipScalar]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro v _
  rw [zip_ofFn]
  congr 2
  funext j
  cases ref : r.operand v j with
  | inl b => simp
  | inr k => simp [wordList]

theorem collect_slices {p n : ℕ} (positive : 0<p) (x : Fin n→Bool) :
    ((List.ofFn (fun i : Fin (poolBatchCount n p)=>List.ofFn (TaggedShorterFields.slice p x i.val))).flatten).take n
      =List.ofFn x := by
  let m := poolBatchCount n p
  let padded : Fin (m*p)→Bool := fun i=> if h : i.val<n then x ⟨i.val,h⟩ else false
  have full : List.ofFn padded=(List.ofFn (fun i : Fin m=>List.ofFn (TaggedShorterFields.slice p x i.val))).flatten := by
    rw [List.ofFn_mul]
    rfl
  rw [←full]
  have lim : n ≤ m*p := by simpa only [m,Nat.mul_comm] using CallPool.count_le_batches_mul n p positive
  apply List.ext_getElem
  · simp [lim]
  · intro i hi hj
    have valid : i<n := by simpa using hj
    simp [padded,valid]

variable {D p : ℕ} {P Tag F : Type} [Fintype P] [CommSemiring F] {bits : P→ℕ}
    (N : Network D P bits) (scalar : Tag→List (List Bool)→F)
    (history : (v : N.Site)→Recipe Tag (Boundary N v))

def width (v : N.Site) : Boundary N v→ℕ := Sum.elim (fun e=>N.width e.1) (fun e=>bits e.1)

/-- Each physical bundle is named by its actual incident/exterior link
and its original within-link chunk ordinal. -/
abbrev Part (p : ℕ) (v : N.Site) := (b : Boundary N v) × Fin (poolBatchCount (width N v b) p)
def arity (p : ℕ) (v : N.Site) := ∑b,poolBatchCount (width N v b) p

def parts (p : ℕ) (v : N.Site) (b : Boundary N v) : List (Part N p v) :=
  List.ofFn (fun j=>⟨b,j⟩)

def number (p : ℕ) (v : N.Site) (rank : Boundary N v ↪ ℕ) : Part N p v ≃ Fin (arity N p v) :=
  ProtocolRAMPortRanks.enumerate _ rank rank.injective

def recipe (p : ℕ) (v : N.Site) (rank : Boundary N v ↪ ℕ) :
    Recipe ((Tag×List ℕ)×List ℕ) (Fin (arity N p v)) :=
  rewire (splitLanes (clipped (history v) (width N v)) (parts N p v)) (number N p v rank)

def word {v : N.Site} (a : N.Assignment) (outer : Ports bits) (b : Boundary N v) : Word (width N v b) :=
  match b with
  | .inl e=>a e.1
  | .inr e=>outer e.1

def readPart (p : ℕ) {v : N.Site} (a : N.Assignment) (outer : Ports bits) (t : Part N p v) : Word p :=
  TaggedShorterFields.slice p (word N a outer t.1) t.2.val

theorem recipe_read (positive : 0<p) (T : N.Tables F) (repr : Represents N scalar T history)
    (v : N.Site) (rank : Boundary N v ↪ ℕ) (a : N.Assignment) (outer : Ports bits) :
    (recipe N history p v rank).value (laneScalar (clipScalar scalar))
      (fun j=>wordList (readPart N p a outer ((number N p v rank).symm j)))=N.read T a outer v := by
  have restore : ((fun j=>wordList (readPart N p a outer ((number N p v rank).symm j))) ∘ (number N p v rank))=
      (fun t:Part N p v=>wordList (readPart N p a outer t)) := by
    funext t
    exact congrArg (fun u=>wordList (readPart N p a outer u)) ((number N p v rank).symm_apply_apply t)
  rw [recipe,rewire_value,restore,splitLanes_value,clipped_value]
  unfold Network.read
  rw [←repr v]
  congr 1
  funext b
  have restored : ((parts N p v b).flatMap (fun t=>wordList (readPart N p a outer t))).take (width N v b)=
      wordList (word N a outer b) := by
    rw [parts,List.flatMap_def,List.map_ofFn]
    exact collect_slices positive (word N a outer b)
  exact restored.trans (by cases b <;> rfl)

end
end Hierarchy.DescentTerminalGraphRows

end OAI
