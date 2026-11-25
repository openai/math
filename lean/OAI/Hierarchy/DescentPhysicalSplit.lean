import OAI.Hierarchy.DescentSeedTrivalentMenu
import OAI.Hierarchy.DescentAttachmentGraph
import OAI.Computability.BorderVNP.BitVolume
import OAI.Hierarchy.DescentLocalTables
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Replacing each finite binary tensor site by a path of actual tensor sites -/

namespace Hierarchy.DescentPhysicalSplit
open Computability.BorderVNP.Crossing LinearAlgebra.SpectralBooks DescentRotor
open scoped BigOperators Classical
noncomputable section
variable {D : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)

def width : Leg N → ℕ
  | .inl p => bits p
  | .inr (e,_) => N.width e

def index (v : N.Site) : Fibre N v ≃ Fin (count N v) := Fintype.equivFin _
def name (v : N.Site) (i : Fin (count N v)) := ((index N v).symm i).val
def localWidth (v : N.Site) (i : Fin (count N v)) := width N (name N v i)
abbrev Vertex := Σ v : N.Site,Attachment.Site (count N v)
abbrev Spine := Σ v : N.Site,Fin (count N v+1)
abbrev Cable := N.Edge ⊕ Spine N

def tap (p : Leg N) : Vertex N := ⟨owner N p,.inr (index N _ ⟨p,rfl⟩)⟩

@[simp] theorem tap_named (v : N.Site) (i : Fin (count N v)) :
    tap N (name N v i)=⟨v,.inr i⟩ := by
  have atPort (q : Fibre N v) : tap N q.val = ⟨v,.inr (index N v q)⟩ := by
    rcases q with ⟨p,h⟩
    subst v
    rfl
  exact (atPort ((index N v).symm i)).trans
    (congrArg (fun j => (⟨v,.inr j⟩ : Vertex N)) ((index N v).apply_symm_apply i))

def graph : Network D P bits where
  Site := Vertex N
  Edge := Cable N
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src
    | .inl e => tap N (.inr (e,false))
    | .inr ⟨v,k⟩ => ⟨v,Attachment.prevSite k⟩
  dst
    | .inl e => tap N (.inr (e,true))
    | .inr ⟨v,k⟩ => ⟨v,Attachment.nextSite k⟩
  width
    | .inl e => N.width e
    | .inr ⟨v,_⟩ => ∑i,localWidth N v i
  attach p := tap N (.inl p)
  position v := N.position v.1
  in_ball v := N.in_ball v.1

abbrev Tuple (v : N.Site) := (i : Fin (count N v)) → Fin (localWidth N v i) → Bool

def tuple (v : N.Site) : (Fin (∑i,localWidth N v i)→Bool) ≃ Tuple N v :=
  (Equiv.arrowCongr finSigmaFinEquiv.symm (Equiv.refl _)).trans (Equiv.piCurry (fun _ _=>Bool))

abbrev Private (v : N.Site) := Fin (count N v+1) → Tuple N v

def decode : (graph N).Assignment ≃ N.Assignment × ((v : N.Site) → Private N v) where
  toFun z := (fun e=>z (.inl e),fun v k=>tuple N v (z (.inr ⟨v,k⟩)))
  invFun p
    | .inl e => p.1 e
    | .inr ⟨v,k⟩ => (tuple N v).symm (p.2 v k)
  left_inv z := by
    funext e
    rcases e with e | ⟨v,k⟩
    · rfl
    · exact (tuple N v).symm_apply_apply _
  right_inv p := by
    rcases p with ⟨a,z⟩
    refine Prod.ext ?_ ?_
    · rfl
    · funext v k
      exact (tuple N v).apply_symm_apply _

def visible (a : N.Assignment) (pins : Ports bits) : (p : Leg N) → Fin (width N p) → Bool
  | .inl p => pins p
  | .inr (e,_) => a e

def args (a : N.Assignment) (pins : Ports bits) (v : N.Site) : Tuple N v :=
  fun i=>visible N a pins (name N v i)

def fromTuple {v : N.Site} (t : Tuple N v) (p : Fibre N v) : Fin (width N p.val) → Bool :=
  fun j=>t (index N v p) (Fin.cast (by simp [localWidth,name]) j)

theorem fromTuple_args (a : N.Assignment) (pins : Ports bits) {v : N.Site} (p : Fibre N v) :
    fromTuple N (args N a pins v) p=visible N a pins p.val := by
  funext j
  have atPort (q : Fibre N v) (same : q = p) :
      visible N a pins q.val (Fin.cast (congrArg (fun t : Fibre N v => width N t.val) same.symm) j) =
        visible N a pins p.val j := by
    subst q
    rfl
  exact atPort _ ((index N v).symm_apply_apply p)

private def cablePort (v : N.Site) (e : {e : N.Edge // N.src e=v ∨ N.dst e=v}) : Fibre N v :=
  if h : N.src e.val=v then ⟨.inr (e.val,false),h⟩ else ⟨.inr (e.val,true),e.property.resolve_left h⟩

variable {K : Type*} [CommSemiring K] (T : N.Tables K)

def rootTable (v : N.Site) (z : Tuple N v) : K :=
  T v (fun e j=>fromTuple N z (cablePort N v e) (Fin.cast (by unfold cablePort; split <;> rfl : N.width e.val=width N (cablePort N v e).val) j))
    (fun p=>fromTuple N z ⟨.inl p.val,p.property⟩)

omit [CommSemiring K] in
@[simp] theorem root_args (a : N.Assignment) (pins : Ports bits) (v : N.Site) :
    rootTable N T v (args N a pins v)=N.read T a pins v := by
  unfold rootTable Network.read
  simp only [fromTuple_args]
  congr 1
  funext e j
  have atCable (q : Leg N) (s : Bool) (same : q = .inr (e.val,s))
      (size : N.width e.val = width N q) :
      visible N a pins q (Fin.cast size j) = a e.val j := by
    subst q
    rfl
  have size : N.width e.val = width N (cablePort N v e).val := by
    unfold cablePort
    split <;> rfl
  by_cases h : N.src e.val = v
  · exact atCable _ false (by simp [cablePort,h]) size
  · exact atCable _ true (by simp [cablePort,h]) size

/-- Evaluate the local coefficient against a complete word assignment. A path
tap checks its single named exterior word. Its two other reads are adjacent
spine words. A unary end supplies the old local tensor. -/
def eval (a : (graph N).Assignment) (pins : Ports bits) : Vertex N → K
  | ⟨v,.inl false⟩ => rootTable N T v ((decode N a).2 v 0)
  | ⟨_,.inl true⟩ => 1
  | ⟨v,.inr i⟩ => Attachment.tap i (args N (decode N a).1 pins v i)
      ((decode N a).2 v i.castSucc) ((decode N a).2 v i.succ)

private theorem visible_local (a b : (graph N).Assignment) (x y : Ports bits) (p : Leg N)
    (wires : ∀e,(graph N).src e=tap N p ∨ (graph N).dst e=tap N p → a e=b e)
    (pins : ∀q,(graph N).attach q=tap N p → x q=y q) :
    visible N (decode N a).1 x p=visible N (decode N b).1 y p := by
  rcases p with q|⟨e,s⟩
  · exact pins q rfl
  · cases s
    · exact wires (.inl e) (Or.inl rfl)
    · exact wires (.inl e) (Or.inr rfl)

theorem eval_local (v : Vertex N) (a b : (graph N).Assignment) (x y : Ports bits)
    (wires : ∀e,(graph N).src e=v ∨ (graph N).dst e=v → a e=b e)
    (pins : ∀q,(graph N).attach q=v → x q=y q) : eval N T a x v=eval N T b y v := by
  rcases v with ⟨v,(_|_)|i⟩
  · exact congrArg (fun w=>rootTable N T v (tuple N v w)) (wires (.inr ⟨v,0⟩) (Or.inl rfl))
  · rfl
  · have outward := visible_local N a b x y (name N v i) (by simpa using wires) (by simpa using pins)
    have left := wires (.inr ⟨v,i.castSucc⟩) (Or.inr (by simp [graph,Attachment.nextSite]))
    have right := wires (.inr ⟨v,i.succ⟩) (Or.inl rfl)
    change Attachment.tap i (visible N (decode N a).1 x (name N v i))
      (tuple N v (a (.inr ⟨v,i.castSucc⟩))) (tuple N v (a (.inr ⟨v,i.succ⟩))) =
      Attachment.tap i (visible N (decode N b).1 y (name N v i))
        (tuple N v (b (.inr ⟨v,i.castSucc⟩))) (tuple N v (b (.inr ⟨v,i.succ⟩)))
    rw [outward,left,right]

def tables : (graph N).Tables K := DescentLocalTables.tables (graph N) (eval N T)

theorem read_eq (a : (graph N).Assignment) (p : Ports bits) (v : Vertex N) :
    (graph N).read (tables N T) a p v=eval N T a p v :=
  DescentLocalTables.read (graph N) (eval N T) (eval_local N T) a p v

/-- Sum the internal path wires at every original site independently. The
complete old tensor, at every boundary word, is unchanged. -/
theorem value_eq (p : Ports bits) : (graph N).value (tables N T) p=N.value T p := by
  let stage (a : N.Assignment) (v : N.Site) (z : Private N v) :=
    rootTable N T v (z 0)*∏i,Attachment.tap i (args N a p v i) (z i.castSucc) (z i.succ)
  have one (a : N.Assignment) (v : N.Site) : (∑z,stage a v z)=N.read T a p v :=
    (Attachment.spine_eq (rootTable N T v) (args N a p v)).trans (root_args N T a p v)
  have term (a : (graph N).Assignment) : (∏v, (graph N).read (tables N T) a p v) =
      ∏v,stage (decode N a).1 v ((decode N a).2 v) := by
    let row : Vertex N → K := eval N T a p
    calc
      _ = ∏v : Vertex N, row v :=
        Finset.prod_congr rfl fun v _ => read_eq N T a p v
      _ = ∏v,∏s,row ⟨v,s⟩ := Fintype.prod_sigma row
      _ = _ := by
        apply Finset.prod_congr rfl
        intro v _
        rw [Fintype.prod_sum_type (fun s : Bool ⊕ Fin (count N v) => row ⟨v,s⟩),
          Fintype.prod_bool]
        simp [row,eval,stage]
  unfold Network.value
  calc
    _ = ∑a, ∏v,stage (decode N a).1 v ((decode N a).2 v) := Finset.sum_congr rfl fun a _=>term a
    _ = ∑a : N.Assignment,∑z : (v:N.Site)→Private N v,∏v,stage a v (z v) := by
      rw [← Fintype.sum_prod_type', ←(decode N).sum_comp (fun s=>∏v,stage s.1 v (s.2 v))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [←Fintype.prod_sum]
      simp_rw [one]

end
end Hierarchy.DescentPhysicalSplit

end OAI
