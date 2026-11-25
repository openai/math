import OAI.Hierarchy.DescentOrderedWords

namespace OAI
/-! # Sparse-key evaluator of each literal binary contact node -/

namespace Hierarchy.DescentOrderedWords.Contact
open Computability.BorderVNP.Crossing DescentContactTree DescentContactTree.Physical
open scoped BigOperators Classical
noncomputable section
variable {I : Type} [Fintype I] {N D h : ℕ} (key : I↪Fin N) (dest : I→ℕ→Bool) (wt : I→ℕ)

def cellKey (k : ℕ) (v : Node k) : Cell dest k v ↪ Fin N :=
  (Function.Embedding.subtype _).trans key

def fibreRead (k : ℕ) (v : Node k) := decode (cellKey key dest k v) (fun i=>wt i.val)

def remapEdges : Equiv.Perm (graph dest wt D h).Assignment :=
  Equiv.piCongrRight fun e=>Equiv.arrowCongr
    (permutation (cellKey key dest (e.1.val+1) e.2) (fun i=>wt i.val)).symm (Equiv.refl Bool)

def remapPins : Equiv.Perm (Ports (terminalWidth dest wt h)) :=
  Equiv.piCongrRight fun p=>match p with
  | .inl _ => Equiv.arrowCongr (permutation key wt).symm (Equiv.refl Bool)
  | .inr v => Equiv.arrowCongr (permutation (cellKey key dest h v) (fun i=>wt i.val)).symm (Equiv.refl Bool)

def innerRows (a : (graph dest wt D h).Assignment) (k : Fin h) (i : I) : Fin (wt i)→Bool :=
  fibreRead key dest wt _ (prefixAt dest (k.val+1) i) (a ⟨k,prefixAt dest (k.val+1) i⟩) ⟨i,rfl⟩

def rootRow (p : Ports (terminalWidth dest wt h)) := decode key wt (p (.inl ()))

def leafRow (p : Ports (terminalWidth dest wt h)) (i : I) : Fin (wt i)→Bool :=
  fibreRead key dest wt _ (prefixAt dest h i) (p (.inr (prefixAt dest h i))) ⟨i,rfl⟩

theorem inner_eq (a : (graph dest wt D h).Assignment) :
    hidden dest wt (remapEdges key dest wt a)=innerRows key dest wt a := by
  funext k i
  let v := prefixAt dest (k.val+1) i
  exact congrFun (decode_eq (cellKey key dest (k.val+1) v)
    (fun z=>wt z.val) (a ⟨k,v⟩)).symm (⟨i,rfl⟩ : Cell dest (k.val+1) v)

theorem top_eq (p : Ports (terminalWidth dest wt h)) : top dest wt (remapPins key dest wt p)=rootRow key dest wt p := by
  exact (decode_eq key wt _).symm

theorem ground_eq (p : Ports (terminalWidth dest wt h)) :
    ground dest wt (remapPins key dest wt p)=leafRow key dest wt p := by
  funext i
  let v := prefixAt dest h i
  exact congrFun (decode_eq (cellKey key dest h v)
    (fun z=>wt z.val) (p (.inr v))).symm (⟨i,rfl⟩ : Cell dest h v)

/-- Every decision is a bit-equality test at two explicit sparse offsets of
the same old identity. Its only data are the actual chronological keys,
the gate's parent/child wire words, and the destination bits. -/
def factor {K : Type*} [CommSemiring K] (a : (graph dest wt D h).Assignment)
    (p : Ports (terminalWidth dest wt h)) (q : Site h) : K :=
  if ∀i : Cell dest q.1.val q.2,incoming wt (rootRow key dest wt p) (innerRows key dest wt a) q.1 i.val=
      outgoing wt (leafRow key dest wt p) (innerRows key dest wt a) q.1 i.val then 1 else 0

theorem read_eq {K : Type*} [CommSemiring K] (a : (graph dest wt D h).Assignment)
    (p : Ports (terminalWidth dest wt h)) (q : Site h) :
    (graph dest wt D h).read (Physical.tables (K:=K) dest wt) (remapEdges key dest wt a)
      (remapPins key dest wt p) q=factor key dest wt a p q := by
  refine (DescentLocalTables.read (graph dest wt D h)
    (relayFactor (K:=K) (D:=D) (h:=h) dest wt) (supported (K:=K) dest wt)
    (remapEdges key dest wt a) (remapPins key dest wt p) q).trans ?_
  simp only [relayFactor,inner_eq key dest wt a,top_eq key dest wt p,ground_eq key dest wt p,factor]

end
end Hierarchy.DescentOrderedWords.Contact

end OAI
