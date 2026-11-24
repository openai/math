import OAI.Computability.VPVNP.DegreeRefreshExpansion
import OAI.Computability.VPVNP.DegreeRefreshIncidence
import OAI.Computability.VPVNP.NetworkKernel

/-!
# The degree refresh as a placed wire-kernel step

In Section 7.3, each old position becomes a port of its block. Its vertex
factor stays whole at that port. The local map reads the outgoing external
word, the incoming word in source-segment order, and the selected supply
half-wires. All padding wires have their unique zero-bit payload.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace Compression.Refresh

open WireTensor NetworkKernel

variable {B S : Type} {d : ℕ} [Fintype B] [Fintype S]

/-- The old wire network in block, slot, and old source-port coordinates. -/
noncomputable def oldWireGraph (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) : Network where
  Site := B × Fin d
  siteFintype := inferInstance
  Edge := Arc B d
  edgeFintype := inferInstance
  src := source
  dst e := source (t e)
  Payload e := Word (w e)
  payloadFintype _ := inferInstance

/-- External slots, one copy of the supply edges per block, and cyclic padding slots. -/
abbrev OutputEdge (B S : Type) (d pad : ℕ) :=
  (B × Fin d) ⊕ ((B × S) ⊕ ((B × Fin d) × Fin pad))

private def outputPayload (w : Arc B d → ℕ) (A : B → S → Type) (pad : ℕ) :
    OutputEdge B S d pad → Type
  | .inl p => Word (∑ j, w (p,j))
  | .inr (.inl (s,e)) => A s e
  | .inr (.inr _) => Word 0

/-- The selected output has one external slot per port. Each copy of the
supply graph lies within one block, as do all cyclic padding arcs. -/
noncomputable def refreshOutput (target : Equiv.Perm (B × Fin d)) (w : Arc B d → ℕ)
    (a b : S → Fin d) (A : B → S → Type) [∀ s e, Fintype (A s e)] (pad : ℕ) : Network where
  Site := B × Fin d
  siteFintype := inferInstance
  Edge := OutputEdge B S d pad
  edgeFintype := inferInstance
  src
    | .inl p => p
    | .inr (.inl (s,e)) => (s,a e)
    | .inr (.inr (p,_)) => p
  dst
    | .inl p => target p
    | .inr (.inl (s,e)) => (s,b e)
    | .inr (.inr ((s,i),_)) => (s,finRotate d i)
  Payload := outputPayload w A pad
  payloadFintype
    | .inl _ => inferInstanceAs (Fintype (Word _))
    | .inr (.inl (s,e)) => inferInstanceAs (Fintype (A s e))
    | .inr (.inr _) => inferInstanceAs (Fintype (Word 0))

variable (target : Equiv.Perm (B × Fin d)) (w : Arc B d → ℕ) (a b : S → Fin d)
  (A : B → S → Type) [∀ s e, Fintype (A s e)] (pad : ℕ)

/-- Concatenated external words and internal assignments together specify
one assignment to the output wires, with every padding slot uniquely filled. -/
def outputAssignments :
    External w × ((s : B) → (e : S) → A s e) ≃
      ((e : (refreshOutput target w a b A pad).Edge) →
        (refreshOutput target w a b A pad).Payload e) where
  toFun zy
    | .inl p => zy.1 p
    | .inr (.inl (s,e)) => zy.2 s e
    | .inr (.inr _) => Fin.elim0
  invFun q := (fun p ↦ q (.inl p), fun s e ↦ q (.inr (.inl (s,e))))
  left_inv _ := rfl
  right_inv q := by
    funext e
    rcases e with p | ⟨s,e⟩ | p
    · rfl
    · rfl
    · exact Subsingleton.elim (α := Word 0) _ _

variable {R : Type*} [CommSemiring R]

/-- The two half-wire lists of the supply motif are read from the internal
arcs of this block, retaining their independent source and target values. -/
def supplyHalf (p : B × Fin d) (u : (refreshOutput target w a b A pad).Half p) :
    (wireNetwork (k := R) a b (A p.1)).Basis p.2 :=
  (fun e h ↦ u.1 (.inr (.inl (p.1,e))) (Prod.ext rfl h),
   fun e h ↦ u.2 (.inr (.inl (p.1,e))) (Prod.ext rfl h))

variable {I : B → Type} [∀ s, Fintype (I s)]

/-- The port-local term of (7.1) for one joint selection of the block motif maps. -/
noncomputable def refreshTerm (t : Equiv.Perm (Arc B d)) (target : Equiv.Perm (B × Fin d))
    (ht : ∀ e : Arc B d, (t e).1 = target e.1) (w : Arc B d → ℕ) (a b : S → Fin d)
    (A : (s : B) → I s → S → Type) [∀ s i e, Fintype (A s i e)]
    (M : ∀ s (i : I s) j, (internalDemand R t w s).Basis j →
      (blockSupply (R := R) a b A s i).Basis j → R)
    (pad : ℕ) (c : (s : B) → I s) : Term R (oldWireGraph t w) where
  output := refreshOutput target w a b (fun s ↦ A s (c s)) pad
  place := id
  kernel p x u :=
    let z := incidentPortSegments t target ht w p (u.1 (.inl p) rfl)
      (u.2 (.inl (target.symm p)) (target.apply_symm_apply p).symm)
    refreshFactor t w a b A M p.1 (c p.1) p.2 (x p rfl) z
      (supplyHalf target w a b (fun s ↦ A s (c s)) pad p u)

variable (t : Equiv.Perm (Arc B d)) (ht : ∀ e : Arc B d, (t e).1 = target e.1)
  (labels : (s : B) → I s → S → Type) [∀ s i e, Fintype (labels s i e)]
  (M : ∀ s (i : I s) j, (internalDemand R t w s).Basis j →
    (blockSupply (R := R) a b labels s i).Basis j → R)

omit [∀ s, Fintype (I s)] in
/-- For a selected term the shared output-edge sum equals the sum over the
external strings and the independent internal assignments in every block. -/
theorem refreshTerm_value (c : (s : B) → I s) (x : ∀ p, (oldWireGraph t w).Half p) :
    (refreshTerm t target ht w a b labels M pad c).value x =
      ∑ z : External w, ∑ y : (s : B) → (e : S) → labels s (c s) e,
        ∏ s, ∏ j, refreshFactor t w a b labels M s (c s) j (x (s,j))
          (portSegments t w z s j) (edgeAssignment a b (y s) j) := by
  let term := refreshTerm t target ht w a b labels M pad c
  let f (u : (e : term.output.Edge) → term.output.Payload e) :=
    ∏ p, term.kernel p (fun q _ ↦ x q) (edgeAssignment term.output.src term.output.dst u p)
  rw [Term.value_eq_edgeSum]
  change (∑ u, f u) = _
  let split := outputAssignments target w a b (fun s ↦ labels s (c s)) pad
  refine (split.sum_comp f).symm.trans ?_
  refine (Fintype.sum_prod_type (fun u ↦ f (split u))).trans ?_
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  change (∏ p : B × Fin d, _) = _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro s _
  apply Finset.prod_congr rfl
  intro j _
  change refreshFactor t w a b labels M s (c s) j (x (s,j))
    (incidentPortSegments t target ht w (s,j) (z (s,j)) (z (target.symm (s,j))))
    (edgeAssignment a b (y s) j) = _
  rw [incidentPortSegments_external]

/-- An ordinary motif identity in each block produces the degree-refresh
step of (7.1), with identity placement in the grouped port coordinates. -/
noncomputable def refreshStep
    (h : ∀ s, (internalDemand R t w s).coeff =
      ∑ i, applyLocal (M s i) (blockSupply (R := R) a b labels s i).coeff) :
    Step R (oldWireGraph t w) where
  Choice := (s : B) → I s
  choiceFintype := inferInstance
  term := refreshTerm t target ht w a b labels M pad
  exact_eq x := by
    simp only [refreshTerm_value]
    exact refresh_edge_expansion t w a b labels M h x

end Compression.Refresh

end VPVNP
end Computability
end OAI
