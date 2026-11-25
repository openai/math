import OAI.ThreeFlat.Diagonal.ApproximatePort
import OAI.ThreeFlat.Diagonal.BoundaryPaths
import OAI.ThreeFlat.Diagonal.BoundaryWire
import OAI.ThreeFlat.Diagonal.GuardedNetwork

namespace OAI
/-! # Network computing the entries of the block approximation

A copy of the collapse evaluator reads the old and new inactive halves, the
tick pins, and the same advice for each block. Each bit of the active half
has one guard row. At touched chunks the guard compares two zeros. The
other rows compare the two endpoints of their bit. All intermediate storage
is shared by consecutive blocks at consecutive word addresses.
-/

namespace ThreeFlat.Diagonal.ApproximateNetwork

open BoundaryWire ApproximatePort

variable {F : Type*} {chunks a d t n q : ℕ}
variable (select : Fin (t+1) → Fin q → ApproximatePort (Fin chunks) d n a)
variable (slot : Fin (t+1) → Fin (n+1) → Fin chunks) (active : Fin (t+1) → Bool)

/-- The four pin fields of each tick are references to the shared boundary and
interior arrays; the old and new halves have the same physical coordinate system. -/
def stateWires (fetch : Fin (stateWidth chunks a) → Source chunks a t n d) :
    BitState (Fin chunks) (Source chunks a t n d) a :=
  (fun half chunk bit => fetch (chunkSite half chunk bit), fun bit => fetch (auxSite chunks bit))

def input (i : Fin (t+1)) (j : Fin q) : Source chunks a t n d :=
  route publicSource BitSource.constant (slot i) (active i) (stateWires (oldSource i))
    (stateWires (newSource i)) (interiorSource i) (select i j)

def guard (keep : Fin (t+1) → Fin chunks → Bool)
    (fetch : Fin (t+1) → Fin (stateWidth chunks a) → Source chunks a t n d)
    (i : Fin (t+1)) (j : Fin (chunks*a)) : Source chunks a t n d :=
  let k := finProdFinEquiv.symm j
  if keep i k.1 then fetch i (chunkSite (active i) k.1 k.2) else .constant false

def network [CommSemiring F] (N : BitNetwork F q) (keep : Fin (t+1) → Fin chunks → Bool) :
    BitNetwork F (pinWidth chunks a d) :=
  GuardedNetwork.network N (input select slot active)
    (guard active keep oldSource) (guard active keep newSource)

@[simp] theorem network_cells [CommSemiring F] (N : BitNetwork F q)
    (keep : Fin (t+1) → Fin chunks → Bool) :
    (network select slot active N keep).cells = (t+1)*(N.cells+chunks*a) := rfl

@[simp] theorem network_internal [CommSemiring F] (N : BitNetwork F q)
    (keep : Fin (t+1) → Fin chunks → Bool) :
    (network select slot active N keep).internal =
      t*stateWidth chunks a + (t+1)*(n*a) + (t+1)*N.internal := rfl

variable (D : Fin d → Bool) (x y : State chunks a) (g : Guesses chunks a t n)

private theorem map_old (i : Fin (t+1)) :
    mapState (fun s => s.read (guessEquiv chunks a t n g) (pinBits D x y))
      (stateWires (oldSource i)) = Fin.cons (α := fun _ => State chunks a) x g.1 i := by
  apply Prod.ext
  · funext k l b
    simp [mapState, stateWires]
  · funext b
    simp [mapState, stateWires]

private theorem map_new (i : Fin (t+1)) :
    mapState (fun s => s.read (guessEquiv chunks a t n g) (pinBits D x y))
      (stateWires (newSource i)) = Fin.snoc (α := fun _ => State chunks a) g.1 y i := by
  apply Prod.ext
  · funext k l b
    simp [mapState, stateWires]
  · funext b
    simp [mapState, stateWires]

theorem read_input (i : Fin (t+1)) (j : Fin q) :
    (input select slot active i j).read (guessEquiv chunks a t n g) (pinBits D x y) =
      route D id (slot i) (active i) (Fin.cons (α := fun _ => State chunks a) x g.1 i)
        (Fin.snoc (α := fun _ => State chunks a) g.1 y i) (g.2 i) (select i j) := by
  let ev := fun s : Source chunks a t n d => s.read (guessEquiv chunks a t n g) (pinBits D x y)
  change ev (route _ _ _ _ _ _ _ _) = _
  rw [route_map ev, map_old D x y g, map_new D x y g]
  congr 1
  · funext j; exact publicSource_read D x y g j
  · funext k l; exact interiorSource_read D x y g i k l

theorem guards_iff (keep : Fin (t+1) → Fin chunks → Bool)
    (test : ∀ i k, keep i k = true ↔ k ∉ Finset.univ.image (slot i)) (i : Fin (t+1)) :
    (∀ j, (guard active keep oldSource i j).read (guessEquiv chunks a t n g) (pinBits D x y) =
      (guard active keep newSource i j).read (guessEquiv chunks a t n g) (pinBits D x y)) ↔
      ∀ k ∉ Finset.univ.image (slot i),
        (Fin.cons (α := fun _ => State chunks a) x g.1 i).1 (active i) k =
          (Fin.snoc (α := fun _ => State chunks a) g.1 y i).1 (active i) k := by
  constructor
  · intro hg k hk
    funext l
    simpa [guard, (test i k).mpr hk] using hg (finProdFinEquiv (k,l))
  · intro hg j
    obtain ⟨⟨k,l⟩,rfl⟩ := finProdFinEquiv.surjective j
    cases h : keep i k with
    | false => simp [guard, h]
    | true => simpa [guard, h] using congrFun (hg k ((test i k).mp h)) l

/-- The entries of this dense bit network are exactly the entries of the
chronological product of the physical approximating blocks. -/
theorem eval [Field F] (N : BitNetwork F q) (keep : Fin (t+1) → Fin chunks → Bool)
    (test : ∀ i k, keep i k = true ↔ k ∉ Finset.univ.image (slot i)) (D : Fin d → Bool)
    (x y : State chunks a) :
    (network select slot active N keep).eval (pinBits D x y) =
      (List.ofFn fun i => ∑ f, physicalFixing (slot i) (active i) f
        (catalyst N (select i) D f)).prod x y := by
  classical
  let K (i : Fin (t+1)) (h : Fin n → Fin a → Bool) : Matrix (State chunks a) (State chunks a) F :=
    fun l r => if ∀ k ∉ Finset.univ.image (slot i), l.1 (active i) k = r.1 (active i) k then
      N.eval (route D id (slot i) (active i) l r h ∘ select i) else 0
  have eqMat (i : Fin (t+1)) :
      (∑ f, physicalFixing (slot i) (active i) f (catalyst N (select i) D f)) = ∑ h, K i h := by
    ext l r
    rw [fixing_sum, Matrix.sum_apply]
    simp [K, Finset.sum_ite_irrel]
  simp_rw [eqMat]
  rw [prod_entry_private, network, GuardedNetwork.eval]
  let along (h : Fin (hiddenWidth chunks a t n) → Bool) := ∏ i : Fin (t+1),
    if ∀ j, (guard active keep oldSource i j).read h (pinBits D x y) =
             (guard active keep newSource i j).read h (pinBits D x y) then
      N.eval (fun j => (input select slot active i j).read h (pinBits D x y)) else 0
  change (∑ h, along h) = _
  rw [← (guessEquiv chunks a t n).sum_comp along, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro i _
  simp only [K, guards_iff slot active D x y _ keep test, read_input]
  rfl

end ThreeFlat.Diagonal.ApproximateNetwork

end OAI
