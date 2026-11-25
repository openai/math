import OAI.Computability.BorderVNP.PackedInheritedParallelOrder

/-! # Parallel composition of persistent private site programs

Every site in the disjoint union executes its child's original private
program, including the observations of newly born paid entries. Its table
is the actual parallel tensor table, on every external and internal input.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening PublicParallel Parallel

variable {copies D M np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Fin copies → Network D P bits)
    (rows : ∀ i, (N i).Edge ↪ Fin M) (portID : P ↪ Fin np) (i : Fin copies) (v : (N i).Site)

private abbrev union := Network.parallel N

private theorem wireOrdinal_eq (z : Incident (N i) v) (k : Fin ((N i).width z.val)) :
    sourceOrder (union N) (parallelName rows) (portRows copies portID) ⟨i,v⟩ (.inl ⟨incident N i v z,k⟩) =
    Fin.cast (incoming_eq N i v).symm (sourceOrder (N i) (rows i) portID v (.inl ⟨z,k⟩)) := by
  apply Fin.ext
  exact (wireOrdinal (union N) _ _ _ (incident N i v z) k).trans
    ((congrArg (· + k.val) (wireStart_eq N rows portID i v z)).trans (wireOrdinal (N i) _ _ _ z k).symm)

private theorem portOrdinal_eq (p : Attached (N i) v) (k : Fin (bits p.val)) :
    sourceOrder (union N) (parallelName rows) (portRows copies portID) ⟨i,v⟩ (.inr ⟨attached N i v p,k⟩) =
    Fin.cast (incoming_eq N i v).symm (sourceOrder (N i) (rows i) portID v (.inr ⟨p,k⟩)) := by
  apply Fin.ext
  exact (portOrdinal (union N) _ _ _ (attached N i v p) k).trans
    ((congrArg (· + k.val) (portStart_eq N rows portID i v p)).trans (portOrdinal (N i) _ _ _ p k).symm)

/-- At a copy-site, the disjoint union's incoming vector reads exactly the original child's rows. -/
theorem parallel_inputWords
    (z : ∀ c : Incident (union N) ⟨i,v⟩, Fin ((union N).width c.val) → Bool)
    (x : ∀ u : Attached (union N) ⟨i,v⟩, Fin (bits u.val.2) → Bool) (k : Fin (incoming (N i) v)) :
    inputWords (union N) (parallelName rows) (portRows copies portID) ⟨i,v⟩ z x (Fin.cast (incoming_eq N i v).symm k) =
      inputWords (N i) (rows i) portID v (fun c => z (incident N i v c)) (fun u => x (attached N i v u)) k := by
  obtain ⟨t,rfl⟩ := (sourceOrder (N i) (rows i) portID v).surjective k
  rcases t with ⟨c,k⟩ | ⟨u,k⟩
  · rw [←wireOrdinal_eq]
    exact (inputWords_wire (union N) _ _ _ z x (incident N i v c) k).trans (inputWords_wire (N i) (rows i) portID v (fun t => z (incident N i v t)) (fun t => x (attached N i v t)) c k).symm
  · rw [←portOrdinal_eq]
    exact (inputWords_port (union N) _ _ _ z x (attached N i v u) k).trans (inputWords_port (N i) (rows i) portID v (fun t => z (incident N i v t)) (fun t => x (attached N i v t)) u k).symm

/-- The child state models its actual table in the parent parallel pack, for arbitrary observation weights. -/
theorem Site.Models.parallelPacks {R : Type*} [AddCommMonoid R] (p : Fin copies → Pack D P bits R)
    (rows : ∀ i, (p i).layout.Edge ↪ Fin M) (portID : P ↪ Fin np) (i : Fin copies) (v : (p i).layout.Site)
    (s : Site) (hsize : s.incoming = Inherited.incoming (p i).layout v) (weight : List (Bool × Option ℕ) → R)
    (models : s.Models (p i).layout (rows i) portID v hsize weight (p i).table) :
    let L := Packing.parallelPacks p
    s.Models L.layout (parallelName rows) (portRows copies portID) ⟨i,v⟩
      (hsize.trans (incoming_eq (fun j => (p j).layout) i v).symm) weight L.table := by
  dsimp only
  intro z x
  have hbits (k : Fin s.incoming) := parallel_inputWords (fun j => (p j).layout) rows portID i v z x (Fin.cast hsize k)
  exact (congrArg (s.value weight) (funext hbits)).trans (models _ _)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
