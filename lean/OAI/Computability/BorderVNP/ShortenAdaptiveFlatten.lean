import OAI.Computability.BorderVNP.ShortenAdaptiveTree

/-!
# Flat port and leaf numbers of a complete shortening tree

The first branch digit is the most significant. A child number `i` and
local copy ordinal `j` have flat index `k^b * i + j`. Every flattened port
keeps its original width and every child pack keeps its own tensor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.Adaptive

open Crossing Packing
open scoped BigOperators

/-- Row-major numbering of the children and their depth-`b` leaves. -/
def copyIndex (k b : ℕ) : Fin k × Fin (k^b) ≃ Fin (k^(b+1)) :=
  finProdFinEquiv.trans (finCongr (by rw [pow_succ, Nat.mul_comm]))

/-- The first branch digit strides by the full number of copies beneath that branch. -/
theorem copyIndex_val (k b : ℕ) (i : Fin k) (j : Fin (k^b)) :
    (copyIndex k b (i,j)).val = k^b * i.val + j.val := Nat.add_comm _ _

private def singletonPort (P : Type) : P ≃ Fin 1 × P where
  toFun p := (0,p)
  invFun p := p.2
  left_inv _ := rfl
  right_inv _ := Prod.ext (Subsingleton.elim _ _) rfl

/-- Relabel the free ports by their flat leaf number and their original port. -/
def portEquiv (k : ℕ) (P : Type) : (b : ℕ) → Port k P b ≃ Fin (k^b) × P
  | 0 => singletonPort P
  | b+1 => ((Equiv.refl (Fin k)).prodCongr (portEquiv k P b)).trans
      ((Equiv.prodAssoc (Fin k) (Fin (k^b)) P).symm.trans ((copyIndex k b).prodCongr (Equiv.refl P)))

/-- The child and local ordinal give the row-major flat port exactly. -/
theorem portEquiv_succ (k : ℕ) (P : Type) (b : ℕ) (i : Fin k) (p : Port k P b) :
    portEquiv k P (b+1) (i,p) = (copyIndex k b (i,(portEquiv k P b p).1),(portEquiv k P b p).2) := rfl

/-- The relabelling keeps the original bit width of every external slot. -/
theorem width_portEquiv {P : Type} (bits : P → ℕ) (k : ℕ) (b : ℕ) (p : Port k P b) :
    width bits k b p = bits (portEquiv k P b p).2 := by
  induction b with
  | zero => rfl
  | succ b ih => exact ih p.2

/-- A complete tree of arbitrary leaf values is bijective to an arbitrary flat array. -/
def leavesEquiv (k : ℕ) (A : Type*) : (b : ℕ) → (Fin (k^b) → A) ≃ Leaves k A b
  | 0 => Equiv.funUnique (Fin 1) A
  | b+1 => ((copyIndex k b).symm.arrowCongr (Equiv.refl A)).trans
      ((Equiv.curry (Fin k) (Fin (k^b)) A).trans (Equiv.piCongrRight fun _ => leavesEquiv k A b))

/-- A child receives exactly its contiguous row-major block of the input array. -/
theorem leavesEquiv_succ (k : ℕ) (A : Type*) (b : ℕ) (flat : Fin (k^(b+1)) → A) (i : Fin k) :
    leavesEquiv k A (b+1) flat i = leavesEquiv k A b (fun j => flat (copyIndex k b (i,j))) := rfl

/-- Pull a flat external assignment onto the nested free ports. -/
def nestedPorts {P : Type} (bits : P → ℕ) (k b : ℕ)
    (x : Ports (fun p : Fin (k^b) × P => bits p.2)) : Ports (width bits k b) :=
  fun p t => x (portEquiv k P b p) (Fin.cast (width_portEquiv bits k b p) t)

variable {D k : ℕ} {P : Type} {bits : P → ℕ} {R : Type*}

/-- A physical output pack presented with one flat leaf number on each free port.
Its internal sites, cables and local tensors are retained. -/
def flattenPack (b : ℕ) (p : Pack D (Port k P b) (width bits k b) R) :
    Pack D (Fin (k^b) × P) (fun q => bits q.2) R where
  layout := { p.layout with attach := fun q => p.layout.attach ((portEquiv k P b).symm q) }
  table v a x := p.table v a (fun q t =>
    x ⟨portEquiv k P b q.val, by
      change p.layout.attach ((portEquiv k P b).symm (portEquiv k P b q.val)) = v
      rw [Equiv.symm_apply_apply]; exact q.property⟩ (Fin.cast (width_portEquiv bits k b q.val) t))

/-- Relabelling free ports commutes with the contraction of the actual output network. -/
theorem tensor_flattenPack [CommSemiring R] (b : ℕ) (p : Pack D (Port k P b) (width bits k b) R)
    (x : Ports (fun q : Fin (k^b) × P => bits q.2)) :
    (flattenPack b p).tensor x = p.tensor (nestedPorts bits k b x) := rfl

private theorem flat_product [CommSemiring R] {A : Type*} (leaf : A → Pack D P bits R) (b : ℕ)
    (flat : Fin (k^b) → A) (x : Ports (fun q : Fin (k^b) × P => bits q.2)) :
    (parallelLeaves leaf b (leavesEquiv k A b flat)).tensor (nestedPorts bits k b x) =
      ∏ i, (leaf (flat i)).tensor (fun p => x (i,p)) := by
  induction b with
  | zero =>
    exact (Fintype.prod_unique (fun i : Fin 1 => (leaf (flat i)).tensor (fun p => x (i,p)))).symm
  | succ b ih =>
    let N := fun i : Fin k => parallelLeaves leaf b (leavesEquiv k A b (fun j => flat (copyIndex k b (i,j))))
    have hprod := Network.parallel_value (fun i => (N i).layout) (fun i => (N i).table) (nestedPorts bits k (b+1) x)
    refine hprod.trans ?_
    let f (z : Fin (k^(b+1))) := (leaf (flat z)).tensor (fun p => x (z,p))
    have he := (copyIndex k b).prod_comp f
    rw [Fintype.prod_prod_type] at he
    apply Eq.trans _ he
    exact Finset.prod_congr rfl fun i _ => ih (fun j => flat (copyIndex k b (i,j)))
      (fun q => x (copyIndex k b (i,q.1),q.2))

/-- For every flat array of arbitrary input packs, nested parallel grouping has the same
tensor as their ordinary flat parallel union, with the exact free-port relabelling. -/
theorem tensor_parallelLeaves [CommSemiring R] {A : Type*} (leaf : A → Pack D P bits R) (b : ℕ)
    (flat : Fin (k^b) → A) (x : Ports (fun q : Fin (k^b) × P => bits q.2)) :
    (flattenPack b (parallelLeaves leaf b (leavesEquiv k A b flat))).tensor x =
      (parallelPacks (fun i => leaf (flat i))).tensor x :=
  (flat_product leaf b flat x).trans (Network.parallel_value (fun i => (leaf (flat i)).layout)
    (fun i => (leaf (flat i)).table) x).symm

/-- The full dependent histogram sum for one inner epoch, exposed on the flat external ports
required by the next placement or sewing operation. -/
theorem System.tensor_flatHistories [CommSemiring R] {b : ℕ} {A : ℕ → Type*} (S : System k b A)
    (pack : ∀ n, A n → Pack D (Port k P n) (width bits k n) R) (exact : S.Exact pack)
    (n : ℕ) (hn : n ≤ b) (flat : Fin (k^n) → A 0) (x : Ports (fun q : Fin (k^n) × P => bits q.2)) :
    (parallelPacks (fun i => pack 0 (flat i))).tensor x =
      ∑ q, (flattenPack n (pack n ((S.layer n).state ((S.histories n hn (leavesEquiv k (A 0) n flat)).term q)))).tensor x :=
  (tensor_parallelLeaves (pack 0) n flat x).symm.trans
    (S.tensor_histories pack exact n hn (leavesEquiv k (A 0) n flat) (nestedPorts bits k n x))

end Shortening.Adaptive

end BorderVNP
end Computability
end OAI
