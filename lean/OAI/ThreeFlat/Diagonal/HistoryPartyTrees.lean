import OAI.ThreeFlat.Diagonal.HistogramOccupiedNetwork

namespace OAI
/-! # Explicit postorder trees of the tile and histogram contractions

The leaves are only bounded base LUTs and uniform dyadic compactor templates.
An entire dynamic party network is never stored as an opaque leaf.
-/

namespace ThreeFlat.Diagonal.HistoryContraction.Tree

open MotifOrderedCells MotifOuterTerms HistogramTileNetwork LinearAlgebra.SpectralBooks Computability.VPVNP.MotifSelector
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [CommRing F] {n p h a b r d e s : ℕ}

def batch {arity : Fin n → ℕ} (N : ∀ i, BitNetwork F (arity i)) (wire : ∀ i, Fin (arity i) → BitSource h p) : Tree F p :=
  .join h n arity wire (fun i => .atom (N i))

omit [CommRing F] in
@[simp] theorem compile_batch {arity : Fin n → ℕ} (N : ∀ i, BitNetwork F (arity i)) (wire : ∀ i, Fin (arity i) → BitSource h p) :
    (batch N wire).compile = BitNetwork.Ordered.glue N wire := rfl

private structure Member (F : Type*) (p : ℕ) where
  pins : ℕ
  node : Tree F pins
  access : Fin pins → BitSource 0 p

private def paired (A : Tree F a) (B : Tree F b) : Fin 2 → Member F (a+b) :=
  ![⟨_,A,fun j => .pin (j.castAdd b)⟩,⟨_,B,fun j => .pin (Fin.natAdd a j)⟩]

def pair (A : Tree F a) (B : Tree F b) : Tree F (a+b) :=
  .join 0 2 (fun i => (paired A B i).pins) (fun i => (paired A B i).access) (fun i => (paired A B i).node)

/-- Public projections of the two ordered children consumed by the physical pair join. -/
def pairArity (A : Tree F a) (B : Tree F b) (i : Fin 2) := (paired A B i).pins
def pairWire (A : Tree F a) (B : Tree F b) (i : Fin 2) :
    Fin (pairArity A B i) → BitSource 0 (a+b) := (paired A B i).access
def pairNetwork (A : Tree F a) (B : Tree F b) (i : Fin 2) :
    BitNetwork F (pairArity A B i) := (paired A B i).node.compile

omit [CommRing F] in
theorem pair_compile (A : Tree F a) (B : Tree F b) :
    (pair A B).compile=BitNetwork.Ordered.glue (pairNetwork A B) (pairWire A B) := rfl

theorem pair_eval (A : Tree F a) (B : Tree F b) (x : Fin a → Bool) (y : Fin b → Bool) :
    (pair A B).compile.eval (Fin.append x y) = A.compile.eval x * B.compile.eval y := by
  rw [pair,compile,BitNetwork.Ordered.glue_eval,Fintype.sum_unique,Fin.prod_univ_two]
  simp [paired,BitSource.read]

def tiled {H : Type*} (K : Tile F H e d b) (C : BitNetwork F ((r*d)+(r*d+r*d))) : Tree F (r*b+e*(r*d)) :=
  let X := pieces (checkedTile K.rule K.table) C
  batch (fun i => (X i).N) (fun i => (X i).wire)

@[simp] theorem tiled_compile {H : Type*} (K : Tile F H e d b) (C : BitNetwork F ((r*d)+(r*d+r*d))) :
    (tiled K C).compile = K.network C := rfl

def admission (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin s)
    (C : BitNetwork F (r+(r+r))) (v : Histogram (Fin s) r) : Tree F (r*b) :=
  let X := MotifSelectorChecks.components good letter C v
  batch (fun i => (X i).net) (fun i => (X i).wire)

@[simp] theorem admission_compile (good : (Fin b → Bool) → Prop) (letter : (Fin b → Bool) → Fin s)
    (C : BitNetwork F (r+(r+r))) (v : Histogram (Fin s) r) :
    (admission good letter C v).compile = MotifSelectorChecks.network good letter C v := rfl

variable {J E S H : Type*} [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [Fintype H] [DecidableEq H] [Nonempty H]
    {k : ℕ} (D : PortGraph J E) (G : Supply J S) (j : J) (base : E → ℕ)
    (B : Header (D.Port j) H (fun q => base q.1.1) k n) (sa : Fin e ≃ (ports G).Port j)
    (sw : H → S → ℕ) (fits : ∀ z a, sw z (sa a).1.1 ≤ d)
    (M : ∀ z v, D.State (fun a => Fin (2^base a)) v → (ports G).State (fun a => Fin (2^sw z a)) v → F)
    (id : H ≃ Fin s) (z : Histogram H r) (C : BitNetwork F ((r*d)+(r*d+r*d))) (count : BitNetwork F (r+(r+r)))

def party := pair (admission (headerGood G j sa B.code) (headerLetter G j sa id B.code) count (numberHistogram id z))
    (tiled (tile D G j base B sa sw fits M) C)

omit [Fintype J] [Nonempty J] [Fintype E] [Fintype S] [DecidableEq H] in
theorem party_value (x : Fin (r*(e*k)) → Bool) (y : Fin (r*B.arity+e*(r*d)) → Bool) :
    (party D G j base B sa sw fits M id z C count).compile.eval (Fin.append x y) =
      (partyNetwork D G j base B sa sw fits M id z C count).eval (Fin.append x y) := by
  rw [party,pair_eval,admission_compile,tiled_compile,partyNetwork,BitNetwork.Ordered.pair_eval]
  rfl

end
end ThreeFlat.Diagonal.HistoryContraction.Tree

end OAI
