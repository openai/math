import OAI.ThreeFlat.BitNetwork.OrderedGlue
import OAI.ThreeFlat.Diagonal.ConstantKernelLUT
import OAI.ThreeFlat.Routing.StableCompactionRank

namespace OAI
/-! # Ordinal trivalent records for a product of tiled port entries

The broadcast header pins are copied in tile order. For each incident
stream, the cell guesses a mask and a supported candidate payload, and
checks its packed boundary with an independent stable compactor. Local
bounded-arity checks compute each tile value on the expanded payload.
All pointer arithmetic uses fixed-stride products or prefix offsets.
-/

namespace ThreeFlat.Diagonal.MotifOrderedCells

open Routing.StableCompaction TraceCircuit
open scoped BigOperators Classical

variable {F : Type*} [CommRing F] {r b e d p h : ℕ}

abbrev Fields (r e d : ℕ) := Fin e → Fin r → Fin d → Bool

/-- Fixed-stride numbering of `port, copy, candidate bit`. -/
def grid (r e d : ℕ) : Fields r e d ≃ (Fin (e*(r*d)) → Bool) :=
  (Equiv.piCongrRight (fun _ => blocks r d)).trans (blocks e (r*d))

@[simp] theorem grid_at (f : Fields r e d) (a : Fin e) (i : Fin r) (j : Fin d) :
    grid r e d f (finProdFinEquiv (a,finProdFinEquiv (i,j))) = f a i j := by
  simp [grid]

def privateFields (r e d : ℕ) : Fields r e d × Fields r e d ≃
    (Fin (e*(r*d) + e*(r*d)) → Bool) :=
  ((grid r e d).prodCongr (grid r e d)).trans (Fin.appendEquiv (α := Bool) _ _)

private theorem private_at (M D : Fields r e d) : privateFields r e d (M,D) = Fin.append (grid r e d M) (grid r e d D) := rfl

def arguments (head : Fin r → Fin b → Bool) (supply : Fin e → Fin (r*d) → Bool) :
    Fin (r*b + e*(r*d)) → Bool := Fin.append (blocks r b head) (blocks e (r*d) supply)

def gAddr (a : Fin e) (i : Fin r) (j : Fin d) : Fin (e*(r*d)) :=
  finProdFinEquiv (a,finProdFinEquiv (i,j))

def maskAddr (a : Fin e) (i : Fin r) (j : Fin d) : BitSource (e*(r*d)+e*(r*d)) p :=
  .hidden ((gAddr a i j).castAdd _)

def dataAddr (a : Fin e) (i : Fin r) (j : Fin d) : BitSource (e*(r*d)+e*(r*d)) p :=
  .hidden (Fin.natAdd _ (gAddr a i j))

def headAddr (i : Fin r) (j : Fin b) : BitSource h (r*b+e*(r*d)) :=
  .pin ((finProdFinEquiv (i,j)).castAdd _)

def outAddr (a : Fin e) (j : Fin (r*d)) : BitSource h (r*b+e*(r*d)) :=
  .pin (Fin.natAdd _ (finProdFinEquiv (a,j)))

/-- The per-copy inputs have fixed local arity, regardless of the number of copies. -/
def tileWire (i : Fin r) : Fin (b+(e*d+e*d)) → BitSource (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) :=
  Fin.append (headAddr i) (Fin.append
    (fun q => let z : Fin e × Fin d := finProdFinEquiv.symm q; maskAddr z.1 i z.2)
    (fun q => let z : Fin e × Fin d := finProdFinEquiv.symm q; dataAddr z.1 i z.2))

/-- Every compactor sees one mask array, the matching candidate bits, and the
proposed full packed stream. -/
def streamWire (a : Fin e) : Fin ((r*d)+(r*d+r*d)) →
    BitSource (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) :=
  Fin.append (fun q => let z : Fin r × Fin d := finProdFinEquiv.symm q; maskAddr a z.1 z.2)
    (Fin.append (fun q => let z : Fin r × Fin d := finProdFinEquiv.symm q; dataAddr a z.1 z.2)
      (outAddr a))

def copyPayload (f : Fields r e d) (i : Fin r) : Fin (e*d) → Bool :=
  blocks e d (fun a j => f a i j)

private theorem tile_read (head : Fin r → Fin b → Bool) (supply : Fin e → Fin (r*d) → Bool)
    (M D : Fields r e d) (i : Fin r) :
    (fun k => (tileWire i k).read (privateFields r e d (M,D)) (arguments head supply)) =
      Fin.append (head i) (Fin.append (copyPayload M i) (copyPayload D i)) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun q => ?_) k
  · simp only [tileWire,Fin.append_left,headAddr,BitSource.read,arguments,blocks_at]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) q <;>
      obtain ⟨⟨a,l⟩,rfl⟩ := finProdFinEquiv.surjective j <;>
      simp only [tileWire,maskAddr,dataAddr,gAddr,private_at,BitSource.read,copyPayload,Fin.append_left,Fin.append_right,Equiv.symm_apply_apply,grid_at,blocks_at]

private theorem stream_read (head : Fin r → Fin b → Bool) (supply : Fin e → Fin (r*d) → Bool)
    (M D : Fields r e d) (a : Fin e) :
    (fun k => (streamWire a k).read (privateFields r e d (M,D)) (arguments head supply)) =
      Fin.append (blocks r d (M a)) (Fin.append (blocks r d (D a)) (supply a)) := by
  funext k
  refine Fin.addCases (fun j => ?_) (fun q => ?_) k
  · obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective j
    simp only [streamWire,maskAddr,gAddr,private_at,BitSource.read,Fin.append_left,Equiv.symm_apply_apply,grid_at,blocks_at]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) q
    · obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective j
      simp only [streamWire,dataAddr,gAddr,private_at,BitSource.read,Fin.append_left,Fin.append_right,Equiv.symm_apply_apply,grid_at,blocks_at]
    · simp only [streamWire,outAddr,arguments,BitSource.read,Fin.append_right,blocks_at]

structure Piece (F : Type*) (h p : ℕ) where
  width : ℕ
  N : BitNetwork F width
  wire : Fin width → BitSource h p

def pieces (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) :
    Fin (r+e) → Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) :=
  Fin.addCases (motive := fun _ => Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d))) (fun i => ⟨_,ConstantKernelLUT.network (tiles i),tileWire i⟩)
    (fun a => ⟨_,C,streamWire a⟩)

private theorem pieces_left (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) (i : Fin r) :
    pieces tiles C (i.castAdd e) = ⟨_,ConstantKernelLUT.network (tiles i),tileWire i⟩ := Fin.addCases_left i

private theorem pieces_right (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) (a : Fin e) :
    pieces tiles C (Fin.natAdd r a) = ⟨_,C,streamWire a⟩ := Fin.addCases_right a

/-- A single explicitly numbered auxiliary network for all the copies and
all the ports of one compressed site. -/
def network (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) : BitNetwork F (r*b+e*(r*d)) :=
  BitNetwork.Ordered.glue (fun z => (pieces tiles C z).N) (fun z => (pieces tiles C z).wire)

/-- Each copy contributes one fixed-arity LUT and each incident port
contributes a single compacting network. -/
theorem network_rows (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) :
    (network tiles C).cells = r*(2^(b+(e*d+e*d))*((b+(e*d+e*d))+1)) + e*C.cells := by
  change (∑ i, (pieces tiles C i).N.cells) = _
  let f (q : Fin (r+e)) := (pieces (b:=b) (e:=e) (r:=r) (d:=d) tiles C q).N.cells
  have hl (i : Fin r) : f (i.castAdd e) = 2^(b+(e*d+e*d))*((b+(e*d+e*d))+1) :=
    (congrArg (fun x : Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.cells) (pieces_left (b:=b) (e:=e) (r:=r) (d:=d) tiles C i)).trans (ConstantKernelLUT.network_cells _)
  have hr (a : Fin e) : f (Fin.natAdd r a) = C.cells :=
    congrArg (fun x : Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.cells) (pieces_right (b:=b) (e:=e) (r:=r) (d:=d) tiles C a)
  rw [Fin.sum_univ_add f]
  simp only [hl,hr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

/-- Mask and candidate buffers each use a rectangular `e*r*d` array. -/
theorem network_bits (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) :
    (network tiles C).internal = e*(r*d)+e*(r*d) + (r*2^(b+(e*d+e*d)) + e*C.internal) := by
  change e*(r*d)+e*(r*d) + (∑ i, (pieces tiles C i).N.internal) = _
  let f (q : Fin (r+e)) := (pieces (b:=b) (e:=e) (r:=r) (d:=d) tiles C q).N.internal
  have hl (i : Fin r) : f (i.castAdd e) = 2^(b+(e*d+e*d)) :=
    (congrArg (fun x : Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.internal) (pieces_left (b:=b) (e:=e) (r:=r) (d:=d) tiles C i)).trans (ConstantKernelLUT.network_internal _)
  have hr (a : Fin e) : f (Fin.natAdd r a) = C.internal :=
    congrArg (fun x : Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d)) => x.N.internal) (pieces_right (b:=b) (e:=e) (r:=r) (d:=d) tiles C a)
  rw [Fin.sum_univ_add f]
  simp only [hl,hr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

/-- Evaluating the joint descriptor guesses the two physical arrays once.
Each compactor and local tile reads its prescribed affine-indexed slice. -/
theorem network_eval (tiles : Fin r → (Fin (b+(e*d+e*d)) → Bool) → F)
    (C : BitNetwork F ((r*d)+(r*d+r*d))) (head : Fin r → Fin b → Bool)
    (supply : Fin e → Fin (r*d) → Bool) :
    (network tiles C).eval (arguments head supply) =
      ∑ M : Fields r e d, ∑ D : Fields r e d,
        (∏ i, tiles i (Fin.append (head i) (Fin.append (copyPayload M i) (copyPayload D i)))) *
        ∏ a, C.eval (Fin.append (blocks r d (M a)) (Fin.append (blocks r d (D a)) (supply a))) := by
  unfold network
  rw [BitNetwork.Ordered.glue_eval, ← (privateFields r e d).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro M _
  apply Finset.sum_congr rfl
  intro D _
  let score (X : Piece F (e*(r*d)+e*(r*d)) (r*b+e*(r*d))) := X.N.eval (fun j => (X.wire j).read (privateFields r e d (M,D)) (arguments head supply))
  let f (t : Fin (r+e)) := score (pieces (b:=b) (e:=e) (r:=r) (d:=d) tiles C t)
  have hl (i : Fin r) : f (i.castAdd e) = tiles i (Fin.append (head i) (Fin.append (copyPayload M i) (copyPayload D i))) := by
    change score _ = _
    rw [pieces_left (b:=b) (e:=e) (r:=r) (d:=d) tiles C i]
    change (ConstantKernelLUT.network (tiles i)).eval _ = _
    rw [ConstantKernelLUT.network_eval,tile_read]
  have hr (a : Fin e) : f (Fin.natAdd r a) = C.eval (Fin.append (blocks r d (M a)) (Fin.append (blocks r d (D a)) (supply a))) := by
    change score _ = _
    rw [pieces_right (b:=b) (e:=e) (r:=r) (d:=d) tiles C a]
    exact congrArg C.eval (stream_read head supply M D a)
  rw [Fin.prod_univ_add f]
  simp only [hl,hr]

end ThreeFlat.Diagonal.MotifOrderedCells

end OAI
