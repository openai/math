import OAI.ThreeFlat.Diagonal.CompressorDenseMotifs

namespace OAI
/-! # Branch-independent lengths of all shrinking-stage spans -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.Compression

structure Dimensions where
  oldBase : ℕ
  oldDegree : ℕ
  colorBits : ℕ
  tagRadix : ℕ
  residual : ℕ
  newDegree : ℕ
  deriving DecidableEq

def Dimensions.oldEdges (x : Dimensions) := x.oldBase*x.oldDegree
def Dimensions.upperBlocks (x : Dimensions) := x.oldEdges*x.residual*x.tagRadix*x.oldDegree
def Dimensions.motifs (x : Dimensions) := x.upperBlocks*(3*2^(x.colorBits-2))
def Dimensions.originalLanes (x : Dimensions) := x.residual*x.tagRadix*x.oldDegree*2^x.colorBits
def Dimensions.originalSites (x : Dimensions) := x.oldBase*x.originalLanes
def Dimensions.newBase (x : Dimensions) := x.oldBase*x.tagRadix
def Dimensions.newEdges (x : Dimensions) := x.newBase*x.newDegree
def Dimensions.outputSites (x : Dimensions) := x.newBase*x.residual

/-- Pointer-valued fields supplied by the chronological bump allocator. -/
structure Pointers where
  counts : ℕ
  choices : ℕ
  supply : ℕ
  next : ℕ
  firstId : ℕ
  demands : ℕ
  oldGraph : ℕ
  oldWidths : ℕ
  split : ℕ
  colors : ℕ
  offsets : ℕ
  newGraph : ℕ
  keys : ℕ
  newWidths : ℕ
  costs : ℕ
  ownHeader : ℕ

/-- Static offsets 0--33, with the elected layout initialized to zero. -/
def headerWord (x : Dimensions) (p : Pointers) : ℕ → ℕ
  | 0 => x.motifs | 1 => p.counts | 2 => p.choices | 3 => p.supply
  | 4 => p.next | 5 => x.originalSites | 6 => p.firstId
  | 8 => p.demands | 9 => 2*x.motifs
  | 10 => x.oldBase | 11 => p.oldGraph | 12 => x.oldEdges | 13 => p.oldWidths
  | 14 => x.residual | 15 => x.tagRadix | 16 => p.split | 17 => 8*x.oldEdges
  | 18 => p.colors | 19 => p.offsets | 20 => p.newGraph | 21 => 6*x.newEdges
  | 22 => x.newEdges | 23 => p.keys | 24 => p.newWidths | 25 => x.newEdges*x.residual
  | 26 => x.originalLanes | 28 => 3*x.motifs | 29 => 8*x.motifs
  | 30 => p.costs | 31 => 2*(x.motifs+1) | 32 => p.ownHeader+27 | 33 => 1
  | _ => 0

theorem dimensions_exact {B H Tag L : Type*} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
    {N d c J R D : ℕ} (P : PackingData B H Tag L d c) (b : B ≃ Fin N) (tag : Tag ≃ Fin J)
    (lane : L ≃ Fin R) (hc : 2≤c) [Fintype B] [Fintype H] [Fintype Tag] [Fintype L] :
    Fintype.card P.Motif = (Dimensions.mk N d c J R D).motifs := by
  rw [Fintype.card_congr (denseMotifRow P b tag lane hc),Fintype.card_fin]
  rfl

def Dimensions.preLengths (x : Dimensions) :=
  [8*x.oldEdges,x.oldBase,x.oldBase,x.oldBase,x.oldBase,2*x.motifs]
def Dimensions.postLengths (x : Dimensions) := [6*x.newEdges,x.newEdges,x.newEdges*x.residual]

/-- A constant multiple of the number of original sites bounds every span,
with coefficient depending on old and new degree only. -/
theorem span_extent (x : Dimensions) (hd : 0<x.oldDegree) (hj : 0<x.tagRadix) (hr : 0<x.residual) :
    let q := x.originalSites*(8*x.oldDegree+6*x.newDegree+6)
    ∀ n ∈ x.preLengths++x.postLengths, n≤q := by
  have bits : 0<2^x.colorBits := Nat.two_pow_pos _
  have fewer : 2^(x.colorBits-2) ≤ 2^x.colorBits :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hb : x.oldBase ≤ x.originalSites := Nat.le_mul_of_pos_right _ (by
    unfold Dimensions.originalLanes
    positivity)
  have hn : x.newEdges*x.residual ≤ x.originalSites*x.newDegree := by
    dsimp [Dimensions.newEdges,Dimensions.newBase,Dimensions.originalSites,Dimensions.originalLanes]
    calc
      _ = (x.oldBase*(x.residual*x.tagRadix))*x.newDegree := by ring
      _ ≤ _ := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact (Nat.le_mul_of_pos_right _ hd).trans (Nat.le_mul_of_pos_right _ bits)
  have he : x.newEdges ≤ x.newEdges*x.residual := Nat.le_mul_of_pos_right _ hr
  have hm : 2*x.motifs ≤ x.originalSites*(6*x.oldDegree) := by
    unfold Dimensions.motifs Dimensions.upperBlocks Dimensions.oldEdges Dimensions.originalSites Dimensions.originalLanes
    calc
      _ = (x.oldBase*x.oldDegree*x.residual*x.tagRadix*x.oldDegree*6)*2^(x.colorBits-2) := by ring
      _ ≤ _ := (Nat.mul_le_mul_left _ fewer).trans_eq (by ring)
  intro q n h
  have cost (k : ℕ) (hk : k ≤ 8*x.oldDegree+6*x.newDegree+6) :
      x.originalSites*k ≤ q := Nat.mul_le_mul_left _ hk
  have baseCost : x.oldBase ≤ q := hb.trans (by simpa using cost 1 (by omega))
  have motifCost := hm.trans (cost _ (by omega))
  have widthCost := hn.trans (cost _ (by omega))
  have edgeCost := he.trans widthCost
  have graphCost : 6*x.newEdges ≤ q := calc
    _ ≤ 6*(x.originalSites*x.newDegree) := Nat.mul_le_mul_left _ (he.trans hn)
    _ = x.originalSites*(6*x.newDegree) := by ring
    _ ≤ q := cost _ (by omega)
  have splitCost : 8*x.oldEdges ≤ q := calc
    _ ≤ 8*(x.originalSites*x.oldDegree) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hb)
    _ = x.originalSites*(8*x.oldDegree) := by ring
    _ ≤ q := cost _ (by omega)
  simp only [Dimensions.preLengths,Dimensions.postLengths,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with (rfl|rfl|rfl|rfl|rfl|rfl) | (rfl|rfl|rfl) <;> assumption

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
