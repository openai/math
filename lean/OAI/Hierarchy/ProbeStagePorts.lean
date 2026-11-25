import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace OAI
/-! # Fixed ports for a bounded-congestion subdivision of a permutation stage -/

namespace Hierarchy.ProbeStage

/-- All records occupy distinct input and output positions in their groups. -/
structure Tiles (R G : Type*) (m : ℕ) where
  group : R → G
  input : R → Fin m
  output : R → Fin m
  input_inj : Function.Injective (fun r => (group r,input r))
  output_inj : Function.Injective (fun r => (group r,output r))

def blockSize (B : ℕ) := B^9
def quota (B : ℕ) := 4 * B^8
def blocks (m B : ℕ) := m ⌈/⌉ blockSize B
def innerSize (m B : ℕ) := blocks m B * quota B

theorem blockSize_le_reserved (B : ℕ) : blockSize B ≤ B * quota B := by
  have eq : B * quota B = 4 * blockSize B := by unfold quota blockSize;ring
  rw [eq]
  omega

theorem blocks_cover (m B : ℕ) (positive : 0 < B) : m ≤ blocks m B * blockSize B := by
  have h : 0 < blockSize B := pow_pos positive _
  simpa only [Nat.mul_comm (blocks m B) (blockSize B)] using
    (ceilDiv_le_iff_le_mul h).mp (le_refl (blocks m B))

/-- Padded rows and their offsets. This embedding depends only on the length. -/
def decode (m B : ℕ) (positive : 0 < B) : Fin m ↪ (Fin (blocks m B) × Fin (blockSize B)) :=
  (Fin.castLEEmb (blocks_cover m B positive)).trans finProdFinEquiv.symm.toEmbedding

/-- A single choice of colors, with independently allocated ranks on both
sides. No rank can be reused in the same block and color. -/
structure Allocation {R L H : Type*} (B : ℕ) (left : R → L) (right : R → H) where
  color : R → Fin B
  enterRank : R → Fin (quota B)
  exitRank : R → Fin (quota B)
  enter_inj : Function.Injective (fun r => (left r,color r,enterRank r))
  exit_inj : Function.Injective (fun r => (right r,color r,exitRank r))

section Split
variable {R G : Type*} {m B : ℕ} (p : Tiles R G m) (pos : 0 < B)

def leftBlock (r : R) := (p.group r, (decode m B pos (p.input r)).1)
def rightBlock (r : R) := (p.group r, (decode m B pos (p.output r)).1)

/-- Source offsets within a block are distinct, so this block has at most
the fixed block size many records. -/
def leftBlockFiber (g : G × Fin (blocks m B)) :
    {r : R // leftBlock p pos r = g} ↪ Fin (blockSize B) where
  toFun r := (decode m B pos (p.input r.val)).2
  inj' := by
    intro x y off
    have block := x.property.trans y.property.symm
    have pair := Prod.mk.inj block
    exact Subtype.ext (p.input_inj (Prod.ext pair.1
      ((decode m B pos).injective (Prod.ext pair.2 off))))

/-- Destination offsets have the analogous block bound. -/
def rightBlockFiber (g : G × Fin (blocks m B)) :
    {r : R // rightBlock p pos r = g} ↪ Fin (blockSize B) where
  toFun r := (decode m B pos (p.output r.val)).2
  inj' := by
    intro x y off
    have block := x.property.trans y.property.symm
    have pair := Prod.mk.inj block
    exact Subtype.ext (p.output_inj (Prod.ext pair.1
      ((decode m B pos).injective (Prod.ext pair.2 off))))

variable (a : Allocation B (leftBlock p pos) (rightBlock p pos))

private def padded (B : ℕ) := Fin.castLEEmb (blockSize_le_reserved B)

/-- Passing from block-major to color-major indexing uses the same fixed
map for every matching. The inverse is the same coordinate exchange. -/
def join {G : Type*} (blocks B q : ℕ) :
    ((G × Fin blocks) × Fin (B*q)) ≃ ((G × Fin B) × Fin (blocks*q)) where
  toFun x := ((x.1.1,(finProdFinEquiv.symm x.2).1),
    finProdFinEquiv (x.1.2,(finProdFinEquiv.symm x.2).2))
  invFun x := ((x.1.1,(finProdFinEquiv.symm x.2).1),
    finProdFinEquiv (x.1.2,(finProdFinEquiv.symm x.2).2))
  left_inv := by
    rintro ⟨⟨g,b⟩,v⟩
    obtain ⟨⟨c,r⟩,rfl⟩ := finProdFinEquiv.surjective v
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨⟨g,b⟩,v⟩
    obtain ⟨⟨c,r⟩,rfl⟩ := finProdFinEquiv.surjective v
    simp only [Equiv.symm_apply_apply]

private theorem initial_inj (side : R → Fin m)
    (inj : Function.Injective (fun r => (p.group r,side r))) :
    Function.Injective (fun r => ((p.group r,(decode m B pos (side r)).1),
      padded B (decode m B pos (side r)).2)) := by
  intro x y eq
  have he := Prod.mk.inj eq
  have group := (Prod.mk.inj he.1).1
  have block := (Prod.mk.inj he.1).2
  have offset := (padded B).injective he.2
  exact inj (Prod.ext group ((decode m B pos).injective (Prod.ext block offset)))

private theorem packed_inj {L : Type*} (f : R → L) (c : R → Fin B) (v : R → Fin (quota B))
    (inj : Function.Injective (fun r => (f r,c r,v r))) :
    Function.Injective (fun r => (f r,finProdFinEquiv (c r,v r))) := by
  intro x y eq
  have he := Prod.mk.inj eq
  exact inj (Prod.ext he.1 (finProdFinEquiv.injective he.2))

/-- Input-side block move. -/
def enter : Tiles R (G × Fin (blocks m B)) (B*quota B) where
  group := leftBlock p pos
  input r := padded B (decode m B pos (p.input r)).2
  output r := finProdFinEquiv (a.color r,a.enterRank r)
  input_inj := initial_inj p pos p.input p.input_inj
  output_inj := packed_inj _ _ _ a.enter_inj

/-- Remaining matching on the shorter color-major lists. -/
def inner : Tiles R (G × Fin B) (innerSize m B) where
  group r := (p.group r,a.color r)
  input r := finProdFinEquiv ((decode m B pos (p.input r)).1,a.enterRank r)
  output r := finProdFinEquiv ((decode m B pos (p.output r)).1,a.exitRank r)
  input_inj := by
    intro x y he
    apply a.enter_inj
    have eq := Prod.mk.inj he
    have gc := Prod.mk.inj eq.1
    have br := Prod.mk.inj (finProdFinEquiv.injective eq.2)
    exact Prod.ext (Prod.ext gc.1 br.1) (Prod.ext gc.2 br.2)
  output_inj := by
    intro x y he
    apply a.exit_inj
    have eq := Prod.mk.inj he
    have gc := Prod.mk.inj eq.1
    have br := Prod.mk.inj (finProdFinEquiv.injective eq.2)
    exact Prod.ext (Prod.ext gc.1 br.1) (Prod.ext gc.2 br.2)

/-- Output-side block move. -/
def exitStage : Tiles R (G × Fin (blocks m B)) (B*quota B) where
  group := rightBlock p pos
  input r := finProdFinEquiv (a.color r,a.exitRank r)
  output r := padded B (decode m B pos (p.output r)).2
  input_inj := packed_inj _ _ _ a.exit_inj
  output_inj := initial_inj p pos p.output p.output_inj

theorem enter_join (r : R) : join (blocks m B) B (quota B)
    ((enter p pos a).group r,(enter p pos a).output r) = ((inner p pos a).group r,(inner p pos a).input r) := by
  simp only [enter,inner,leftBlock,join,Equiv.coe_fn_mk,Equiv.symm_apply_apply]; rfl

theorem exit_join (r : R) : join (blocks m B) B (quota B)
    ((exitStage p pos a).group r,(exitStage p pos a).input r) =
    ((inner p pos a).group r,(inner p pos a).output r) := by
  simp only [exitStage,inner,rightBlock,join,Equiv.coe_fn_mk,Equiv.symm_apply_apply]; rfl

end Split
end Hierarchy.ProbeStage

end OAI
