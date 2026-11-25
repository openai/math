import OAI.Hierarchy.ProbeStagePrefixMemory
import OAI.Hierarchy.ProbeStageRowNative

namespace OAI
/-! # The mixed-radix group numbering is independent of the routed permutation -/

namespace Hierarchy.ProbeStage.Native
open scoped Fin.CommRing
noncomputable section

def numberedOuter {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (j : Fin (rounds d)) (forward : Bool) : Matching (2^h) :=
  let p := history h d π j.val
  let a := assigned j π
  let tiles := if forward then enter p.tiles (radix_pos h d) a else exitStage p.tiles (radix_pos h d) a
  {shape := ⟨p.shape.Group×Fin (blocks p.shape.span (radix h d)),radix h d*quota (radix h d)⟩
   count := p.count * blocks p.shape.span (radix h d)
   encode := innerEncode p.encode
   tiles := tiles}

def stageMatching {h d : ℕ} (π : Equiv.Perm (Fin (2^h))) (s : Fin (2*rounds d+1)) : Matching (2^h) :=
  if left : s.val<rounds d then numberedOuter (d:=d) π ⟨s.val,left⟩ true
  else if center : s.val=rounds d then history h d π (rounds d)
  else numberedOuter (d:=d) π ⟨2*rounds d-s.val,by omega⟩ false

def fieldNumber {n : ℕ} (p : Matching n) (r : Fin n) : Fin 3 → ℕ :=
  ![(p.encode (p.tiles.group r)).val,(p.tiles.input r).val,(p.tiles.output r).val]

/-- All data specifying the numeric group column, without the tile assignment. -/
structure GroupNumbering where
  shape : Shape
  count : ℕ
  encode : shape.Group ↪ Fin count

def groupFormat {n : ℕ} (p : Matching n) : GroupNumbering := ⟨p.shape,p.count,p.encode⟩

private def innerFormat (B : ℕ) (p : GroupNumbering) : GroupNumbering :=
  ⟨⟨p.shape.Group × Fin B,innerSize p.shape.span B⟩,p.count*B,innerEncode p.encode⟩

private def outerFormat (B : ℕ) (p : GroupNumbering) : GroupNumbering :=
  ⟨⟨p.shape.Group × Fin (blocks p.shape.span B),B*quota B⟩,p.count*blocks p.shape.span B,
    innerEncode p.encode⟩

theorem history_numbering {h d : ℕ} (π ρ : Equiv.Perm (Fin (2^h))) (j : ℕ) :
    groupFormat (history h d π j)=groupFormat (history h d ρ j) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (innerFormat (radix h d)) ih

theorem stage_numbering {h d : ℕ} (π ρ : Equiv.Perm (Fin (2^h))) (s : Fin (2*rounds d+1)) :
    groupFormat (stageMatching π s)=groupFormat (stageMatching ρ s) := by
  unfold stageMatching
  split
  · exact congrArg (outerFormat (radix h d)) (history_numbering π ρ _)
  · split
    · exact history_numbering π ρ _
    · exact congrArg (outerFormat (radix h d)) (history_numbering π ρ _)

/-- View the emitted mixed-radix number as an equivalence on any equal public stage shape. -/
def GroupNumbering.onShape (x : GroupNumbering) (s : Shape) (same : x.shape=s)
    (count : x.count=Fintype.card s.Group) : s.Group ≃ Fin (Fintype.card s.Group) :=
  let emb := (Equiv.cast (congrArg Shape.Group same).symm).toEmbedding.trans
    (x.encode.trans (finCongr count).toEmbedding)
  Equiv.ofBijective emb ((Fintype.bijective_iff_injective_and_card _).2 ⟨emb.injective,by simp⟩)

theorem GroupNumbering.number_val (x : GroupNumbering) (count : x.count=Fintype.card x.shape.Group)
    (g : x.shape.Group) : ((x.onShape x.shape rfl count) g).val=(x.encode g).val := rfl

theorem GroupNumbering.onShape_congr {x y : GroupNumbering} (eqn : x=y) (s : Shape)
    (hx : x.shape=s) (hy : y.shape=s) (cx : x.count=Fintype.card s.Group)
    (cy : y.count=Fintype.card s.Group) : x.onShape s hx cx=y.onShape s hy cy := by
  cases eqn
  rfl

end
end Hierarchy.ProbeStage.Native

end OAI
