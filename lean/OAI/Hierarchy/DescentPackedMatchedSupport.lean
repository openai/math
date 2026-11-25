import OAI.Hierarchy.DescentPackedMatchedInput
import OAI.Hierarchy.DescentPositiveAperture
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # Occupied target geometry preserves the true positive first-fit order -/

namespace Hierarchy.DescentPacking.PackedMatch.Local
open scoped Classical
noncomputable section
variable {E U C V : Type*} [Fintype E] [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]
variable {r D p digit : ℕ}

def frequency {Z : Type*} (key : E→Z) (z : Z) := Fintype.card {e : E // key e=z}

private theorem frequency_pos_iff {Z : Type*} (key : E → Z) (z : Z) :
    0 < frequency key z ↔ Nonempty {e : E // key e = z} := by
  unfold frequency
  exact Fintype.card_pos_iff

private theorem frequency_eq_of_fibers {Z Z' : Type*} (key : E → Z) (key' : E → Z') (z : Z) (z' : Z')
    (h : ∀ e, key e = z ↔ key' e = z') : frequency key z = frequency key' z' := by
  unfold frequency
  exact Fintype.card_congr (Equiv.subtypeEquivRight h)

/-- Name the nonempty fibers of the same real occurrence inventory in two
orders. Repeated parallel cables supply separate occurrences on both sides. -/
def from_occurrences (tag : E→C) (slot : E→V)
    (mono : ∀x y : E,PositiveAperture.rank (tag x)<PositiveAperture.rank (tag y) ↔
      PositiveAperture.rank (slot x)<PositiveAperture.rank (slot y)) :
    PositiveAperture.Map (frequency tag) (frequency slot) := by
  classical
  have same (x y : E) : tag x=tag y ↔ slot x=slot y := by
    have old : Function.Injective (PositiveAperture.rank (T:=C)) := fun _ _ h=>(Fintype.equivFin C).injective (Fin.ext h)
    have new_ : Function.Injective (PositiveAperture.rank (T:=V)) := fun _ _ h=>(Fintype.equivFin V).injective (Fin.ext h)
    constructor
    · intro h
      apply new_
      apply Nat.le_antisymm <;> apply Nat.le_of_not_gt
      · intro hlt;have bad := (mono y x).mpr hlt;rw [h] at bad;exact (lt_irrefl _) bad
      · intro hlt;have bad := (mono x y).mpr hlt;rw [h] at bad;exact (lt_irrefl _) bad
    · intro h
      apply old
      apply Nat.le_antisymm <;> apply Nat.le_of_not_gt
      · intro hlt;have bad := (mono y x).mp hlt;rw [h] at bad;exact (lt_irrefl _) bad
      · intro hlt;have bad := (mono x y).mp hlt;rw [h] at bad;exact (lt_irrefl _) bad
  let old (u : {c // 0<frequency tag c}) : {e : E // tag e = u.val} :=
    ((frequency_pos_iff tag u.val).mp u.property).some
  let new_ (v : {j // 0<frequency slot j}) : {e : E // slot e = v.val} :=
    ((frequency_pos_iff slot v.val).mp v.property).some
  let forward (u : {c // 0<frequency tag c}) : {j // 0<frequency slot j} :=
    ⟨slot (old u).val,(frequency_pos_iff slot _).mpr ⟨⟨(old u).val,rfl⟩⟩⟩
  let backward (v : {j // 0<frequency slot j}) : {c // 0<frequency tag c} :=
    ⟨tag (new_ v).val,(frequency_pos_iff tag _).mpr ⟨⟨(new_ v).val,rfl⟩⟩⟩
  let equiv : {c // 0<frequency tag c} ≃ {j // 0<frequency slot j} :=
    ⟨forward,backward,fun u=>Subtype.ext (((same _ _).mpr (new_ (forward u)).property).trans (old u).property),
      fun v=>Subtype.ext (((same _ _).mp (old (backward v)).property).trans (new_ v).property)⟩
  refine ⟨equiv,?_,?_⟩
  · intro c
    apply frequency_eq_of_fibers slot tag (slot (old c).val) c.val
    intro x
    calc
      slot x = slot (old c).val ↔ tag x = tag (old c).val := (same x (old c).val).symm
      _ ↔ tag x = c.val := by rw [(old c).property]
  · intro c d
    change _ ↔ PositiveAperture.rank (slot (old c).val)<PositiveAperture.rank (slot (old d).val)
    rw [←mono,(old c).property,(old d).property]

/-- A gathered neighbor-panel from the real actor raster, with physical site
order and the heap address read at each active lane. `fiber` states that a
colony in a neighbor host lives wholly in that host's old block interval. -/
structure Places (u : Panel r D p digit) (row : U↪ℕ) (home : U→C) where
  actor : Fin D→Fin r→Option U
  active : ∀v x,u.peerWinner v x≠0 ↔ (actor v x).isSome
  sameLeaf : ∀v x y a b,actor v x=some a→actor v y=some b→
    (leaf (u.peerWinner v x).val=leaf (u.peerWinner v y).val ↔ home a=home b)
  fiber : ∀v x a b,actor v x=some a→home b=home a→∃y,actor v y=some b
  order : ∀v x a v' y b,actor v x=some a→actor v' y=some b→
    (row a<row b ↔ v.val*r+x.val<v'.val*r+y.val)

variable {u : Panel r D p digit} {row : U↪ℕ} {home : U→C}

omit [Fintype C] [DecidableEq C] in
theorem Places.minimum (h : Places u row home) (surj : Function.Surjective home) (v : Fin D) (x : Fin r) (a : U)
    (appears : h.actor v x=some a) : ∃m : Fin r,∃z,h.actor v m=some z ∧ m.val=first u v x ∧
      home z=home a ∧ row z=DescentPhysicalOrder.first row home surj (home a) := by
  have alive : u.peerWinner v x≠0 := (h.active v x).mpr (by simp [appears])
  obtain ⟨⟨m,eqn,present,heap⟩,_⟩ := first_live u v x alive
  obtain ⟨z,there⟩ := Option.isSome_iff_exists.mp ((h.active v m).mp present)
  have group := (h.sameLeaf v m x z a there appears).mp heap
  obtain ⟨b,gb,earliest⟩ := DescentPhysicalOrder.first_at row home surj (home a)
  obtain ⟨y,atY⟩ := h.fiber v x a b appears gb
  have heapY := (h.sameLeaf v y x b a atY appears).mpr gb
  have bound : m.val≤y.val := by
    rw [eqn,first_same u v x y heapY.symm]
    exact (first_live u v y ((h.active v y).mpr (by simp [atY]))).2
  have prior : row z≤row b := Nat.le_of_not_gt (fun bad=>by
    have bad' := (h.order v y b v m z atY there).mp bad
    omega)
  have lower := DescentPhysicalOrder.first_le row home surj z
  rw [group] at lower
  exact ⟨m,z,there,eqn,group,Nat.le_antisymm (prior.trans earliest.le) lower⟩

omit [DecidableEq C] in
theorem Places.ordered (h : Places u row home) (surj : Function.Surjective home)
    (typed : ∀a b,PositiveAperture.rank a<PositiveAperture.rank b ↔
      DescentPhysicalOrder.first row home surj a<DescentPhysicalOrder.first row home surj b)
    {v z : Fin D} {x y : Fin r} {a b : U} (atX : h.actor v x=some a) (atY : h.actor z y=some b) :
    PositiveAperture.rank (home a)<PositiveAperture.rank (home b) ↔ bin u v x<bin u z y := by
  obtain ⟨i,a',ar,ax,_,amin⟩ := h.minimum surj v x a atX
  obtain ⟨j,b',br,by_,_,bmin⟩ := h.minimum surj z y b atY
  rw [typed,←amin,←bmin,h.order v i a' z j b' ar br,ax,by_]
  unfold bin
  omega

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
