import OAI.Computability.IntegerMultiplication.Loom.Horizon

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Loom
open Net IntegerMultiplication.Port Matrix Finset Strip Optic Dims Adic
variable (J W L : Type) [DecidableEq J] [Fintype J] [Fintype W]
abbrev dim (T : Type) [Fintype T] := Fintype.card T
structure Passage (p : ℕ) (f : J ≃ Fin (dim J)) (M : (j:ℕ) → Matrix J J (Tower p j)) (quota : ℤ) where
  moves : List (Lag J p)
  ok : ∀ v∈moves,v.legal (ranking f)
  paid : ((moves.map Lag.prices).sum:ℤ) ≤ quota
  goal j x : moves.foldl (Lag.fire j) x = Net.Shuttle.Rank.shear (M j) x

/-- Tune any number of bits along each role stream. -/
structure Design (p : ℕ) (discount : ℝ) where
  large : 2≤p
  occupancy : 2≤dim J
  roles : 1≤dim W
  order : J≃Fin (dim J)
  train : Circuit W L
  face : (j:ℕ)→L→Matrix J J (Tower p j)
  way : L→L→Prop
  quota : L→L→ℤ
  curve l k : way l k → Nonempty (Passage J p order (fun j => face j k-face j l) (quota l k))
  assigned : train.smooth way
  polite : train.ok
  route : W ≃ W
  arrived (x : W→ZMod 2) w : train.logical 0 x (route w)=x w
  ascend j (w : W) : face j (train.sink (route w))-face j (train.init w)=1
  saved : ((∑ w:W, train.cost (fun _ => quota) w : ℤ) : ℝ)/dim W < (dim J:ℝ)^discount

-- certificate amount converts to #calls
namespace Design
open Circuit
noncomputable section
variable {J W L} {p j : ℕ} {discount : ℝ} (d : Design J W L p discount)
variable {P G B : Tape}
def path (l k : L) (x : d.way l k) :=
  Classical.choice (d.curve _ _ x)
include d
theorem shape [NeZero p]
    (v : W→Keys P G B J (Block p j)→ZMod 2) (w : W) :
    d.train.physical (breath (d.face j) _ _ _ (ZMod 2)) 0 v (d.route w) =
      travel (tide (1:Matrix J J (Tower p j)) ..) (v w) := by
  rw [endpoint d.train d.polite _ _ _ (fun _ => (1:ZMod 2))
    (by intro a q; rw [one_mul,d.arrived])]
  change (fun y => 1 * ((breath ..).act _ _ y)) = _ -- cannot infer implicit?
  rw [undulate,d.ascend]
  simp

theorem extGate [NeZero p] (l : W→L) (a : Hop W L)
    (v : W→Keys P G B J (Block p j)→ZMod 2) (w : W) :
    Circuit.edges l a.label (breath (d.face j) _ _ _ (ZMod 2)) v w =
    travel (tide (d.face j (a.label w)-d.face j (l w)) ..) (v w) :=
  undulate _ _ _ _

open Net.Shuttle
def laced : Design Point FPbit Mark base Net.Motif.sigma := by
  classical
  let f := Fintype.equivFin Point
  refine {
    large := base_large.le
    occupancy := by rw [dim,volume]; norm_num [Motif.radix]
    roles := by
      let : Nonempty Motif.Piece := Shuttle.pieces
      let a : Motif.Piece := Classical.arbitrary _
      exact Fintype.card_pos_iff.mpr (Nonempty.intro (Sum.inl fun _ => a))
    order := f
    train := circuit
    face := deck
    way := Motif.Place.road align
    quota := allow
    curve := ?_
    assigned := smooth
    polite := ok
    route := Motif.Carnival.route
    arrived := exchange
    ascend := flowEnds
    saved := bound }
  intro l k e
  obtain ⟨z,v,g,t⟩ := choiceSchedule l k (ranking f) (well f) e
  exact ⟨⟨z,v,g,t⟩⟩
end
end Design
end Loom

end IntegerMultiplication
end Computability
end OAI
