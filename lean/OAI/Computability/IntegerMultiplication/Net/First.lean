import OAI.Computability.IntegerMultiplication.Net.Rational

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Shuttle
open Finset Matrix Motif Carnival Tensor Halo
abbrev Point := S → Core
abbrev FPbit := Bank Piece Core
abbrev Mark := Place Piece

theorem volume : Fintype.card Point = radix := by simp [Point,Core,S,radix]

theorem pieces : Nonempty Piece := Fintype.card_pos_iff.mp (by rw [v]; omega)

def circuit : Circuit FPbit Mark := net (Triple.bit)
abbrev align (a b : Piece) : Prop := Triple.bit.near a b = true
abbrev allow : Mark → Mark → ℤ := Place.allowance 100
def addressFrame (m : Mark) : Mat Point ℚ := directionQ Triple.rational m
theorem ok : circuit.ok := ok_net _ Triple.bit_near_symm
theorem smooth : circuit.smooth (Place.road align) := smooth_net _

theorem usage (a b : Mark) (x : Place.road align a b) : ∃ l : List (Outer Point ℚ),
    addressFrame b - addressFrame a = (l.map value).sum ∧ (l.length : ℤ) ≤ allow a b := by
  by_cases e : a=b
  · subst a
    exact ⟨[],by simp,by simp⟩
  let : Nonempty Piece := pieces
  have g : ∀ t u, align t u → t≠u := by
    rintro t u n q; subst u; simp [align, Triple.bit] at n
  have hs := Or.resolve_left
    (Halo.passes Triple.rational (fun _ => True) align (Triple.ratPermission) g a b x) e
  simpa only [addressFrame, Core, allow,Fintype.card_fin, Nat.cast_ofNat] using
    (release_order Triple.rational a b hs (notOpening a b x e))

theorem exchange (y : FPbit → ZMod 2) (w : FPbit) :
    circuit.logical 0 y (route w) = y w := by
  rw [circuit, run_net (Triple.bit) (0:ZMod 2) (Triple.bit_good _ (by decide))]
  rcases w with _|_|⟨_,_⟩
  all_goals exact one_mul _

theorem terminals (w : FPbit) :
    addressFrame (circuit.sink (route w)) - addressFrame (circuit.init w) = 1 := by
  rw [circuit, sink_net, init_net]
  rcases w with a|a|⟨j,p,k⟩
  · change directionQ Triple.rational (.ybox 3 a) -
      directionQ Triple.rational (.opening a) = 1
    simp [directionQ, Place.isOp, operator]
  · change directionQ Triple.rational (.box 3 a) -
      directionQ Triple.rational (.ybox 0 a) = 1
    simp [directionQ, Place.isOp, operator]
  · have hj : j.val < 3 := j.isLt
    change directionQ Triple.rational (if j.val < 3 then .full else .clear) -
      directionQ Triple.rational (if j.val < 0 then .full else .clear) = 1
    simp [directionQ, Place.isOp, operator, hj]

theorem bound :
    ((∑ w : FPbit, circuit.cost (fun _ => allow) w : ℤ) : ℝ) / Fintype.card FPbit <
      (Fintype.card Point : ℝ)^Motif.sigma := by
  rw [volume]
  exact gap (C:=Core) (by simp [Core]) (Triple.bit)
end Net.Shuttle

end IntegerMultiplication
end Computability
end OAI
