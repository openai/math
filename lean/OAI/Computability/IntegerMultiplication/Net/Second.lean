import OAI.Computability.IntegerMultiplication.Net.First
import OAI.Computability.IntegerMultiplication.Net.Stamp

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Shuttle
open Finset Matrix Motif Carnival Tensor Halo Walsh
abbrev FPclock := Bank Piece (Core⊕Fin 1)
def cycle : Circuit FPclock Mark := net (Triple.phase)
abbrev adapt (a b : Piece) : Prop := Triple.phase.near a b = true
def addressPhase := standing (Triple.binary (J:=Core))
theorem trust : cycle.ok := ok_net _ Triple.phase_near_symm
theorem quiet : cycle.smooth (Place.road adapt) := smooth_net _

theorem howMany (a b : Mark) (x : Place.road adapt a b) :
    ∃ l : List (Stamp Point),
      (l.map bill).sum = addressPhase b - addressPhase a ∧
        (∀ s∈l, s.v ⬝ᵥ s.v=1) ∧
        (l.length : ℤ) ≤ allow a b := by
  by_cases e : a=b
  · subst a
    exact ⟨[],by simp,by simp,by simp⟩
  let : Nonempty Piece := pieces
  have g : ∀ t u, adapt t u → t≠u := by
    rintro t u n rfl
    simp [adapt, Triple.phase] at n
  have hs := Or.resolve_left
    (Halo.passes Triple.binary (fun Z => Z.pull=Z.push.transpose) adapt
      (Triple.binPermission (by simp [Core])) g a b x) e
  simpa only [addressPhase, Core, allow,Fintype.card_fin,Nat.cast_ofNat] using
    (advance Triple.binary a b hs)

variable {R : Type} [CommRing R]
theorem signed (c : Quarter R) (y : FPclock → R) (w : FPclock) :
    cycle.logical c.half y (route w) = sign w * y w :=
  run_net Triple.phase _ (Triple.phase_good _ c.two) y w

def rayQ (a : Keys Piece) : Addr Point := Tensor.vec (fun j => Triple.oneIn B (a j))
theorem opener (a : Keys Piece) :
    proj Triple.binary 0 a = Matrix.vecMulVec (rayQ a) (rayQ a) := by
  rw [rayQ, proj, Tensor.Plate.cube, ← Tensor.outer]
  congr 1

def witness (w : FPclock) : Addr Point :=
  match w with
  | .inl a => rayQ a
  | _ => 0

-- direct exceptional phase calculation (even works without norm assumptions)
theorem splitRay (a : Keys Piece) (z : Addr Point) :
    weight ((1 - proj Triple.binary 0 a) *ᵥ z) - weight ((proj Triple.binary 0 a) *ᵥ z) =
    tint (rayQ a) z := by
  rw [opener, sub_mulVec, one_mulVec,outer_apply]
  unfold tint
  have e : ∀ v : Addr Point, z-v=z+v := by intro v; rw [sub_eq_add_neg,Walsh.neg_eq]
  rw [e, plus,dotProduct_smul, dotProduct_comm z,smul_eq_mul]
  rcases bit_value (rayQ a ⬝ᵥ z) with h|h <;> simp [h]
  abel

theorem profile (w : FPclock) :
    addressPhase (cycle.sink (route w)) - addressPhase (cycle.init w) = tint (witness w) := by
  rw [cycle,sink_net,init_net]
  funext x
  rcases w with a|a|⟨j,p,s⟩
  · change standing Triple.binary (.ybox 3 a) x -
      standing Triple.binary (.opening a) x = tint (rayQ a) x
    simpa [standing, operator] using (splitRay a x)
  · change standing Triple.binary (.box 3 a) x -
      standing Triple.binary (.ybox 0 a) x = tint 0 x
    simp [standing, operator, neutral]
  · have hj : j.val < 3 := j.isLt
    change standing Triple.binary (if j.val < 3 then .full else .clear) x -
      standing Triple.binary (if j.val < 0 then .full else .clear) x = tint 0 x
    simp [hj, standing, operator, neutral]

theorem price :
    ((∑ w : FPclock, cycle.cost (fun _ => allow) w : ℤ) : ℝ) / Fintype.card FPclock <
      (Fintype.card Point : ℝ)^Motif.sigma := by
  rw [volume]
  exact gap (C:=Core⊕Fin 1) (by norm_num [Core]) Triple.phase
end Net.Shuttle

end IntegerMultiplication
end Computability
end OAI
