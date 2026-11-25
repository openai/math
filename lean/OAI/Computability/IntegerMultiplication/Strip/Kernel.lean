import OAI.Computability.IntegerMultiplication.Strip.Lens
import OAI.Computability.IntegerMultiplication.Net.Second

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Net Finset Matrix -- Tensor nested
namespace Optic
open Net.Shuttle Net.Walsh Net.Tensor
variable {O J N K R : Type} [Fintype J] [Fintype N] [DecidableEq J] [DecidableEq N] [CommRing R]
-- address column interface; as fixed number m basis coordinates and f columns, K spectator
abbrev Batch (N J : Type) := N → Addr J
abbrev Layout (O N J K : Type) := Lens O (Batch N J) K
abbrev broadcast (M : Mat (Addr J) R) : Mat (Batch N J) R :=
  mat (fun _ : N => M)
variable (l : Layout O N J K)
def pipe (M : Mat (Addr J) R) := operate l (broadcast M)
theorem pipe_mul (M S : Mat (Addr J) R) (x : O→R) :
    pipe l M (pipe l S x) = pipe l (M*S) x := by
  rw [pipe,pipe,dot,broadcast,broadcast,multiply]
  rfl
@[simp] theorem pipe_one : pipe l (1 : Mat (Addr J) R) = id := by
  rw [pipe,broadcast,Net.Tensor.unit, Optic.one]

theorem input_scale (M : Mat (Addr J) R) (x : O→R) (r : R) :
    pipe l M (r • x) = r • pipe l M x := by
  funext i
  unfold pipe operate everywhere beamAll attach fiber
  -- change fibers
  let k := (l i).2
  let y := fun t => x (l.symm (t,k))
  change (broadcast M *ᵥ (r • y)) (l i).1 = (r • (broadcast M *ᵥ y)) (l i).1
  rw [Matrix.mulVec_smul]

theorem input_add (M : Mat (Addr J) R) (x y : O → R) :
    pipe l M (x+y) = pipe l M x + pipe l M y := by
  funext i
  let f := fun (x : O→R) => fun t => x (l.symm (t,(l i).2))
  change (broadcast M *ᵥ (f x + f y)) (l i).1 =
    (broadcast M *ᵥ f x + broadcast M *ᵥ f y) (l i).1
  rw [Matrix.mulVec_add]

variable {G : Type} (q : G → Addr J → Clock) (c : Quarter R)

def codec : Hop.Frames G O R where
  act m := {
    toFun := pipe l (oscillate c (q m))
    invFun := pipe l (oscillate c (-q m))
    left_inv := fun w => by rw [pipe_mul, osc_add,neg_add_cancel,osc_zero, pipe_one]; rfl
    right_inv := fun w => by rw [pipe_mul, osc_add,add_neg_cancel,osc_zero,pipe_one]; rfl }
  add _ := input_add l _
  scale _ r f := input_scale l _ f r

@[simp] theorem advance (a b : G) (x : O→R) :
    (codec l q c).act b (((codec l q c).act a).symm x) =
      pipe l (oscillate c (q b - q a)) x := by
  exact (pipe_mul ..).trans (by rw [Net.Walsh.between ..])

-- actual directional factors
theorem used (s : Stamp J) :
    oscillate c (bill s) = kernel c s.night s.v := by
  cases e : s.night
  · unfold bill; rw [e]
    exact (kernel_osc c 1 (Or.inl rfl) s.v)
  have r := kernel_osc c (-1:Clock) (Or.inr rfl) s.v
  unfold bill; rw [e]
  simpa (config := {decide:=true}) using r

def gateplay (x : O→R) (s : Stamp J) : O→R := pipe l (kernel c s.night s.v) x

theorem play (u : List (Stamp J)) (x : O→R) :
    u.foldl (gateplay l c) x =
      pipe l (oscillate c ((u.map bill).sum)) x := by
  induction u generalizing x with
  | nil =>
    simp only [List.map_nil,List.sum_nil,List.foldl_nil,osc_zero,pipe_one,id_eq]
  | cons a t ih =>
    rw [List.map_cons, List.sum_cons, List.foldl_cons, ih,gateplay,← used, pipe_mul,
      osc_add, add_comm]

end Optic

namespace Permit
open Net.Tensor Net.Shuttle Net.Walsh Net.Motif Net.Motif.Carnival Optic
variable {O N K R : Type} [DecidableEq N] [Fintype N] [CommRing R] (l : Layout O N Point K)
variable (c : Quarter R)
/-- frame implementation for stage pipeline on any selected wire address (including
spectator records or intra-record word position). Before frame network input add Z
sign tracks as needed; physical output is signed. -/
def clockOut (x : FPclock → O → R) : FPclock → O → R :=
  cycle.physical (codec l addressPhase c) c.half x

abbrev targets (w : FPclock) (j : Point) := decide (witness w j ≠ 0)
theorem far (x : FPclock → O → R) (w : FPclock) :
    clockOut l c x (route w) =
      (sign w:R) • pipe l (allC c (targets w)) (x w) := by
  unfold clockOut
  rw [Circuit.endpoint cycle trust _ c.half route _ (signed c) x w]
  simp_rw [Optic.advance,profile, prism]
  rfl

-- sign corrections efficiently
def vst (w : FPclock) : Walsh.Field Point R :=
  Matrix.diagonal (swapSignVec (targets w))

theorem slow (r : R) (M : Walsh.Field Point R) (x : O→R) :
    pipe l (r • M) x = (r^Fintype.card N) • pipe l M x := by
  unfold pipe broadcast
  rw [combine_scale, Finset.prod_const, Finset.card_univ, Optic.scale]

theorem repaired (x : FPclock → O→R) (w : FPclock) :
    (sign w:R) •
      pipe l ((pack c (targets w)) • vst w)
        (clockOut l c (fun u => pipe l (vst u) (x u)) (route w))
        =
      pipe l (allC c (fun _ => false)) (x w) := by
  have t : (sign w:R)*sign w = 1 := by unfold sign; split <;> simp
  rw [far, input_scale, smul_smul, t, one_smul, pipe_mul, pipe_mul, Matrix.smul_mul,
    Matrix.smul_mul]
  exact congrArg (fun m : Walsh.Field Point R => pipe l m (x w)) (wrap c (targets w))
end Permit
end Strip

end IntegerMultiplication
end Computability
end OAI
