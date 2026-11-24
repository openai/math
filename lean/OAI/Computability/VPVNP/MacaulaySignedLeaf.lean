import OAI.Computability.VPVNP.MacaulayReadArms
import OAI.Computability.VPVNP.JointScalarLeaf

/-! # Installing the signed coefficient routine on the Macaulay reader bus -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.SignedLeaf

open RAMTape BurstRAM UniversalCountStack MacaulayRowDispatch
open RadicalCertificate.MonomialIndex

variable {K : Type}

/-- Row and exponent inputs refer directly to the caller's register and
buffer. The result port belongs to the enclosing matrix reader. -/
def ports (embed : JointScalar.Leaf.Port → K) (i : JointScalar.Leaf.Port) : Arms.Ports K :=
  if i = .row then route (.reg (outReg 1))
  else if i = .packed then Arms.slot false (.external .packed)
  else if i = JointScalar.Leaf.resultPort then .result
  else Arms.extra (.payload (embed i))

private theorem row_address : route (.reg (outReg 1)) = (.aux (.inl (.reg (outReg 1))) : Arms.Ports K) := by
  simp [route,outReg,inReg,Dispatch.Code.outReg,Dispatch.Code.inReg]

theorem ports_injective {embed : JointScalar.Leaf.Port → K} (hinj : Function.Injective embed) : Function.Injective (ports embed) := by
  intro i j h
  simp only [ports,row_address,Arms.slot,Arms.extra] at h
  split_ifs at h <;> first | contradiction | subst_vars; rfl | exact hinj (by simp at h <;> assumption)

/-- Preloaded private stacks, including the checker advice, width words and
field modulus. The three externally aliased ports require no payload. -/
def Loaded (L : JointScalar.Leaf.Layout) (embed : JointScalar.Leaf.Port → K) (aux : Stacks K) :=
  ∀ i, i ≠ .row → i ≠ .packed → i ≠ JointScalar.Leaf.resultPort → aux (embed i) = JointScalar.Leaf.clean L [] [] [] i

private theorem leafFrame {w : ℕ} (rs : Reg → Word w) (res : List Bool)
    (d : Bool → PairCall.Inputs) (pack flag constant : Bool → List Bool) (aux : Stacks K)
    (embed : JointScalar.Leaf.Port → K) (L : JointScalar.Leaf.Layout) (loaded : Loaded L embed aux) (i : JointScalar.Leaf.Port) :
    frame rs res (Arms.storage w d pack flag constant aux) (ports embed i) =
      JointScalar.Leaf.clean L (digits w (rs (outReg 1)).val) (pack false) res i := by
  by_cases hr : i = .row
  · subst i
    simp only [ports, ite_true, frame_route]
    change wordBits (rs (outReg 1)) = wordBits (Fin.ofNat _ (rs (outReg 1)).val)
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt (rs (outReg 1)).isLt).symm
  by_cases hp : i = .packed
  · subst i; rfl
  by_cases hs : i = JointScalar.Leaf.resultPort
  · subst i; rfl
  simp only [ports, hr, hp, hs, ite_false]
  change aux (embed i) = _
  rw [loaded i hr hp hs]
  cases i with
  | row => contradiction
  | packed => contradiction
  | arithmetic i =>
    rcases i with i|i
    · cases i with
      | divide j => cases j <;> rfl
      | _ => rfl
    · cases i <;> first | rfl | exact (hs rfl).elim
  | _ => rfl

/-- A bounded run on the named coefficient bank lifts to a returning reader
arm. The input registers, payload, flags, and both scan buffers are restored. -/
theorem bounded [DecidableEq K] {w cap steps : ℕ} (rs : Reg → Word w) (d : Bool → PairCall.Inputs)
    (pack flag constant : Bool → List Bool) (aux : Stacks K) (embed : JointScalar.Leaf.Port → K) (hinj : Function.Injective embed)
    (L : JointScalar.Leaf.Layout) (loaded : Loaded L embed aux) (out : List Bool)
    (room : ∀ i, (frame rs [] (Arms.storage w d pack flag constant aux) i).length ≤ cap)
    (call : JointScalar.Leaf.machine.BoundedRun cap steps (JointScalar.Leaf.clean L (digits w (rs (outReg 1)).val) (pack false) [])
      (JointScalar.Leaf.clean L (digits w (rs (outReg 1)).val) (pack false) out)) :
    (JointScalar.Leaf.machine.onPorts (ports embed)).BoundedRun cap steps (frame rs [] (Arms.storage w d pack flag constant aux))
      (frame rs out (Arms.storage w d pack flag constant aux)) := by
  apply call.framed (ports_injective hinj) room (leafFrame rs [] d pack flag constant aux embed L loaded)
    (leafFrame rs out d pack flag constant aux embed L loaded)
  intro i hi
  cases i <;> first | rfl | exact (hi JointScalar.Leaf.resultPort rfl).elim

end RankQuery.Stack.MacaulayRead.SignedLeaf

end VPVNP
end Computability
end OAI
