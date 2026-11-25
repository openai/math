import OAI.Computability.BorderVNP.DiagonalSignedChooserLayout
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostPointers

/-! # Signed host pointers in the reached directory publication -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing BorderVNP.Cube Cube.Physical Cube.NativeIntervals LocalRow CubeArena CubeHeaderInstall
open TeamContraction.JointHeader VPVNP.BurstRAM FiniteEvaluator

variable {w R X : ℕ} {a : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {slotted : Memory w} {base : ℕ} {pub : Arg → Word w} {f : BroadcastFrame} {old : Fin 81 → Word w}
    {fresh gates outputs width off ell controls : ℕ} {G : List Bool} {claims : List (List Bool)}
    {pad : ℕ} {raw : Broadcast a.n a.header.d a.header.cap}
    (room : PinnedRawInput (ar := a) (D := D) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
      f old fresh gates outputs width off ell controls G claims pad raw R X)
include room

/-- All eight host operands in the reached signed RAM have their physical
addresses and native row widths. The bound for each bank comes from the
allocated arena and the signed packet widths in this same publication. -/
theorem PinnedRawInput.signed_host_pointers :
    CubeAllocation.HostPointers a (pub 0).val
      (readings (Packing.Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp))) := by
  intro k member value field
  have fits := room.arena
  obtain ⟨_,labels,group,pair,host,records,reserved,endRoom⟩ := a.writer_order
  have ordPower : a.ordinalBase+a.cables=a.powerBase := rfl
  have powerGroup := a.group_order.2.2.2.2.2.2.2.1
  have alpha : a.dataMean+a.alphabet=a.widthBase := rfl
  have widthOrd : a.widthBase≤a.ordinalBase := Nat.le_add_right ..
  have single := a.separated.2.1
  have vertex : a.vertexBase ≤ a.publicBase := Nat.le_add_right ..
  obtain ⟨dirWord,bankWord,selectorWord⟩ := room.signed_host_operands
  simp only [CubeAllocation.hostPointerFields,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp only [CubeArena.Layout.operand,Option.some.injEq] at field <;> subst value
  all_goals first | exact dirWord | exact bankWord | exact selectorWord |
    exact room.boot.arenaOperand a old fresh G.length gates outputs width off ell rfl (by omega)

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
