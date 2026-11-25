import OAI.Computability.BorderVNP.PackedInheritedHookCode
import OAI.Computability.BorderVNP.PackedLiveCuts

/-! # Executing the full rectangular immutable hook packet

The matched-count join, the clipped interval words, and the destination wire
view are shared across all scalar operands. The public output includes the
successor occupancy bit, destination site address, and all nine words of the
actual sparse equality command.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedHook

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Inherited InheritedProfile BankSite BankJoint BankCircuit BankPacket CellSparse Word
open ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Type} [Fintype S] {n old sites np C d h w : ℕ} (seed : S ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))

/-- Shared numeric input vector of every potential clipped-hook packet. -/
noncomputable def operands : Frame σ (Row old D × Arg × Fin w) :=
  let joined := parallelFrame (matched e seed F counts) (parallelFrame cut (Views.frame F))
  joined.select fun (t : Row old D × Arg × Fin w) =>
    let r := t.1
    let j := t.2.2
    let b : Band D := some (r.2.1,true)
    match t.2.1 with
    | .matched => .inl (r,j)
    | .span => .inr (.inl ((r.1,b),.span,j))
    | .ordinal => .inr (.inl ((r.1,b),.ordinal,j))
    | .wire => .inr (.inr (.inl (.inl (.inr (candidate e (n := n) r))),j))

omit [NeZero D] in
/-- The live cut and virtual address passes occur once in the hook operand frame. -/
theorem operands_size : (operands e seed F counts cut).size =
    (matched e seed F counts).size+cut.size+(Views.frame F).size := by
  simp [operands,parallelFrame_size,Nat.add_assoc]

/-- One scalar expression in the nine-word native payload. -/
noncomputable def wordExpr (j : Fin 9) : WidthExpr Arg :=
  (code e).words[j.val]'(j.isLt.trans_eq (code_length e).symm)

omit [NeZero D] in
/-- Reading the nine expression values produces the native serialized equality in order. -/
theorem wordExpr_value (x : Arg → ℕ) (j : Fin 9) :
    (wordExpr e j).eval x = (Packet.record ((code e).read x))[j.val]?.getD 0 := by
  rw [← RecordCode.words_eval]
  simp [wordExpr,j.isLt.trans_eq (code_length e).symm]

/-- The enable bit, destination site pointer, and nine words of one live hook packet. -/
abbrev Column (d w : ℕ) := Unit ⊕ (Fin d ⊕ (Fin 9 × Fin w))

variable (occupied : Fin (edgeCapacity e old n) → σ)

omit [NeZero D] in
/-- Emit all hook packets for all live branches using one gate list chosen only
from the static input pins. Disabled candidates retain an explicit zero enable. -/
theorem exists_frame :
    ∃ f : Frame σ (Row old D × Column d w), f.size ≤ (operands e seed F counts cut).size+1+
      Fintype.card (Row old D)*(nodes e*(100*(w+1)^2)) ∧
    ∀ x r, f.eval x (r,.inl ()) = x (occupied (candidate e (n := n) r)) ∧
      (∀ j, f.eval x (r,.inr (.inl j)) = x (F.ptr (.inl (.inr (candidate e (n := n) r))) j)) ∧
      ∀ j : Fin 9, let input := fun i => value (fun l => (operands e seed F counts cut).eval x (r,i,l))
        (wordExpr e j).Fits w input →
          value (fun l => f.eval x (r,.inr (.inr (j,l)))) = (Packet.record ((code e).read input))[j.val]?.getD 0 := by
  let source := operands e seed F counts cut
  let leaf (t : Row old D × Fin 9) := ((wordExpr e t.2).frame w).subst
    (Frame.initial (fun i : Arg × Fin w => (t.1,i)))
  obtain ⟨joint,hs,he⟩ := exists_parallelFrames leaf
  let payload := joint.subst source
  let flags : Frame σ (Row old D × (Unit ⊕ Fin d)) := Frame.initial fun t => t.2.elim
    (fun _ => occupied (candidate e (n := n) t.1)) (fun j => F.ptr (.inl (.inr (candidate e (n := n) t.1))) j)
  let pins (t : Row old D × Column d w) : (Row old D × (Unit ⊕ Fin d)) ⊕ (Σ _ : Row old D × Fin 9, Fin w) :=
    match t.2 with
    | .inl u => .inl (t.1,.inl u)
    | .inr (.inl j) => .inl (t.1,.inr j)
    | .inr (.inr (k,j)) => .inr ⟨(t.1,k),j⟩
  let out := (parallelFrame flags payload).select pins
  refine ⟨out,?_,fun x r => ⟨?_,?_,?_⟩⟩
  · have hl (t : Row old D × Fin 9) : (leaf t).size ≤ (wordExpr e t.2).nodes*(100*(w+1)^2) := by
      simp only [leaf,Frame.subst_size,Frame.initial_size,zero_add]
      exact (wordExpr e t.2).frame_size w
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun t _ => hl t
    have hn : (∑ t : Row old D × Fin 9,(wordExpr e t.2).nodes*(100*(w+1)^2)) =
        Fintype.card (Row old D)*(nodes e*(100*(w+1)^2)) := by
      rw [Fintype.sum_prod_type]
      change (∑ _ : Row old D, ∑ j : Fin 9,(wordExpr e j).nodes*(100*(w+1)^2)) = _
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.sum_mul]
      rfl
    rw [hn] at hsum
    simp only [out,Frame.select_size,parallelFrame_size,flags,Frame.initial_size,payload,Frame.subst_size,zero_add,source]
    omega
  · simp [out,pins,flags]
  · intro j
    simp [out,pins,flags]
  · intro j input hfit
    let localBits := fun i : Arg × Fin w => source.eval x (r,i)
    have hv : (fun l => out.eval x (r,.inr (.inr (j,l)))) = ((wordExpr e j).frame w).eval localBits := by
      funext l
      simp [out,pins,payload,he,leaf,localBits]
      congr 1
      funext i
      simp
    rw [hv]
    exact ((wordExpr e j).frame_value w localBits hfit).trans (wordExpr_value e input j)

end Packing.InheritedHook

end BorderVNP
end Computability
end OAI
