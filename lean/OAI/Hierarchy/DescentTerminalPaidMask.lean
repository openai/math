import OAI.Hierarchy.DescentTerminalDenseMask
import OAI.Hierarchy.DescentTerminalThreshold

namespace OAI
/-! # Linear static verification of the paid-row cutoff words on the live trace -/

namespace Hierarchy.DescentTerminalPaidMask
open ThreeFlat ThreeFlat.Routing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalPorts DescentTerminalDenseMask DescentTerminalThreshold Computability.BorderVNP.Crossing
open scoped Fin.CommRing Classical BigOperators
noncomputable section

variable {F : Type*} [CommSemiring F] {rows word W : ℕ}

abbrev Pin (rows word : ℕ) := (Fin rows×Fin (depth word)) ⊕ RowBit rows word

def pins (cut : Fin rows→ℕ) (pay : RowBit rows word→Bool) : Pin rows word→Bool :=
  Sum.elim (fun x=>(cut x.1).testBit x.2.val) pay

private def wire (i : Fin rows) : DescentTerminalThreshold.Pin (depth word) word→Pin rows word ⊕ Empty
  | .inl j=>.inl (.inl (i,j))
  | .inr j=>.inl (.inr (i,j))

private def allowed (F : Type*) [CommSemiring F] (hidden pay : Bool) : F :=
  if hidden=true→pay=false then 1 else 0

def network (F : Type*) [CommSemiring F] (rows word : ℕ) : BitNetwork F (Fintype.card (Pin rows word)) :=
  TypedWiring.glue (fun _ : Fin rows=>DescentTerminalThreshold.network (depth_room word).le (allowed F)) wire

theorem network_value (F : Type*) [CommSemiring F] (cut : Fin rows→ℕ) (pay : RowBit rows word→Bool)
    (fits : ∀i,cut i≤word) :
    TypedWiring.value (network F rows word) (pins cut pay)=
      if ∀x : RowBit rows word,cut x.1≤x.2.val→pay x=false then 1 else 0 := by
  rw [network,TypedWiring.glue_value,Fintype.sum_unique]
  have each (i : Fin rows) (hidden : Empty → Bool) :
      TypedWiring.value (DescentTerminalThreshold.network (depth_room word).le (allowed F))
        (fun j=>Sum.elim (pins cut pay) hidden (wire i j))=
        ∏j : Fin word,allowed F (decide (cut i≤j.val)) (pay (i,j)) := by
    have e : (fun j=>Sum.elim (pins cut pay) hidden (wire i j))=
        Sum.elim (fun j : Fin (depth word)=>(cut i).testBit j.val) (fun j=>pay (i,j)) := by
      funext j
      cases j <;> rfl
    rw [e]
    apply DescentTerminalThreshold.network_value _ _ _ ((fits i).trans_lt (depth_room word))
  trans ∏ i : Fin rows, ∏ j : Fin word, allowed F (decide (cut i ≤ j.val)) (pay (i,j))
  · exact Finset.prod_congr rfl (fun i _ => each i _)
  by_cases good : ∀x : RowBit rows word,cut x.1≤x.2.val→pay x=false
  · rw [ite_eq_left good]
    apply Finset.prod_eq_one
    intro i _
    apply Finset.prod_eq_one
    intro j _
    unfold allowed
    exact ite_eq_left (fun atCut => good (i,j) (of_decide_eq_true atCut))
  · rw [ite_eq_right good]
    obtain ⟨⟨i,j⟩,fails⟩:=not_forall.mp good
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [allowed,fails]))

theorem network_size (F : Type*) [CommSemiring F] (rows word : ℕ) (hw : 0<word) :
    (network F rows word).cells+(network F rows word).internal≤9*(rows*word) := by
  let A:=DescentTerminalThreshold.network (depth_room word).le (allowed F)
  have e : (network F rows word).cells+(network F rows word).internal=rows*(A.cells+A.internal) := by
    simp [network,A,TypedWiring.glue_cells,TypedWiring.glue_internal,Nat.mul_add]
  rw [e,Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ (linear (allowed F) hw)

variable {D : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)

/-- Every accepted physical payload has exactly the required zero slack.
Only the native cutoff words and the payload itself are exposed to this
fixed trivalent network. -/
theorem native_value (F : Type*) [CommSemiring F] (code : N.Edge ↪ ℕ) (room : (∑e,N.width e)≤rows*word)
    (dst header : ℕ) (limit : rows*word<2^W) (wordFit : word<2^W) (dstFit : dst+rows<2^W)
    (headerFit : header<2^W) (away : header<dst ∨ dst+rows≤header) (pay : RowBit rows word→Bool) :
    (DescentTerminalDenseMask.procedure W rows word dst header).Spec
      (fun m=>m header=((∑e,N.width e:ℕ):Word W))
      (fun _ o=>TypedWiring.value (network F rows word)
          (pins (fun i=>(o (dst+i.val)).val) pay)=
        if ZeroUnused N (denseBits N code room) pay then 1 else 0) (4+54*rows) := by
  refine Procedure.Spec.mono (A:=DescentTerminalDenseMask.procedure W rows word dst header)
    (cutoff_spec N code room dst header limit wordFit dstFit headerFit away) (fun _ h=>h) ?_ le_rfl
  intro m out result
  let cut:=fun i : Fin rows=>(out (dst+i.val)).val
  have fits (i):cut i≤word := (result i).1.le.trans (min_le_left ..)
  rw [network_value _ _ _ fits]
  apply if_congr _ rfl rfl
  rw [← mask_ok N (denseBits N code room) pay]
  refine forall_congr' ?_
  rintro ⟨i,j⟩
  rw [←(result i).2 j,decide_eq_true_eq]

end
end Hierarchy.DescentTerminalPaidMask

end OAI
