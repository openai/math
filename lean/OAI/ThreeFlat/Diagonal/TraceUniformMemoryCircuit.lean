import OAI.ThreeFlat.Diagonal.TraceUniformMemoryStages
import OAI.ThreeFlat.Diagonal.TraceUniformSortBoundary

namespace OAI
/-! # One gate template for all physical memory-check rows -/

namespace ThreeFlat.Diagonal.TraceMemoryCircuit

open Computability.VPVNP BurstRAM RAMSort RAMSerialization
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)
open TraceSortSite TraceSlots TraceWords

variable {d w : ℕ}

private def initialExpr : Live w → Expr (ControlledPort d w)
  | .inl (i,f,j) => .input (.inl (initial i f j))
  | .inr _ => .const true

private noncomputable def uniformInitial (d w : ℕ) : Frame (ControlledPort d w) (Live w) :=
  (Frame.initial id).step initialExpr

private theorem uniformInitial_eval (v : Fin (2^d)) (x : Port d w → Bool) :
    (uniformInitial d w).eval (controlVal x v) = (initialFrame w d).eval x := by
  funext q
  rcases q with ⟨i,f,j⟩ | ⟨⟩ <;> simp [uniformInitial,initialExpr,initialFrame,controlVal,Expr.eval]

private def boundaryPin (out : Bool) : SlotAddr w (ControlledPort d w) :=
  fun f j => .inl (boundary out f j)

private noncomputable def uniformCore (d w : ℕ) : Frame (ControlledPort d w) Unit :=
  finishInput (uniformRun (schedule d) (uniformInitial d w)) (boundaryPin false)
    (boundaryPin true) (.inr (.inr ()))

private theorem uniformCore_eval (v : Fin (2^d)) (x : Port d w → Bool) :
    (uniformCore d w).eval (controlVal x v) () = (core v).eval x () :=
  finishInput_agrees _ _ _ _ _ _ _ _ _ _
    (uniformRun_eval (schedule d) v x _ _ (uniformInitial_eval v x))
    (fun _ _ => rfl) (fun _ _ => rfl) rfl

private def uniformOwnerCheck (hw : 2 ≤ w) : Expr (ControlledPort d w) :=
  ((allBits fun l : Fin (RAMLayout.layerCount d) => allBits fun i : Fin 2 =>
    valid hw (exchange l true i)).rename Sum.inl).and
    ((.not (.input (.inr (.inr ()))) : Expr (ControlledPort d w)).or
      ((valid hw (boundary true)).rename Sum.inl))

private theorem uniformOwnerCheck_eval (hw : 2 ≤ w) (v : Fin (2^d)) (x : Port d w → Bool) :
    (uniformOwnerCheck hw).eval (controlVal x v) = (ownerCheck hw v).eval x := by
  by_cases h : v.val+1<2^d <;>
    simp [uniformOwnerCheck,ownerCheck,controlVal,controlsAt,Expr.eval,h]

/-- The program of this AND/NOT circuit has no row-index parameter. -/
noncomputable def uniformRow (hw : 2 ≤ w) : Frame (ControlledPort d w) Unit :=
  (uniformCore d w).withInput.step fun _ =>
    ((uniformOwnerCheck hw).rename Sum.inl).and (.input (.inr ()))

/-- Arbitrary data bits give exactly the ordinary row's value on the affine
address bits and successor control of that row. -/
theorem uniformRow_eval (hw : 2 ≤ w) (v : Fin (2^d)) (x : Port d w → Bool) :
    ((uniformRow hw).circuit ()).eval (Sum.elim x (controlsAt (w := w) v)) = ((row hw v).circuit ()).eval x := by
  change ((uniformRow hw).circuit ()).eval (controlVal x v) = _
  simp [uniformRow,row,Expr.eval,uniformCore_eval,uniformOwnerCheck_eval]

private theorem initialSize (w d : ℕ) : (uniformInitial d w).size ≤ 14*w+1 := by
  have h (i : Live w) : (initialExpr (d := d) i).size ≤ 1 := by rcases i with ⟨_,_,_⟩ | ⟨⟩ <;> rfl
  have z := (Frame.initial (id : ControlledPort d w → ControlledPort d w)).step_size_le initialExpr 1 h
  simp only [Frame.initial_size,zero_add,mul_one,Live,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_unit] at z
  exact z.trans (by omega)

private theorem uniformOwner_size (hw : 2 ≤ w) : (uniformOwnerCheck (d := d) hw).size ≤
    RAMLayout.layerCount d*(640*(w+1)+4)+320*(w+1)+5 := by
  have h (l : Fin (RAMLayout.layerCount d)) :=
    allBits_size_le (fun i : Fin 2 => valid hw (exchange l true i)) (s := 320*(w+1))
      (fun _ => valid_size hw _)
  have hs := allBits_size_le (fun l : Fin (RAMLayout.layerCount d) =>
    allBits fun i : Fin 2 => valid hw (exchange l true i)) (s := 640*(w+1)+3)
    (fun i => (h i).trans (by omega))
  change _ ≤ RAMLayout.layerCount d*(640*(w+1)+4)+1 at hs
  have hb := valid_size hw (boundary (d := d) true)
  simp only [uniformOwnerCheck,Expr.size,Expr.size_rename]
  omega

theorem uniformRow_size (hw : 2 ≤ w) :
    (uniformRow (d := d) hw).circuitSize () ≤ 80000*(d+2)^2*(w+1)^2 := by
  have hi := initialSize w d
  have hs := uniformRun_size (schedule d) (uniformInitial d w)
  rw [schedule,length_phases] at hs
  have hf := finishInput_size (uniformRun (schedule d) (uniformInitial d w))
    (boundaryPin false) (boundaryPin true) (.inr (.inr ()))
  change (uniformCore d w).size ≤ _ at hf
  have hv := uniformOwner_size (d := d) hw
  have hout := (uniformCore d w).withInput.step_size_le
    (fun _ : Unit => ((uniformOwnerCheck hw).rename Sum.inl).and (.input (.inr ())))
    ((uniformOwnerCheck (d := d) hw).size+2) (fun _ => by simp [Expr.size])
  change (uniformRow (d := d) hw).size ≤ _ at hout
  simp only [Frame.withInput_size,Fintype.card_unit,one_mul] at hout
  have ht := (uniformRow (d := d) hw).circuitSize_le ()
  have hchoose := Nat.choose_le_pow (1+d+1) 2
  have hl : RAMLayout.layerCount d ≤ (d+2)^2 :=
    (Nat.choose_le_pow (d+1) 2).trans (Nat.pow_le_pow_left (by omega) _)
  have hs' : (uniformRun (schedule d) (uniformInitial d w)).size ≤
      (14*w+1)+(d+2)^2*((14*w+1)*(1030*(w+1))) := by
    apply hs.trans
    apply Nat.add_le_add hi
    apply Nat.mul_le_mul_right
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hchoose
  have hv' := hv.trans (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) _) _)
  apply ht.trans
  apply (Nat.mul_le_mul_left 4 (hout.trans (Nat.add_le_add hf (Nat.add_le_add_right hv' _)))).trans
  apply (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (Nat.add_le_add_right hs' _) _)).trans
  nlinarith only [Nat.zero_le (d^2*w^2), Nat.zero_le (d^2*w), Nat.zero_le (d*w^2),
    Nat.zero_le (d*w), Nat.zero_le d, Nat.zero_le w, Nat.zero_le (d^2), Nat.zero_le (w^2)]


end ThreeFlat.Diagonal.TraceMemoryCircuit

end OAI
