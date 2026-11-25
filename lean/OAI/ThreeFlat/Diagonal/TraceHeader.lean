import OAI.ThreeFlat.Diagonal.TraceProgramText
import OAI.ThreeFlat.Diagonal.TraceFormulaPacket

namespace OAI
/-! # Validity and value of the RAM program entry supplied in the input image -/

namespace ThreeFlat.Diagonal.TraceProgram

open TraceWords RAM TracePair
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

def headerPins (j : Fin w) : Expr (Text w p k) :=
  .input (⟨0,by omega⟩,j)

def headerTest (w p k : ℕ) : Expr (Text w p k) :=
  Expr.disjoin (List.ofFn fun i : Fin p => fieldIs headerPins i.val)

noncomputable def headerCircuit (w p k : ℕ) : TraceCompose.Packet (Text w p k) :=
  formulaPacket (headerTest w p k)

theorem headerCircuit_true (data : Memory w) :
    (headerCircuit w p k).2.eval (contents data) = true ↔ (data 0).val < p := by
  simp only [headerCircuit,formulaPacket_eval,headerTest,Expr.eval_disjoin_true,List.mem_ofFn,
    exists_exists_eq_and]
  have ht (i : Fin p) : (fieldIs (headerPins (p:=p) (k:=k)) i.val).eval (contents data) = true ↔
      (data 0).val = i.val := fieldIs_true _ _ _ _ (fun _ => rfl)
  constructor
  · rintro ⟨i,hi⟩
    rw [(ht i).mp hi]
    exact i.isLt
  · exact fun hi => ⟨⟨_,hi⟩,(ht _).mpr rfl⟩

theorem headerCircuit_valid (data : Memory w) :
    (headerCircuit w p k).2.eval (contents data) = (readProgram w p r k data).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [headerCircuit_true]
  by_cases h : (data 0).val < p <;> simp [h,readProgram,bounded]

theorem readProgram_entry {data : Memory w} {M : Machine w p r k} (h : readProgram w p r k data = some M) :
    M.entry.val = (data 0).val := by
  by_cases he : (data 0).val < p
  · simp [readProgram,bounded,he] at h
    subst M
    rfl
  · simp [readProgram,bounded,he] at h

theorem headerCircuit_size_le (w p k : ℕ) :
    (headerCircuit w p k).1 ≤ 4*(p*(10*w+2)+1) := by
  apply (formulaPacket_size_le _).trans
  apply Nat.mul_le_mul_left
  apply (Expr.size_disjoin_le _ (10*w+1) ?_).trans
  · simp [Nat.add_assoc]
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact fieldIs_size _ _ (fun _ => le_rfl)

end ThreeFlat.Diagonal.TraceProgram

end OAI
