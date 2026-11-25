import OAI.Computability.NearSquareRoot.CRTPositionOpcodeStage
import OAI.Computability.NearSquareRoot.CRTPositionProgramTable
import OAI.Computability.NearSquareRoot.CRTPositionNamedBranch

/-! # Canonical physical input for a named position opcode -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Loom NamedPacked

private theorem sizeRows (l : List Tally) (n : ℕ) (h : ∀ x ∈ l, x.length ≤ n) :
    size l ≤ l.length*(2*n+2)+1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h₀ := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [size_cons,size_tally,List.length_cons]
    rw [Nat.succ_mul l.length (2*n+2)]
    omega

theorem keySize (k : ℕ) (op : Op) (wf : WellFormed k (guardWidth k) op) :
    size (tally k,op) ≤ 128*(k+1)^2 := by
  have small (c d : Fin 3) : size (c,d) ≤ 64 := by decide +revert
  rcases op with ⟨c,d⟩ | (⟨r,t⟩ | (⟨s,d⟩ | ⟨s,d⟩))
  · simp only [size_prod,size_tally,tally_length,size_inl]
    have h := small c d; rw [size_prod] at h; nlinarith
  · obtain ⟨hr,read,rfl⟩ := wf
    have co : Nat.clog 2 (k+1) ≤ k := Nat.clog_le_of_le_pow (show k < 2^k from Nat.lt_two_pow_self)
    have hN := Nat.div_le_self k 3
    let code (j : Fin (k/3)) := tally (((read j).map Fin.val).getD (k/3))
    have table := sizeRows (List.ofFn code) (k/3) (by
      intro u hu; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hu
      unfold code
      cases h : read j with
      | none => simp
      | some s => simp [s.isLt.le])
    rw [List.length_ofFn] at table
    change size (tally k,packed (r,List.ofFn code)) ≤ _
    simp only [size_prod,size_tally,tally_length,size_inr,size_inl]
    unfold guardWidth at hr
    have h := Nat.mul_le_mul hN (show 2*(k/3)+2 ≤ 2*k+2 by omega)
    nlinarith
  · obtain ⟨ha,hb⟩ := wf
    simp only [size_prod,size_tally,tally_length,size_inr,size_inl]; have := Nat.div_le_self k 3; nlinarith
  · obtain ⟨ha,hb,_,_⟩ := wf
    simp only [size_prod,size_tally,tally_length,size_inr]; nlinarith

/-- All actual word widths, legal opcodes, payload widths, and payload contents are
in this same input family before choosing any environment-independent command. -/
structure Call {T : Type} (wrap : T → Op) where
  k : ℕ
  operand : T
  legal : WellFormed k (guardWidth k) (wrap operand)
  width : ℕ
  data : Block 2 k → Fin width → Bead

namespace Call

variable {T : Type} {wrap : T → Op}

def key (x : Call wrap) := send (tally x.k,wrap x.operand)

def regime (wrap : T → Op) : Regime (Call wrap) where
  scale := k
  header := key
  gauge := ⟨2,128,fun x => keySize x.k _ x.legal⟩

noncomputable def packet (x : Call wrap) (f : Block 2 x.k → Fin x.width → Bead) :=
  stripe (line 2 x.k) (fun a => strip (Series.natural x.width) (f a))

noncomputable def input (x : Call wrap) : Tree := .fork x.key (x.packet x.data)

noncomputable def output (x : Call wrap) : Tree :=
  x.packet (x.data ∘ nativeOp x.k (guardWidth x.k) (wrap x.operand))

theorem widthHas : (regime wrap).Has (tally ∘ k) := by
  exact (show (regime wrap).Has (fun x => (tally x.k,wrap x.operand)) from Regime.self).ez Easy.fst

theorem opcodeHas : (regime wrap).Has (fun x => wrap x.operand) := by
  exact (show (regime wrap).Has (fun x => (tally x.k,wrap x.operand)) from Regime.self).ez Easy.snd

end Call

def OpAt {T : Type} (c : Cmd) (ρ : ℝ) (wrap : T → Op) : Prop :=
  BreezeAt c (Spindle.modes Call.k (τ:=ρ)) (Call.regime wrap)
    (fun x => (line 2 x.k).count) Call.width Call.input Call.output

theorem opAt_table {ρ : ℝ} {c : Cmd} (h : OpAt c ρ id) :
    BreezeAt c (Spindle.modes (fun i : StageCase => i.1.k) (τ:=ρ)) tableRegime
      (fun i => (line 2 i.1.k).count) (fun i => i.1.width)
      (fun i => Tree.fork (i.1.key i.2.1) (i.1.packet i.2.2)) (fun i => i.1.packet (i.1.rowStep i.2.1 i.2.2)) := by
  let pick (i : StageCase) : Call id := ⟨i.1.k,i.2.1.val,table_wf i,i.1.width,i.2.2⟩
  exact h.on pick

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
