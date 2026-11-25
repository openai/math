import OAI.ThreeFlat.RAM.AdmissionPrefix
import OAI.ThreeFlat.RAM.CheckRowsBlock
import OAI.ThreeFlat.RAM.AdmissionHeader

namespace OAI
/-! # Deterministic admission of a packed stage histogram -/

namespace ThreeFlat.RAM.AdmissionBank

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr ContinuationLink
open scoped Classical Fin.CommRing

variable {w k n P R U : ℕ}

def rowTerm (ctrl K : ℕ) : Term w k 1 :=
  (closed (AdmissionPrefix.select K (0:Fin 3) 1 2)).instantiate (fun i => closed (args ctrl K i))

def cost (ctrl K : ℕ) := (AdmissionPrefix.select K (0:Fin 3) 1 2).work + ∑ i,(args ctrl K i).work

theorem cost_eq (ctrl K : ℕ) : cost ctrl K=cost 0 K := by
  unfold cost
  apply congrArg (Nat.add (AdmissionPrefix.select K (0:Fin 3) 1 2).work)
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> rfl

theorem binds_row (ctrl K : ℕ) : (rowTerm ctrl K : Term w k 1).binds=cost ctrl K := by
  simp [rowTerm,cost,binds_closed]

def block (ctrl K : ℕ) := CheckRowsBlock.block (rowTerm ctrl K : Term w k 1) ctrl

def ValidRow (ctrl K i : ℕ) (m : Memory w) : Prop :=
  AdmissionPrefix.Valid K (m (descBase ctrl m + 3*i+2)).val
    (fun j => (m (denseBase ctrl m + K*i+j.val)).val) (m (descBase ctrl m + 3*i)).val

theorem row_value (ctrl K i : ℕ) (data : Fin k → Word w) (m : Memory w)
    (h : Fits ctrl K m) (hi : i<rowCount ctrl m) :
    (rowTerm ctrl K).eval data m (fun _ => (i:Word w)) =
      if ValidRow ctrl K i m then (1:Word w) else 0 := by
  let b := denseBase ctrl m + K*i
  have less : K*(i+1) ≤ K*rowCount ctrl m := Nat.mul_le_mul_left K hi
  rw [Nat.mul_succ] at less
  have bound : b+K ≤ 2^w := by dsimp [b]; have := h.dense_le; omega
  have fits : b<2^w := by
    by_cases hz : K=0
    · simp [b,hz,denseBase]
    · omega
  rw [rowTerm,Term.eval_instantiate,eval_closed]
  simp_rw [eval_closed]
  rw [arg_value ctrl K i m h hi]
  let vs : Fin 3 → Word w := ![m (descBase ctrl m+3*i+2),(b:Word w),m (descBase ctrl m+3*i)]
  change (AdmissionPrefix.select K 0 1 2).value _ m vs = _
  have ptr : (vs 1).val=b := Fin.val_cast_of_lt fits
  have bit := AdmissionPrefix.word_value K (0:Fin 3) 1 2 (fun _ => 0) m vs (by rw [ptr]; exact bound)
  rw [ptr] at bit
  exact bit

theorem advance_block (ctrl K : ℕ) (width : 0<w)
    (pc : Fin (9+(rowTerm ctrl K : Term w k 1).labels) ↪ Fin P)
    (reg : Fin (4+(rowTerm ctrl K : Term w k 1).binds) ↪ Fin R)
    (φ : Fin k → Fin U) (exit : Fin P) (M : Machine w P R U)
    (installed : (block (w:=w) (k:=k) ctrl K).Installed M pc reg φ exit)
    (c : Config w P R) (m : Memory w) (start : c.pc=pc (block (w:=w) (k:=k) ctrl K).first)
    (room : Fits ctrl K m) :
    ∃ t ≤ 6+rowCount ctrl m*(2*cost ctrl K+4), ∃ d : Config w P R, advance M.program t c m=some (d,m) ∧
      d.pc=(if ∀ i, i<rowCount ctrl m → ValidRow ctrl K i m then exit else
        pc ((8:Fin 9).castAdd (rowTerm ctrl K : Term w k 1).labels)) ∧
      M.code (pc ((8:Fin 9).castAdd (rowTerm ctrl K : Term w k 1).labels))=.reject := by
  obtain ⟨t,ht,d,run,where_,rej⟩ := CheckRowsBlock.advance_block (rowTerm ctrl K) ctrl pc reg φ exit
    M installed c m start
  have count : (m (m (ctrl:Word w).val).val).val=rowCount ctrl m := by
    rw [Fin.val_cast_of_lt room.ctrl_lt]; rfl
  rw [count,binds_row] at ht
  rw [count] at where_
  have one : (1:Word w) ≠ 0 := by
    have bound : 1 < 2^w := Nat.one_lt_two_pow (by omega)
    intro eq
    have := congrArg Fin.val eq
    simp [Nat.mod_eq_of_lt bound] at this
  have valid : (∀ i, i<rowCount ctrl m → (rowTerm ctrl K).eval (M.publicData ∘ φ) m (fun _ => (i:Word w))=1) ↔
      ∀ i, i<rowCount ctrl m → ValidRow ctrl K i m := by
    have point (i : ℕ) (hi : i<rowCount ctrl m) :
        (rowTerm ctrl K).eval (M.publicData ∘ φ) m (fun _ => (i:Word w))=1 ↔ ValidRow ctrl K i m := by
      rw [row_value ctrl K i _ m room hi]
      by_cases h : ValidRow ctrl K i m <;> simp [h,Ne.symm one]
    exact ⟨fun all i hi => (point i hi).mp (all i hi),fun all i hi => (point i hi).mpr (all i hi)⟩
  refine ⟨t,ht,d,run,?_,rej⟩
  by_cases h : ∀ i, i<rowCount ctrl m → ValidRow ctrl K i m
  · simpa only [ite_eq_left h, ite_eq_left (valid.mpr h)] using where_
  · simpa only [ite_eq_right h, ite_eq_right (fun a => h (valid.mp a))] using where_

/-- A malformed bank contributes zero at the uniform stage budget and every greater fuel. -/
theorem reject_mass {F : Type*} [Semiring F] (field : FieldCode F w) (ctrl K : ℕ) (width : 0<w)
    (pc : Fin (9+(rowTerm ctrl K : Term w k 1).labels) ↪ Fin P)
    (reg : Fin (4+(rowTerm ctrl K : Term w k 1).binds) ↪ Fin R)
    (φ : Fin k → Fin U) (exit : Fin P) (M : Machine w P R U)
    (installed : (block (w:=w) (k:=k) ctrl K).Installed M pc reg φ exit)
    (c : Config w P R) (m : Memory w) (start : c.pc=pc (block (w:=w) (k:=k) ctrl K).first)
    (room : Fits ctrl K m) (invalid : ¬∀ i, i<rowCount ctrl m → ValidRow ctrl K i m)
    (fuel : ℕ) :
    mass field M.program (fuel+(6+rowCount ctrl m*(2*cost 0 K+4))) c m = 0 := by
  obtain ⟨t,ht,d,run,where_,rej⟩ := advance_block ctrl K width pc reg φ exit M installed c m start room
  rw [ite_eq_right invalid] at where_
  rw [cost_eq ctrl K] at ht
  let budget := 6+rowCount ctrl m*(2*cost 0 K+4)
  have room' : t≤budget := ht
  change mass field M.program (fuel+budget) c m=0
  rw [show fuel+budget=(fuel+(budget-t))+t by omega,mass_of_advance field _ run]
  generalize fuel+(budget-t)=rest
  cases rest with
  | zero => rfl
  | succ rest => simp [mass,Machine.program,where_,rej,Instr.run]

end ThreeFlat.RAM.AdmissionBank

end OAI
