import OAI.ThreeFlat.RAM.HistorySelectedSweep
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # A chronological selected-node sweep over an arbitrary native preparation procedure -/

namespace ThreeFlat.RAM.HistoryNodeDirectory.Selected
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure
open scoped Fin.CommRing

variable {w p r k : ℕ}

private theorem run_any (M : Machine w p r k) (P : Fin 35 ↪ Fin p) (R : Fin 8 ↪ Fin r)
    (pub : Fin 6 → Fin k) (take exit : Fin p) (rom : ∀ i, M.code (P i)=rows P R pub take exit i)
    (selected : ℕ → Bool) (cost : ℕ → ℕ) (inv : ℕ → Memory w → Prop) (n : ℕ)
    (state : Config w p r) (input : Memory w) (entry : state.pc=P 0)
    (initial : inv 0 («initialize» (M.publicData∘pub) input))
    (live : ∀ i m, inv i m → (cur (M.publicData∘pub) m < m (M.publicData (pub 0)+1).val ↔ i<n))
    (which : ∀ i m, inv i m → i<n → (groupOK (M.publicData∘pub) m ∧ slotOK (M.publicData∘pub) m ↔ selected i=true))
    (skip : ∀ i m, inv i m → i<n → selected i=false → inv (i+1) (bump (M.publicData∘pub) m))
    (body : ∀ i (c : Config w p r) m, inv i m → i<n → selected i=true → c.pc=take →
      ∃ t≤cost i, ∃ d m', advance M.program t c (bump (M.publicData∘pub) m)=some (d,m') ∧
        d.pc=P 11 ∧ inv (i+1) m') :
    ∃ t≤11+budget selected cost 0 n, ∃ d out, advance M.program t state input=some (d,out) ∧
      d.pc=exit ∧ inv n out := by
  have loop (left i : ℕ) (endAt : i+left=n) (c : Config w p r) (m : Memory w)
      (atGuard : c.pc=P 11) (ok : inv i m) :
      ∃ t≤budget selected cost i left, ∃ d out, advance M.program t c m=some (d,out) ∧
        d.pc=exit ∧ inv n out := by
    induction left generalizing i c m with
    | zero =>
      have stop := (live i m ok).not.mpr (by omega)
      have guard := check M P R pub take exit rom c m atGuard
      dsimp only [Function.comp_apply] at guard
      rw [ite_eq_right stop] at guard
      obtain ⟨rs,done⟩ := guard
      exact ⟨6,le_rfl,⟨exit,c.persistent,rs,c.privateMem⟩,m,done,rfl,(by omega : i=n) ▸ ok⟩
    | succ left ih =>
      have hi : i<n := by omega
      have guard := check M P R pub take exit rom c m atGuard
      dsimp only [Function.comp_apply] at guard
      rw [ite_eq_left ((live i m ok).mpr hi)] at guard
      obtain ⟨t,ht,rs,go⟩ := guard
      let mid (pc : Fin p) : Config w p r := ⟨pc,c.persistent,rs,c.privateMem⟩
      cases sel : selected i with
      | false =>
        have miss := (which i m ok hi).not.mpr (by simp [sel])
        rw [ite_eq_right miss] at go
        obtain ⟨b,hb,z,out,done,pc,good⟩ := ih (i+1) (by omega) (mid (P 11)) (bump _ m) rfl (skip i m ok hi sel)
        exact ⟨t+b,by simp only [budget,sel,Bool.false_eq_true,ite_false,Nat.add_zero]; omega,
          z,out,advance_trans go done,pc,good⟩
      | true =>
        rw [ite_eq_left ((which i m ok hi).mpr sel)] at go
        obtain ⟨a,ha,d,m',work,pc,ok'⟩ := body i (mid take) m ok hi sel rfl
        obtain ⟨b,hb,z,out,done,atExit,good⟩ := ih (i+1) (by omega) d m' pc ok'
        exact ⟨t+a+b,by simp only [budget,sel,ite_true]; omega,z,out,
          advance_trans (advance_trans go work) done,atExit,good⟩
  obtain ⟨rs,startup⟩ := start M P R pub take exit rom state input entry
  obtain ⟨b,hb,z,out,done,atExit,ok⟩ := loop n 0 (by omega)
    ⟨P 11,state.persistent,rs,state.privateMem⟩ («initialize» (M.publicData ∘ pub) input) rfl initial
  exact ⟨11+b,by omega,z,out,advance_trans startup done,atExit,ok⟩

/-- The guard owns eight local registers and six public operands; its selected
body has its own register/public spaces and reloads the cursor on return. -/
def procedure (data : Data w) (A : Procedure w) : Procedure w where
  labels := 35+A.labels
  registers := 8+A.registers
  slots := 6+A.slots
  publicData := Fin.append data A.publicData
  block := block (A.block.reindex (Fin.natAddEmb 8) (Fin.natAdd 6))
    (Fin.castAddEmb A.registers) (Fin.castAdd A.slots)

/-- A different local specification and cost may be used at each selected site.
The invariant remembers the original input so it can express the final
Store certificate, pointer bounds and untouched low frame. -/
theorem procedure_spec (data : Data w) (A : Procedure w) (n : ℕ) (selected : ℕ → Bool) (cost : ℕ → ℕ)
    (pre : Memory w → Prop) (inv : Memory w → ℕ → Memory w → Prop)
    (initial : ∀ input, pre input → inv input 0 («initialize» data input))
    (live : ∀ input i m, inv input i m → (cur data m < m (data 0+1).val ↔ i<n))
    (which : ∀ input i m, inv input i m → i<n → (groupOK data m ∧ slotOK data m ↔ selected i=true))
    (skip : ∀ input i m, inv input i m → i<n → selected i=false → inv input (i+1) (bump data m))
    (body : ∀ input i, pre input → i<n → selected i=true →
      A.Spec (fun x => ∃ m, inv input i m ∧ x=bump data m)
        (fun _ out => inv input (i+1) out) (cost i)) :
    (procedure data A).Spec pre (fun input out => inv input n out) (11+budget selected cost 0 n) := by
  intro p r k M pc regs pub exit installed table state input entry prepared
  let P := (Fin.castAddEmb A.labels).trans pc
  let Q := (Fin.natAddEmb 35).trans pc
  let R := (Fin.castAddEmb A.registers).trans regs
  let S := (Fin.natAddEmb 8).trans regs
  let choose := pub ∘ Fin.castAdd A.slots
  let use := pub ∘ Fin.natAdd 6
  have matchData : M.publicData ∘ choose = data := by
    funext i
    exact (table (i.castAdd A.slots)).trans (Fin.append_left data A.publicData i)
  have innerData (i : Fin A.slots) : M.publicData (use i)=A.publicData i := by
    exact (table (Fin.natAdd 6 i)).trans (Fin.append_right data A.publicData i)
  have guard (i : Fin 35) : M.code (P i)=rows P R choose (Q A.block.first) exit i := by
    exact (installed (i.castAdd A.labels)).trans (Fin.append_left _ _ i)
  have inner : A.block.Installed M Q S use (P 11) := by
    intro i
    exact (installed (Fin.natAdd 35 i)).trans (Fin.append_right _ _ i)
  apply run_any M P R choose (Q A.block.first) exit guard selected cost (inv input) n state input entry
  · rw [matchData]
    exact initial input prepared
  · intro i m ok
    change cur (M.publicData ∘ choose) m < m ((M.publicData ∘ choose) 0+1).val ↔ i<n
    rw [matchData]
    exact live input i m ok
  · intro i m ok hi
    rw [matchData]
    exact which input i m ok hi
  · intro i m ok hi miss
    rw [matchData]
    exact skip input i m ok hi miss
  · intro i c m ok hi sel here
    rw [matchData]
    exact body input i prepared hi sel M Q S use (P 11) inner innerData c (bump data m) here ⟨m,ok,rfl⟩

end ThreeFlat.RAM.HistoryNodeDirectory.Selected

end OAI
