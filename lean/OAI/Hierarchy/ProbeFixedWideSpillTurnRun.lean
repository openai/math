import OAI.Hierarchy.ProbeFixedWideSpillTurns
import OAI.Hierarchy.ProtocolRAMDateSpillTurnInputs
import OAI.Hierarchy.ProtocolRAMFrozenSeries

namespace OAI
/-! # Simultaneous physical readback of all five-word spill boards after the last date -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open HistoryRoles RoleProgram
open scoped Classical BigOperators Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits datedROM terminalROM terminalWork rankFirst turnFirst : ℕ)
local notation "T" => (events v.mesh).length
local notation "native" => v.wideTerminal h width bits terminalROM terminalWork
local notation "w" => wordBits h (2^v.W) copies
variable (oldStart newStart leftOnly rightOnly : Fin (events v.mesh).length→ℕ)
local notation "panel" j => v.wideSpillTurnPage h width bits datedROM terminalROM terminalWork rankFirst
  turnFirst oldStart newStart leftOnly rightOnly j
local notation "outputEnd" => v.wideSpillTurnsEnd h width bits datedROM terminalROM terminalWork rankFirst
  turnFirst oldStart newStart leftOnly rightOnly
local notation "stride" => v.wideSpillTurnStride h width bits terminalROM terminalWork
local notation "Seat" => ProtocolRAMTurnShelf.Seats (native).sites (native).seats

theorem wide_spill_turn_run (m : Memory w) (reads : ∀j,(panel j).Inputs turnFirst m)
    (room : outputEnd≤2^w) :
    ∃out,(v.wideSpillTurnsProgram h width bits datedROM terminalROM terminalWork rankFirst turnFirst
      oldStart newStart leftOnly rightOnly).Exec m out
      (v.wideSpillTurnsTicks h width bits datedROM terminalROM terminalWork rankFirst turnFirst oldStart newStart leftOnly rightOnly) ∧
      (∀j (f : Fin 5) (s : Seat),out ((panel j).base+f.val*((native).sites*(native).seats)+s.1.val*(native).seats+s.2.val)=
        (reads j).word f s) ∧ ∀a,a<turnFirst ∨ outputEnd≤a→ out a=m a := by
  let phase : Fin (T+1)→Procedure w := Fin.cases (scan w 0 0 (.lit 0)) (fun j=>(panel j).program w)
  let tick : Fin (T+1)→ℕ := Fin.cases 4 (fun j=>(panel j).ticks)
  let atAddr (j : Fin T) (f : Fin 5) (s : Seat):=(panel j).base+f.val*((native).sites*(native).seats)+s.1.val*(native).seats+s.2.val
  let board : Fin (T+1)→ℕ→Prop:=Fin.cases (fun _=>False) (fun j a=>∃f s,atAddr j f s=a)
  let cell : Fin (T+1)→ℕ→Word w→Prop:=Fin.cases (fun _ _=>True)
    (fun j a z=>∀f s,atAddr j f s=a→z=(reads j).word f s)
  have first (j : Fin T) : (panel j).first=turnFirst+j.val*stride := rfl
  have last (j : Fin T) : (panel j).stop≤turnFirst+(j.val+1)*stride :=
    v.wide_spill_turn_end h width bits datedROM terminalROM terminalWork rankFirst turnFirst oldStart newStart leftOnly rightOnly j
  have finalBound (j : Fin T) : (panel j).stop≤outputEnd :=
    (last j).trans (Nat.add_le_add_left (Nat.mul_le_mul_right stride j.isLt) _)
  have inPage (j : Fin T) (f : Fin 5) (s : Seat) : atAddr j f s<(panel j).stop := by
    have a : s.1.val*(native).seats+s.2.val<(native).sites*(native).seats :=
      calc _ < s.1.val*(native).seats+(native).seats := Nat.add_lt_add_left s.2.isLt _
           _ = (s.1.val+1)*(native).seats := (Nat.succ_mul ..).symm
           _ ≤ _ := Nat.mul_le_mul_right _ s.1.isLt
    have b:=Nat.mul_le_mul_right ((native).sites*(native).seats) f.isLt
    rw [Nat.succ_mul] at b
    have bounds:=(panel j).window.bounds
    have fence : (panel j).window.base+5*((native).sites*(native).seats)≤(panel j).window.scratch := bounds.2.2.2.1
    dsimp only [atAddr,DateSpill.TurnPage.stop,DateSpill.TurnPage.base]
    omega
  obtain ⟨out,exec,_,stored,frame⟩:=ProtocolRAMFrozenSeries.run_observed T phase m
    (fun u=>∀a<turnFirst,u a=m a) (fun a=>a<turnFirst ∨ outputEnd≤a) board cell tick (by simp) (by
      intro i
      refine Fin.cases ?_ (fun j=>?_) i
      · intro s keep
        have zero : (scan w 0 0 (.lit 0)).Exec s (image 0 0 (.lit 0) s) 4:=scan_exec 0 0 (.lit 0) s trivial (Nat.two_pow_pos _)
        have empty : image 0 0 (.lit 0) s=s:=by funext a;simp [image,fillSegment]
        rw [empty] at zero
        exact ⟨s,zero,keep,by simp [board],by simp,by simp⟩
      · intro s keep
        obtain ⟨next,ran,words,stable⟩:=(reads j).run s keep (by rw [first];omega) ((finalBound j).trans room)
        refine ⟨next,ran,fun a ha=>(stable a (.inl (by rw [first];omega))).trans (keep a ha),
          fun a _ f s h=>h ▸ words f s,?_,?_⟩
        · rintro a (ha|ha)
          · exact stable a (.inl (by rw [first];omega))
          · exact stable a (.inr ((finalBound j).trans ha))
        · intro i
          refine Fin.cases (by simp [board]) (fun t ht a ha=>?_) i
          obtain ⟨f,s,rfl⟩:=ha
          have step:=Nat.mul_le_mul_right stride (show t.val+1≤j.val from Fin.succ_lt_succ_iff.mp ht)
          exact stable _ (.inl ((inPage t f s).trans_le ((last t).trans (by rw [first];omega)))))
  refine ⟨out,?_,fun j f s=>stored j.succ _ ⟨f,s,rfl⟩ f s rfl,frame⟩
  have total : (∑ i : Fin (T+1), tick i) =
      v.wideSpillTurnsTicks h width bits datedROM terminalROM terminalWork rankFirst turnFirst
        oldStart newStart leftOnly rightOnly := by
    simp only [Fin.sum_univ_succ, tick, Fin.cases_zero, Fin.cases_succ, wideSpillTurnsTicks]
  change (ProcedureBank.program T phase).Exec m out
    (v.wideSpillTurnsTicks h width bits datedROM terminalROM terminalWork rankFirst turnFirst
      oldStart newStart leftOnly rightOnly)
  rw [← total]
  exact @exec

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
