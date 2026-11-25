import OAI.ThreeFlat.RAM.TickControlHeader
import OAI.ThreeFlat.RAM.TickClockWriter
import OAI.ThreeFlat.RAM.TickPhysicalABI

namespace OAI
/-! # Deterministic physical controls at the entry of the compressor replay -/

namespace ThreeFlat.RAM.TickNavigationEntry
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan Diagonal.TickChronology TickActiveROM
open scoped Fin.CommRing
variable {w k r pc : ℕ}

/-- The two four-word arrays written by the native prologue. -/
def controls (w team step : ℕ) (ph : Phase) : Fin 4 → Word w :=
  ![(team : Word w),(step : Word w),(ph.tag : Word w),1]

def destination (w base : ℕ) (i : Fin 4) : Word w := (base+i.val : ℕ)

def input (B : Layout) (clock : Clock) (team step : ℕ) (m : Memory w) : Memory w :=
  fillSegment B.clockWords 4 (fun j => (TickClockWords.values clock B.bits B.teams team step
    (Fin.ofNat 4 (j-B.clockWords)) : Word w))
    (TickControlHeader.store (destination w B.control) (controls w team step (clock.phase step)) m)

private def destEmbedding (base : ℕ) (room : base+4 ≤ 2^w) : Fin 4 ↪ Word w where
  toFun := destination w base
  inj' := by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have eq := congrArg Fin.val h
    change ((base+i.val : ℕ) : Word w).val = ((base+j.val : ℕ) : Word w).val at eq
    rw [Fin.val_cast_of_lt (by omega),Fin.val_cast_of_lt (by omega)] at eq
    exact Fin.ext (by omega)

theorem hydrated (B : Layout) (clock : Clock) (team step : ℕ) (m : Memory w)
    (disjoint : B.control+4 ≤ B.clockWords) (fit : B.clockWords+4 < 2^w) :
    TickPhysicalABI.Inputs B clock (input B clock team step m) team step := by
  let dest := destEmbedding B.control (by omega : B.control+4 ≤ 2^w)
  constructor
  · intro i
    have hi := i.isLt
    have addr : (dest i).val=B.control+i.val := Fin.val_cast_of_lt (by omega)
    change fillSegment B.clockWords 4 _ _ (B.control+i.val) = _
    rw [fillSegment,ite_eq_right (by omega),← addr]
    have got := TickControlHeader.store_read dest (controls w team step (clock.phase step)) m i
    exact got.trans (by fin_cases i <;> simp [controls])
  · intro i
    have hi := i.isLt
    have ind : Fin.ofNat 4 (B.clockWords+i.val-B.clockWords) = i := by
      apply Fin.ext
      simp []
    change fillSegment B.clockWords 4 _ _ (B.clockWords+i.val) = _
    rw [fillSegment,ite_eq_left (by omega),ind]

private theorem header_ready (B : Layout) (clock : Clock) (M : Machine w pc r k)
    (team step : ℕ) (regH : Fin 5 ↪ Fin r) (P : Fin 10 → Fin pc)
    (exit : Fin pc) (c : Config w pc r) (m : Memory w)
    (header : ∀ i, M.code (P i) = TickControlHeader.emit P regH (destination w B.control)
      (TickControlHeader.markerAddr (clock.phase step) B.oldAux B.newAux) exit i)
    (here : c.pc=P 0) (idT : c.reg (regH 0) = (team : Word w)) (idS : c.reg (regH 1) = (step : Word w))
    (tag : c.reg (regH 2) = ((clock.phase step).tag : Word w))
    (marker : m (TickControlHeader.markerAddr (w:=w) (clock.phase step) B.oldAux B.newAux).val = 1) :
    ∃ d : Config w pc r, d.pc=exit ∧ advance M.program 10 c m=some (d,
      TickControlHeader.store (destination w B.control) (controls w team step (clock.phase step)) m) :=by
  obtain ⟨d,there,_,_,_,run⟩:=TickControlHeader.advance_header M P regH (destination w B.control)
    (TickControlHeader.markerAddr (clock.phase step) B.oldAux B.newAux) exit header c m here
  exact ⟨d,there,by simpa only [idT,idS,tag,marker,controls] using run⟩

attribute [local irreducible] TickClockWriter.expr TickGenerateTable.driver TickGenerateTable.emit

set_option maxHeartbeats 800000 in
theorem advance_entry (B : Layout) (clock : Clock) (M : Machine w pc r k)
    (team step : ℕ) (regH : Fin 5 ↪ Fin r) (P : Fin 10 → Fin pc)
    (C : Fin ((TickClockWriter.expr (w:=w) (k:=k) clock B.bits B.teams B.clockWords
      (B.control : Word w) (B.control+1 : ℕ)).labels+6) → Fin pc)
    (R : Fin (4+(TickClockWriter.expr (w:=w) (k:=k) clock B.bits B.teams B.clockWords
      (B.control : Word w) (B.control+1 : ℕ)).binds) ↪ Fin r)
    (exit : Fin pc) (c : Config w pc r) (m : Memory w)
    (header : ∀ i, M.code (P i) = TickControlHeader.emit P regH (destination w B.control)
      (TickControlHeader.markerAddr (clock.phase step) B.oldAux B.newAux) (TickGenerateTable.driver (TickClockWriter.expr (w:=w) (k:=k) clock B.bits B.teams
        B.clockWords (B.control : Word w) (B.control+1 : ℕ)) C 0) i)
    (cc : ∀ i, M.code (C i) = TickGenerateTable.emit (TickClockWriter.expr clock B.bits B.teams
      B.clockWords (B.control : Word w) (B.control+1 : ℕ)) (B.clockWords : Word w) (B.clockWords+4 : ℕ) C R exit i)
    (here : c.pc=P 0) (idT : c.reg (regH 0) = (team : Word w)) (idS : c.reg (regH 1) = (step : Word w))
    (tag : c.reg (regH 2) = ((clock.phase step).tag : Word w))
    (marker : m (TickControlHeader.markerAddr (w:=w) (clock.phase step) B.oldAux B.newAux).val = 1)
    (disjoint : B.control+4 ≤ B.clockWords) (fit : B.clockWords+4 < 2^w)
    (td : clock.groupDuration < 2^w) (tb : clock.beginTick < 2^w) (ts : step < 2^w) :
    ∃ t ≤ 1470, ∃ d : Config w pc r, d.pc=exit ∧ advance M.program t c m = some (d,input B clock team step m) := by
  let dest := destEmbedding B.control (by omega : B.control+4 ≤ 2^w)
  let vals := controls w team step (clock.phase step)
  let cached := TickControlHeader.store dest vals m
  obtain ⟨d,there,head⟩:=header_ready B clock M team step regH P
    (TickGenerateTable.driver (TickClockWriter.expr (w:=w) (k:=k) clock B.bits B.teams
        B.clockWords (B.control : Word w) (B.control+1 : ℕ)) C 0) c m header here idT idS tag marker
  have a0 : (B.control : Word w).val = B.control := Fin.val_cast_of_lt (by omega)
  have a1 : ((B.control+1 : ℕ) : Word w).val = B.control+1 := Fin.val_cast_of_lt (by omega)
  have t0 : cached (B.control : Word w).val = (team : Word w) := by
    have read := TickControlHeader.store_read dest vals m 0
    change cached ((B.control+0 : ℕ) : Word w).val = (team : Word w) at read
    simpa only [Nat.add_zero] using read
  have t1 : cached ((B.control+1 : ℕ) : Word w).val = (step : Word w) :=
    TickControlHeader.store_read dest vals m 1
  have ht : (B.control : Word w).val < B.clockWords := by rw [a0]; omega
  have hs : ((B.control+1 : ℕ) : Word w).val < B.clockWords := by rw [a1]; omega
  change advance M.program 10 c m = some (d,cached) at head
  obtain ⟨n,limit,f,done,run⟩ := TickClockWriter.generate clock B.bits B.teams B.clockWords
    B.control (B.control+1 : ℕ) M cached d team step td tb ts fit ht hs
    t0 t1 C R exit cc there
  exact ⟨10+n,by omega,f,done,advance_trans head run⟩

end ThreeFlat.RAM.TickNavigationEntry

end OAI
