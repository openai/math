import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentStaticWordColumn
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # A single public grain column for all operands of an ordinary date -/
namespace Hierarchy.DescentDatedPublicGrain
open DescentSIMDLookup DescentDatedPriorOperand DescentCompiler ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

/-- Number of p-bit words in one marked child bundle at this cut. -/
def amount (S : AtomSchedule) (b date : ℕ) := b^(S.rounds*S.height-S.ordinaryDone date)

theorem bits_per_bundle (S : AtomSchedule) (b p date : ℕ) :
    S.grainAt b p date=p*amount S b date := rfl

theorem amount_pos (S : AtomSchedule) {b : ℕ} (hb : 0<b) (date : ℕ) :
    0<amount S b date := Nat.pow_pos hb

theorem amount_fits (S : AtomSchedule) (b date size : ℕ) (radix : b≤2^S.capGain)
    (field : S.capGain*(S.rounds*S.height-S.ordinaryDone date)<size+2) :
    amount S b date<2^(size+2) := by
  calc
    _ ≤ (2^S.capGain)^(S.rounds*S.height-S.ordinaryDone date) := Nat.pow_le_pow_left radix _
    _ = 2^(S.capGain*(S.rounds*S.height-S.ordinaryDone date)) := (pow_mul ..).symm
    _ < _ := Nat.pow_lt_pow_right (by decide) field

def bank (l : Layout) (base : ℕ) : Bank := ⟨base,Nat.clog 2 l.rows⟩
def endAddress (l : Layout) (base : ℕ) := base+l.span

theorem capacity (l : Layout) (base : ℕ) : l.rows≤(bank l base).size :=
  Nat.le_pow_clog (by decide) _

theorem fits (l : Layout) {base stop w : ℕ} (room : endAddress l base≤ stop) (space : stop<2^w) :
    (bank l base).Fits w stop := by
  change 0<l.span ∧ l.span<2^w ∧ base+l.span≤ stop
  change base+l.span≤ stop at room
  exact ⟨Nat.two_pow_pos _,by omega,room⟩

/-- The original packed row uses the same digit for every genuine group.
Both the high lanes of its final chunk and the unused dyadic addresses are zero. -/
def literal (l : Layout) (grain : Cell (l.size+2)) (i : ℕ) : ℕ :=
  if hi : i<l.rows then
    (data (fun (_ : Fin l.hosts) (_ : Fin l.groups)=>grain)
      ((row l.hosts l.groups l.lanes).symm ⟨i,hi⟩)).val
  else 0

def program (l : Layout) (w base : ℕ) (grain : Cell (l.size+2)) :=
  DescentStaticWordColumn.program w base (literal l grain) l.span

def image (l : Layout) {w : ℕ} (base : ℕ) (grain : Cell (l.size+2)) (m : Memory w) :=
  DescentStaticWordColumn.image base (literal l grain) m l.span

def ticks (l : Layout) := 4+10*l.span

theorem run (l : Layout) {w : ℕ} (base : ℕ) (grain : Cell (l.size+2)) (m : Memory w)
    (room : endAddress l base<2^w) :
    (program l w base grain).Exec m (image l base grain m) (ticks l) :=
  DescentStaticWordColumn.mount base l.span _ m room

theorem cheap (l : Layout) (w base : ℕ) (grain : Cell (l.size+2)) :
    CheapCode (program l w base grain) := by
  have go (n : ℕ) : CheapCode (DescentStaticWordColumn.program w base (literal l grain) n) := by
    induction n with
    | zero=>apply scan_cheap
    | succ _ ih=>apply cheap_seq <;> first | exact @ih | apply scan_cheap
  exact @go l.span

theorem row_read (l : Layout) {w : ℕ} (base : ℕ) (grain : Cell (l.size+2)) (m : Memory w)
    (p : Row l.hosts l.groups l.lanes) :
    image l base grain m ((bank l base).base+(row l.hosts l.groups l.lanes p).val) =
      ((data (fun (_ : Fin l.hosts) (_ : Fin l.groups)=>grain) p).val:Word w) := by
  let r:=row l.hosts l.groups l.lanes p
  have hr : r.val<l.rows:=r.isLt
  have rd := DescentStaticWordColumn.read base l.span (literal l grain) m (hr.trans_le (capacity l base))
  refine rd.trans ?_
  unfold literal
  rw [dite_eq_left hr]
  change ((data (fun (_ : Fin l.hosts) (_ : Fin l.groups)=>grain)
    ((row l.hosts l.groups l.lanes).symm ((row l.hosts l.groups l.lanes) p))).val:Word w)=_
  rw [Equiv.symm_apply_apply]

theorem padding (l : Layout) {w : ℕ} (base : ℕ) (grain : Cell (l.size+2)) (m : Memory w)
    (p : Row l.hosts l.groups l.lanes) (lane : Fin l.lanes)
    (width : (l.size+2)*l.lanes≤w) :
    digit (l.size+2) lane.val (image l base grain m (base+(row l.hosts l.groups l.lanes p).val)).val =
      if p.2.val*l.lanes+lane.val<l.groups then grain.val else 0 := by
  have read:=row_read l base grain m p
  change image l base grain m (base+(row l.hosts l.groups l.lanes p).val)=_ at read
  rw [read]
  let val (j : Fin l.lanes) : Cell (l.size+2) :=
    if p.2.val*l.lanes+j.val<l.groups then grain else 0
  change digit (l.size+2) lane.val (((encode _ _ val).val:Word w)).val=_
  rw [Fin.val_cast_of_lt ((encode _ _ val).isLt.trans_le (Nat.pow_le_pow_right (by decide) width)),
    digit_encode]
  by_cases ok : p.2.val*l.lanes+lane.val<l.groups <;> simp [val,ok]

theorem tail_zero (l : Layout) {w : ℕ} (base : ℕ) (grain : Cell (l.size+2)) (m : Memory w)
    {i : ℕ} (past : l.rows≤ i) (inside : i<l.span) : image l base grain m (base+i)=0 := by
  have read:=DescentStaticWordColumn.read base l.span (literal l grain) m inside
  simpa only [image,literal,dite_eq_right (Nat.not_lt_of_ge past),Nat.cast_zero] using read

theorem frame (l : Layout) {w : ℕ} (base : ℕ) (grain : Cell (l.size+2)) (m : Memory w) (addr : ℕ)
    (away : addr<base ∨ endAddress l base≤addr) : image l base grain m addr=m addr :=
  DescentStaticWordColumn.frame base l.span _ m addr away

theorem span_bound (l : Layout) : l.span≤2*l.rows+1 := by
  let n:=l.rows
  change 2^Nat.clog 2 n≤2*n+1
  by_cases lo : n≤1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp lo with z|z <;> rw [z] <;> decide
  · have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
    cases dep : Nat.clog 2 n with
    | zero=>omega
    | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega

theorem fee (l : Layout) (w base : ℕ) (grain : Cell (l.size+2)) :
    DescentStaticWordColumn.names (program l w base grain)=15*(l.span+1) ∧
    ticks l+DescentStaticWordColumn.names (program l w base grain)+endAddress l base
      ≤128*(1+base+l.rows) := by
  have names:=DescentStaticWordColumn.names_mount w base (literal l grain) l.span
  change DescentStaticWordColumn.names (program l w base grain)=_ at names
  refine ⟨names,?_⟩
  rw [names]
  unfold ticks endAddress
  have := span_bound l
  omega

end
end Hierarchy.DescentDatedPublicGrain

end OAI
