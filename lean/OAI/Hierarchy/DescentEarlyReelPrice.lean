import OAI.Hierarchy.DescentNamedCountedReel
import OAI.Hierarchy.DescentEarlyMatrixBudget

namespace OAI
/-! # The measured count tape, original seventeen-column move and early matrix reel -/
namespace Hierarchy.DescentExteriorMatrixUpdate.Calendar
open DescentCompiler DescentExteriorShelf DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

theorem dated_names (cells : ℕ → Cell) (w age : ℕ) :
    names (dated cells w age) = 19+111*age := by
  induction age with
  | zero => rw [dated,names_scan]; rfl
  | succ a ih =>
    rw [dated,names_seq,ih,Cell.program,names_scan]
    change 19+111*a+(11+4*25)=_
    omega

theorem early_names (S : AtomSchedule) (k tail base : ℕ) (tag : ℕ→Bool)
    (rotation : ℕ→ℕ) (j r t E compact w : ℕ) :
    names (earlyProgram S k tail base tag rotation j r t E compact w) =
      123+15*(S.length*stride S k tail)+111*S.length := by
  let I:=sheet S k tail base tag w
  have size : I.length=S.length*stride S k tail := by
    change (base+S.length*stride S k tail)-base=_
    omega
  have rom:=I.hardware.2
  rw [size] at rom
  unfold earlyProgram
  rw [names_seq,names_seq,show names (sheet S k tail base tag w).program = _ from rom]
  rw [relocate,names_scan,Reel.program,names_seq,names_scan,publish,names_seq,dated_names,names_scan]
  change 15*(S.length*stride S k tail+1)+(11+4*7)+
    ((11+4*1)+(19+111*S.length+(11+4*6)))=_
  omega

/-- Every exterior plane row is moved in each of the seventeen physical columns. -/
theorem early_clock_rows (S : AtomSchedule) (k tail j r t E : ℕ) :
    306*(E*2^(j+r))≤earlyClock S k tail j r t E := by
  have room:=row_room (j:=j) (r:=r) (t:=t) (e:=E)
  change E*2^(j+r)≤ span j r t E at room
  unfold earlyClock
  omega

end
end Hierarchy.DescentExteriorMatrixUpdate.Calendar

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open Catalyst DescentCompiler DescentExteriorShelf DescentExteriorMatrixUpdate.Calendar
open DescentSixParty.Chronology DescentStaticWordColumn
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (S : AtomSchedule)
variable (base : ℕ) (tag : ℕ→Bool) (rotation loc : ℕ→ℕ) (lo compact k tail j r t w : ℕ)
set_option quotPrecheck false
local notation "occ" => (countDates 0 (kindCalendar S.rounds S.height)).length
local notation "ports" => Fintype.card (Port P X.width)
local notation "machine" => historyCountReel X S base tag rotation loc lo compact k tail j r t w

omit [Field F] in
theorem counted_names : names machine =
    15+18*occ+(123+15*(S.length*stride S k tail)+111*S.length) := by
  unfold historyCountReel
  rw [names_seq,(DescentLowCountBook.hardware ..).2,early_names]

private theorem count_le (xs : List Bool) (i : ℕ) : (countDates i xs).length≤xs.length := by
  induction xs generalizing i with
  | nil => simp [countDates]
  | cons b xs ih =>
    cases b <;> simp only [countDates,List.length_cons] <;> have := ih (i+1) <;> omega

private theorem active_count : occ≤S.length := by
  apply (count_le _ 0).trans
  change (List.replicate S.height (kindPeriod S.rounds)).flatten.length≤(S.rounds+1)*S.height
  generalize S.height=n
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.flatten_cons,List.length_append,kindPeriod,
      List.length_replicate,List.length_cons,List.length_nil,Nat.mul_succ] at *
    omega

omit [Field F] in
/-- The actual low observer and all seventeen original shelf columns are charged once. -/
theorem counted_tariff (h : ℕ) (rom : S.length*stride S k tail≤2^(h/2))
    (dates : S.length≤2^(h/2)) (look : tableBits j r t≤h/2) :
    (4+11*occ)+earlyClock S k tail j r t ports+7*names machine≤
      8192*(2^(h/2)+ports*2^(j+r)) := by
  rw [counted_names]
  have a:=active_count S
  have b:=span_price (j:=j) (r:=r) (t:=t) (e:=ports) look
  change span j r t ports≤2*(ports*2^(j+r))+1+2^(h/2) at b
  have portRoom:=Nat.le_mul_of_pos_right ports (Nat.two_pow_pos (j+r))
  have one:1≤2^(h/2):=Nat.one_le_two_pow
  unfold earlyClock
  omega

omit [Field F] in
/-- The exterior term in the open-host invoice pays for arbitrarily many actual ports. -/
theorem counted_open_price (h M copies s T factor : ℕ) (large : 10≤h)
    (support : 2^h≤2*(M*copies)) (power : T≤ s)
    (arch : w+1≤factor*h) (outside : copies=2^(j+(j+r))) (packed : h≤32*(2^j*s))
    (rom : S.length*stride S k tail≤2^(h/2)) (dates : S.length≤2^(h/2))
    (look : tableBits j r t≤h/2) :
    ((4+11*occ)+earlyClock S k tail j r t ports+7*names machine)*(w+1)*T≤
      (262144*factor)*((copies*s)*(M+T*ports)) := by
  have raw:=counted_tariff X S base tag rotation loc lo compact k tail j r t w h rom dates look
  exact DescentSixParty.early_open_words h M copies s T factor ports j r w _
    large support power arch outside packed raw

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
