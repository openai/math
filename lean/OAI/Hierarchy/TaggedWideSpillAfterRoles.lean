import OAI.Hierarchy.TaggedWideOrderedFacts
import OAI.Hierarchy.TaggedWideSpillOrder

namespace OAI
/-! # Retaining all four kinds of observations of the actual corrected spill sheets -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open ProbeStage.CoreBoard.HistoryRoles
open scoped BigOperators Classical

variable {W : ℕ}

/-- Readback from a corrected page only inspects that page's physical interval. -/
def PageLocal {n : ℕ} (page : Fin n→Scatter) (post : Fin n→Memory W→Prop) : Prop :=
  ∀i s t,(∀a,(page i).floor≤a→a<(page i).stop→t a=s a)→post i s→post i t

/-- A page can also retain an earlier operand snapshot, since every later
scatter preserves the entire prefix through the end of this page. -/
def PagePrefixLocal {n : ℕ} (page : Fin n→Scatter) (post : Fin n→Memory W→Prop) : Prop :=
  ∀i s t,(∀a,a<(page i).stop→t a=s a)→post i s→post i t

/-- All prior sheets from this phase are available, in addition to the
observations and low frame from the completed preceding phases. -/
def PageSteps {n : ℕ} (page : Fin n→Scatter) (post : Fin n→Memory W→Prop) (base : Memory W→Prop) : Prop :=
  ∀i s,base s→(∀j,j < i→post j s)→
    ∃t,((page i).code W).Exec s t (page i).ticks ∧ post i t ∧ ∀a,a<(page i).floor→t a=s a

private theorem append_local {a b : ℕ} {p : Fin a→Scatter} {q : Fin b→Scatter}
    {f : Fin a→Memory W→Prop} {g : Fin b→Memory W→Prop}
    (front : PagePrefixLocal p f) (back : PagePrefixLocal q g) : PagePrefixLocal (Fin.addCases p q) (Fin.addCases f g) := by
  intro i
  induction i using Fin.addCases with
  | left i=>simpa only [Fin.addCases_left] using front i
  | right j=>simpa only [Fin.addCases_right] using back j

private theorem append_steps {a b : ℕ} {p : Fin a→Scatter} {q : Fin b→Scatter}
    {f : Fin a→Memory W→Prop} {g : Fin b→Memory W→Prop} {base : Memory W→Prop}
    (front : PageSteps p f base) (back : PageSteps q g (fun s=>base s ∧ ∀i,f i s)) :
    PageSteps (Fin.addCases p q) (Fin.addCases f g) base := by
  intro i
  induction i using Fin.addCases with
  | left i=>
    intro s init earlier
    simp only [Fin.addCases_left]
    apply front i s init
    intro j hj
    simpa only [Fin.addCases_left] using earlier (j.castAdd b) hj
  | right i=>
    intro s init earlier
    simp only [Fin.addCases_right]
    apply back i s
    · refine ⟨init,fun j=>?_⟩
      have lt : j.castAdd b<Fin.natAdd a i := by change j.val<a+i.val;omega
      simpa only [Fin.addCases_left] using earlier (j.castAdd b) lt
    · intro j hj
      have lt : Fin.natAdd a j<Fin.natAdd a i := by change a+j.val<a+i.val;exact Nat.add_lt_add_left hj a
      simpa only [Fin.addCases_right] using earlier (Fin.natAdd a j) lt

private theorem shift_local {a b : ℕ} (eqn : a=b) {p : Fin b→Scatter} {f : Fin b→Memory W→Prop}
    (localReads : PagePrefixLocal p f) : PagePrefixLocal (p ∘ Fin.cast eqn) (f ∘ Fin.cast eqn) := by
  cases eqn
  exact localReads

private theorem shift_steps {a b : ℕ} (eqn : a=b) {p : Fin b→Scatter} {f : Fin b→Memory W→Prop}
    {base : Memory W→Prop} (runs : PageSteps p f base) : PageSteps (p ∘ Fin.cast eqn) (f ∘ Fin.cast eqn) base := by
  cases eqn
  exact runs

private theorem unshift {a b : ℕ} (eqn : a=b) (post : Fin b→Prop)
    (valid : ∀i,post (Fin.cast eqn i)) : ∀j,post j := by
  cases eqn
  exact valid

variable {T : ℕ} (z : SpillDates T) (rom oldWork start : ℕ)
    (count : ∀i,z.original.controlColumns i=SiteControls.fieldCount z.original.roleCount)
local notation "r" => 3*((T+1)*3)
local notation "roles" => z.roleSheet rom start
local notation "ballots" => z.ballot rom oldWork start
local notation "packets" => z.packetControl rom oldWork start
local notation "spills" => fun j=>z.spillControl rom oldWork start j count

/-- The original role, ballot, packet and spill observations survive on the
literal final memory of the entire dated machine. -/
theorem SpillDates.run_after_roles_prefix (original : Memory W)
    (rr : Fin r→Memory W→Prop) (br pr sr : Fin T→Memory W→Prop)
    (rLocal : PagePrefixLocal roles rr) (bLocal : PagePrefixLocal ballots br)
    (pLocal : PagePrefixLocal packets pr) (sLocal : PagePrefixLocal spills sr)
    (runRole : PageSteps roles rr (fun s=>∀a,a<start→s a=original a))
    (runBallot : PageSteps ballots br (fun s=>(∀a,a<start→s a=original a) ∧ ∀j,rr j s))
    (runPacket : PageSteps packets pr (fun s=>((∀a,a<start→s a=original a) ∧ ∀j,rr j s) ∧ ∀j,br j s))
    (runSpill : PageSteps spills sr (fun s=>(((∀a,a<start→s a=original a) ∧ ∀j,rr j s) ∧ ∀j,br j s) ∧ ∀j,pr j s)) :
    ∃out,(z.program W rom oldWork start count).Exec original out (z.ticks rom oldWork start count) ∧
      (∀i,rr i out) ∧ (∀i,br i out) ∧ (∀i,pr i out) ∧ (∀i,sr i out) ∧ ∀a,a<start → out a=original a := by
  let eqn : SpillDates.last T+1=r+(T+(T+T)):=by unfold SpillDates.last;omega
  let post : Fin (r+(T+(T+T))) → Memory W → Prop :=
    Fin.addCases rr (Fin.addCases br (Fin.addCases pr sr))
  have localReads:=append_local rLocal (append_local bLocal (append_local pLocal sLocal))
  have steps:=append_steps runRole (append_steps runBallot (append_steps runPacket runSpill))
  obtain ⟨out,run,all,frame⟩:=(z.ordered rom oldWork start count).run_prefix original (post ∘ Fin.cast eqn)
    (shift_local eqn localReads) (shift_steps eqn steps)
  have each:=unshift eqn (fun j=>post j out) all
  refine ⟨out,run,?_,?_,?_,?_,frame⟩
  · intro j
    simpa only [post,Fin.addCases_left] using each (j.castAdd (T+(T+T)))
  · intro j
    simpa only [post,Fin.addCases_right,Fin.addCases_left] using each (Fin.natAdd r (j.castAdd (T+T)))
  · intro j
    simpa only [post,Fin.addCases_right,Fin.addCases_left] using
      each (Fin.natAdd r (Fin.natAdd T (j.castAdd T)))
  · intro j
    simpa only [post,Fin.addCases_right] using each (Fin.natAdd r (Fin.natAdd T (Fin.natAdd T j)))

theorem SpillDates.run_after_roles (original : Memory W)
    (rr : Fin r→Memory W→Prop) (br pr sr : Fin T→Memory W→Prop)
    (rLocal : PageLocal roles rr) (bLocal : PageLocal ballots br)
    (pLocal : PageLocal packets pr) (sLocal : PageLocal spills sr)
    (runRole : PageSteps roles rr (fun s=>∀a,a<start→s a=original a))
    (runBallot : PageSteps ballots br (fun s=>(∀a,a<start→s a=original a) ∧ ∀j,rr j s))
    (runPacket : PageSteps packets pr (fun s=>((∀a,a<start→s a=original a) ∧ ∀j,rr j s) ∧ ∀j,br j s))
    (runSpill : PageSteps spills sr (fun s=>(((∀a,a<start→s a=original a) ∧ ∀j,rr j s) ∧ ∀j,br j s) ∧ ∀j,pr j s)) :
    ∃out,(z.program W rom oldWork start count).Exec original out (z.ticks rom oldWork start count) ∧
      (∀i,rr i out) ∧ (∀i,br i out) ∧ (∀i,pr i out) ∧ (∀i,sr i out) ∧ ∀a,a<start → out a=original a :=
  z.run_after_roles_prefix rom oldWork start count original rr br pr sr
    (fun i s t same=>rLocal i s t (fun a _ below=>same a below))
    (fun i s t same=>bLocal i s t (fun a _ below=>same a below))
    (fun i s t same=>pLocal i s t (fun a _ below=>same a below))
    (fun i s t same=>sLocal i s t (fun a _ below=>same a below))
    runRole runBallot runPacket runSpill

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
