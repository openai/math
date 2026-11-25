import OAI.ThreeFlat.Diagonal.NavigationRunBuckets
import OAI.ThreeFlat.Diagonal.NavigationSlotSchedule
import OAI.ThreeFlat.Diagonal.CursorGroupMass

namespace OAI
/-! # Every typed cursor history fits both packed group halves in the physical auxiliary word bank -/
namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open PhysicalStage HistoryContraction LinearAlgebra.SpectralBooks.VNP Computability.VPVNP.BurstRAM
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {d l : ℕ} {A : State d l}
variable (a : RootArchive) (r : Run F A) (h : r.plan.History) (C : r.Charges) (start pay : A.Site→ℕ)
local notation "b" => a.typedRoot r h
local notation "E" => r.terminalOrderEquiv h

theorem intrinsicAt (f : (r.plan.finish h).Site→ℕ) (i : Fin (b).rootCount) :
    (b).atRank r h f i=f ((E).symm i) := by
  have eqv (v : (r.plan.finish h).Site) : terminalRank r h v=i.val ↔ v=(E).symm i := by
    rw [show terminalRank r h v=(E v).val from (r.terminalOrderEquiv_val h v).symm]
    exact Fin.ext_iff.symm.trans (E).eq_symm_apply.symm
  simp only [atRank,eqv,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem intrinsicWork_sum :
    Team.ticks ((b).rankedWork r h C start) (b).ids=a.nodeBank.unitWork*r.rootTotal h C start := by
  simp only [Team.ticks,ids,List.map_ofFn,List.sum_ofFn,Function.comp_apply,rankedWork,intrinsicAt]
  rw [←r.chargeAt_sum h C start,←Finset.mul_sum]
  exact congrArg (a.nodeBank.unitWork * ·) ((E).symm.sum_comp (r.chargeAt h C start))

theorem intrinsicPairs_sum : Team.ticks ((b).rankedPairs r h pay) (b).ids=∑x,pay x := by
  simp only [Team.ticks,ids,List.map_ofFn,List.sum_ofFn,Function.comp_apply,rankedPairs,intrinsicAt]
  let mass (v : (r.plan.finish h).Site):=∑ z : {x // r.plan.destination h x=v},pay z.val
  change (∑ i,mass ((E).symm i))=_
  rw [(E).symm.sum_comp]
  exact Fintype.sum_fiberwise _ _

/-- Summing the selected root pair fields counts the same physical pairs in
the original leaves, including the last partial bucket. -/
theorem intrinsicGroup_mass (owner : Fin (b).rootCount→ℕ) (g : ℕ) :
    (∑ x : A.Site, if owner (E (r.plan.destination h x))=g then pay x else 0)=
      ∑ i : Fin (b).rootCount, if owner i=g then (b).rankedPairs r h pay i else 0 := by
  let mass (v : (r.plan.finish h).Site):=∑ z : {x // r.plan.destination h x=v},pay z.val
  let term (v : (r.plan.finish h).Site):=if owner (E v)=g then mass v else 0
  have atRoot (i : Fin (b).rootCount) :
      (if owner i=g then (b).rankedPairs r h pay i else 0)=term ((E).symm i) := by
    let j : Fin (Fintype.card (r.plan.finish h).Site) := i
    have eo : owner ((E) ((E).symm j)) = owner j := congrArg owner ((E).apply_symm_apply j)
    simp only [rankedPairs,intrinsicAt,term,mass]
    change (if owner j = g then _ else 0) = (if owner ((E) ((E).symm j)) = g then _ else 0)
    rw [eo]
  simp_rw [atRoot]
  refine Eq.trans ?_ ((E).symm.sum_comp term).symm
  let dest : A.Site → (r.plan.finish h).Site := fun x => r.plan.destination h x
  let amount (x : A.Site) := if owner (E (dest x)) = g then pay x else 0
  refine (Fintype.sum_fiberwise dest amount).symm.trans ?_
  apply Finset.sum_congr rfl
  intro v _
  have same (z : {x : A.Site // dest x = v}) :
      owner (E (dest z.val)) = owner (E v) :=
    congrArg (fun site : (r.plan.finish h).Site => owner (E site)) z.property
  change (∑ z : {x : A.Site // dest x = v}, amount z.val) =
    (if owner (E v) = g then mass v else 0)
  by_cases yes : owner (E v) = g
  · rw [ite_eq_left yes]
    change _ = ∑ z : {x : A.Site // dest x = v}, pay z.val
    apply Finset.sum_congr rfl
    intro z _
    exact ite_eq_left ((same z).trans yes)
  · rw [ite_eq_right yes]
    apply Finset.sum_eq_zero
    intro z _
    exact ite_eq_right (fun hit => yes ((same z).symm.trans hit))


end
end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.Parameters
open PhysicalStage RAM RAM.NavigationNodeRows NavigationDirectory TickPhaseModel TickChronology RootArchive
open LinearAlgebra.SpectralBooks.VNP Computability.VPVNP.BurstRAM
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F)
variable {u rem low stride cells tableOffset tariff e Aexp : ℕ} (shape : PhysicalPinsExpr.Shape)
local notation "p" => Parameters.cursor B u rem low stride cells shape tableOffset tariff
local notation "W" => (16*u^10)
local notation "P" => B.repeat (u^8)
local notation "k" => ((P).charge+rem)
local notation "off" => (1+((k+low)+(k+low)))
local notation "A" => (p).archive (2^B.exponent 0) W
local notation "ss" => (P).directory rem (p).axes
local notation "n" => (p).nodeArchive A ss W
local notation "a" => (p).rootArchive A n ss W
variable (hk : 2 ≤ (B.repeat (u^8)).charge + rem)
local notation "X" => B.cursorState hk low off cells
local notation "R" => (P).run rem X
local notation "C" => B.charges (u^8) rem X
local notation "start" => B.seedWork hk low off cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells
local notation "pay" => B.clippedPairs hk low off cells (2*shape.halfBits)
variable (clock : Clock) (groups : 0<clock.groups) (total : clock.chunks=2*shape.chunks)
    (cover : 2*shape.halfBits ≤ 2^(((B.repeat (u^8)).charge+rem)+low))
local notation "T" => cursorBuckets B u rem low stride cells tableOffset tariff shape hk clock groups total cover
local notation "teams" => (clock.evaluateTicks*2^(u^3))
local notation "rootOf" => (a).typedRoot R

/-- The schedule denominator and the terminal maxima hold before any transcript
is supplied. The order is the actual physical base-and-lane order of this branch. -/
theorem cursor_intrinsic_facts (age : 512≤u) (hu : e+40≤u) (half : low≤u^10/2)
    (axes : k≤u^11) (depth : k+low≤u^10+2*u^6) (deg : 2^(B.exponent 0)≤u) (slot : off*cells*3≤u^e)
    (trace : TraceBitHeader.seedTraceWork low stride cells B.cursorCopies (k+low)≤2^low*u^e)
    (level : B.levels+1≤u) (coeff : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (peak : B.peakBase≤u) (unit : 0<tariff) (price : tariff≤u^e)
    (save : 146+2*e+26+(TraceVolume.cm+2)≤Aexp) (volume : 2^(k+low)≤2*FoldTrace.hFuel u Aexp)
    (chunks : 0<shape.chunks) (bits : shape.bits=2^(u^10-u^4))
    (timetable : 2^(u^6)=4*((a).groups*clock.evaluateTicks)) (pins : 2*shape.halfBits≤2^(k+low)) (h : (R).plan.History) :
    ScheduleFacts (rootOf h) W teams ((rootOf h).rankedWork R h C start) ((rootOf h).rankedPairs R h pay) (rootOf h).ids := by
  let b:=rootOf h
  have young : 40≤u := (by decide : 40≤512).trans age
  have scaled : (R).rootTotal h ((R).scaled tariff C) (fun x => tariff * start x)
      ≤ FoldTrace.total u/u^(Aexp-(146+2*e+26)) :=
    B.cursor_total_work (u:=u) (rem:=rem) (low:=low) («off»:=off) (slots:=cells)
      (total:=2*shape.halfBits) (copies:=B.cursorCopies) (depth:=k+low) (stride:=stride) (cells:=cells)
      (e:=e) (unitWork:=tariff) (Aexp:=Aexp) young hk axes deg slot trace level coeff
      energy growth price (by omega : 146+2*e+26≤Aexp) volume h
  apply cursor_schedule_scalars (u:=u) (e:=e) (Aexp:=Aexp) b shape clock.evaluateTicks
    (b.rankedWork R h C start) (b.rankedPairs R h pay) age save
    (pins.trans (Nat.pow_le_pow_right (by decide) depth)) chunks bits rfl rfl rfl timetable
  refine ⟨?_,?_,?_⟩
  · refine (intrinsicPairs_sum a R h pay).trans ((B.clippedPairs_sum hk low off cells (2*shape.halfBits)).trans ?_)
    apply min_eq_left
    simpa only [Nat.pow_add] using pins
  · exact (intrinsicWork_sum a R h C start).le.trans
      (((R).rootTotal_scaled h C start tariff).ge.trans scaled)
  · intro i
    let v:=((R).terminalOrderEquiv h).symm i
    let mass (t : ((R).plan.finish h).Site) := ∑ x : {x // (R).plan.destination h x=t}, pay x.val
    have pairAt : b.rankedPairs R h pay i=mass v := intrinsicAt a R h mass i
    have workAt : b.rankedWork R h C start i=tariff*(R).chargeAt h C start v :=
      intrinsicAt a R h (fun t => tariff*(R).chargeAt h C start t) i
    have localCharge : 1+(R).terminalIncident h v+mass v≤(R).chargeAt h C start v :=
      B.terminal_charge_covers (u^8) rem X h start pay
        (B.seedWork_covers hk low off cells (2*shape.halfBits) B.cursorCopies (k+low) stride cells) v
    have gain : mass v<(R).chargeAt h C start v :=
      (Nat.lt_add_of_pos_left (Nat.add_pos_left (by decide) ((R).terminalIncident h v))).trans_le localCharge
    have exp : u^e≤u^(e+2) := Nat.pow_le_pow_right ((by decide : 0<40).trans_le young) (Nat.le_add_right e 2)
    refine ⟨pairAt.le.trans_lt ((gain.trans_le (Nat.le_mul_of_pos_left _ unit)).trans_eq workAt.symm),workAt.le.trans ?_⟩
    rw [Nat.mul_comm]
    exact B.cursor_terminal_peak (e:=e+2) young ((Nat.add_le_add_left (by decide : 2≤40) e).trans hu)
      half peak (slot.trans exp) hk h start
      (B.cursor_start_le (e:=e) ((by decide : 4≤40).trans young) hk deg slot trace) (price.trans exp) v

/-- Both old and fresh bits of a group, and the common half-register, fit at
every history. This is independent of the assembler's proposed memory image. -/
theorem cursor_group_room (ng : (a).groups=clock.groups) (word : (a).groups<2^W) (chunks : 0 < shape.chunks)
    (two : 2 ≤ shape.bits) (v : HistoryContraction.Plan.Terminal (R).plan ((R).readTerminal (fun Y=>Y.widthSum)))
    (facts : ScheduleFacts (rootOf v.1) W teams ((rootOf v.1).rankedWork R v.1 C start)
      ((rootOf v.1).rankedPairs R v.1 pay) (rootOf v.1).ids) (g : ℕ) :
    1+shape.bits/2+2*(T).length v g ≤ shape.bits := by
  let b:=rootOf v.1
  let work:=b.rankedWork R v.1 C start
  let mass:=b.rankedPairs R v.1 pay
  let owner (i : Fin b.rootCount):=b.groupWord W teams work mass i.val
  have bounds : (∀i,owner i<b.groups) ∧ ∀z,b.groups*(∑i,if owner i=z then mass i else 0)≤4*b.totalPairs :=
    groupWord_bounds b teams work mass facts word
  have group (j : ((R).plan.finish v.1).Site) : ((T).group v.1 j).val=owner (((R).terminalOrderEquiv v.1) j) := by
    have ord : terminalRank R v.1 j=(((R).terminalOrderEquiv v.1) j).val :=
      ((R).terminalOrderEquiv_val v.1 j).symm
    change b.groupWord W teams work mass (terminalRank R v.1 j)%clock.groups=_
    rw [ord];exact Nat.mod_eq_of_lt ((bounds.1 _).trans_eq ng)
  have full : clock.chunks*shape.bits=2*shape.halfBits := by rw [total];exact Nat.mul_assoc ..
  have length : (T).length v g=∑i,if owner i=g then mass i else 0 := by
    rw [B.cursor_length_sum hk low off cells R _ clock shape.bits T (fun _=>rfl),full]
    simp_rw [group]
    exact intrinsicGroup_mass a R v.1 pay owner g
  have bound : (a).groups*(T).length v g≤4*(a).totalPairs := by rw [length];exact bounds.2 g
  have packed : 256*(T).length v g ≤ shape.bits := by
    apply Nat.le_of_mul_le_mul_left (c:=4*(2*shape.chunks)) _ (by positivity)
    calc 4*(2*shape.chunks)*(256*(T).length v g)=(a).groups*(T).length v g := by
           change _=1024*(2*shape.chunks)*_;ring
         _ ≤4*(a).totalPairs := bound
         _ =4*(2*shape.chunks)*shape.bits := by change 4*(2*(shape.chunks*shape.bits))=_;ring
  omega

theorem cursor_pairSpace (age : 512≤u) (hu : e+40≤u) (half : low≤u^10/2)
    (axes : k≤u^11) (depth : k+low≤u^10+2*u^6) (deg : 2^(B.exponent 0)≤u) (slot : off*cells*3≤u^e)
    (trace : TraceBitHeader.seedTraceWork low stride cells B.cursorCopies (k+low)≤2^low*u^e)
    (level : B.levels+1≤u) (coeff : B.costFactors.sum≤u) (energy : 4*Real.sqrt B.blockError≤(u:ℝ))
    (growth : Real.sqrt B.stageGrowth≤(u:ℝ)) (peak : B.peakBase≤u) (unit : 0<tariff) (price : tariff≤u^e)
    (save : 146+2*e+26+(TraceVolume.cm+2)≤Aexp) (volume : 2^(k+low)≤2*FoldTrace.hFuel u Aexp)
    (chunks : 0 < shape.chunks) (bits : shape.bits=2^(u^10-u^4))
    (timetable : 2^(u^6)=4*((a).groups*clock.evaluateTicks)) (ng : (a).groups=clock.groups)
    (v : HistoryContraction.Plan.Terminal (R).plan ((R).readTerminal (fun Y=>Y.widthSum))) (g : ℕ) :
    1+shape.bits/2+2*(T).length v g ≤ shape.bits := by
  have pos : 0<u := by omega
  have eval : 0<clock.evaluateTicks := by
    by_contra! hn
    rw [show clock.evaluateTicks=0 by omega,Nat.mul_zero,Nat.mul_zero] at timetable
    exact Nat.ne_of_gt (Nat.two_pow_pos _) timetable
  have payFit : (a).groups<2^W := by
    have charged : (a).groups≤2^(u^6) := by rw [timetable];exact
      (Nat.le_mul_of_pos_right _ eval).trans (Nat.le_mul_of_pos_left _ (by decide))
    exact charged.trans_lt (Nat.pow_lt_pow_right (by decide)
      (show u^6<W from (Nat.pow_le_pow_right pos (by decide : 6≤10)).trans_lt (by nlinarith [(show 0<u^10 from Nat.pow_pos pos)])))
  have lowBits : 2 ≤ shape.bits := by
    have gap : u^4 < u^10 := Nat.pow_lt_pow_right (by omega : 1 < u) (by decide : 4 < 10)
    rw [bits]
    exact Nat.le_self_pow (by omega : u^10-u^4 ≠ 0) 2
  exact cursor_group_room B shape hk clock groups total cover ng payFit chunks lowBits v
    (cursor_intrinsic_facts B shape hk clock age hu half axes depth deg slot trace level coeff energy growth peak
      unit price save volume chunks bits timetable cover v.1) g


end
end ThreeFlat.Diagonal.NavigationPass.Parameters

end OAI
