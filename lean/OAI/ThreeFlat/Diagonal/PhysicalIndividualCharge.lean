import OAI.ThreeFlat.Diagonal.PhysicalTerminalDegree
import OAI.ThreeFlat.Diagonal.PhysicalTerminalPorts
import OAI.ThreeFlat.Diagonal.PhysicalTerminalMass
import OAI.ThreeFlat.Diagonal.PhysicalArchiveBounds
import OAI.ThreeFlat.Diagonal.PhysicalStateHalfRows
import OAI.ThreeFlat.Diagonal.PhysicalArchiveJoin
import OAI.ThreeFlat.Diagonal.NumberedArchiveSites
import OAI.ThreeFlat.Diagonal.PhysicalLevelCaps
import OAI.ThreeFlat.Diagonal.PhysicalArchiveRows
import OAI.ThreeFlat.Diagonal.TickScratchRegion
import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly
import OAI.ThreeFlat.Diagonal.PhysicalRefreshOutput
import OAI.ThreeFlat.RAM.NavigationNodeRows
import OAI.ThreeFlat.Diagonal.HistoryRootDirectory
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily
import OAI.ThreeFlat.Diagonal.TraceCursorState
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule
import OAI.ThreeFlat.Diagonal.PhysicalPeakCharges

namespace OAI
/-! # Individual terminal charges in native words and archived site rows -/

namespace ThreeFlat.Diagonal.PhysicalStage.Block

/-- At the selected age the repeated maximum charge, both cursor-word widths, and
the final compiler coefficient fit in the native terminal charge allowance. -/
theorem peak_native_arithmetic {u e low : ℕ} (hu : 40≤u) (he : e≤u) (hlo : low≤u^10/2) :
    u^(u^8)*(1+2^low*u^e+2^low*u^e)*u^e ≤ 2^((3*u^10+4)/5) := by
  have iter : u^(u^8) ≤ 2^(u^9) := by
    calc u^(u^8) ≤ (2^u)^(u^8) := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2^(u^9) := by rw [← pow_mul]; congr 1; ring
  have small : u^e ≤ 2^(u^2) := by
    calc u^e ≤ (2^u)^e := Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2^(u*e) := (pow_mul ..).symm
      _ ≤ 2^(u^2) := Nat.pow_le_pow_right (by decide) (by simpa [pow_two] using Nat.mul_le_mul_left u he)
  have term : 2^low*u^e ≤ 2^(low+u^2) := by rw [pow_add]; exact Nat.mul_le_mul_left _ small
  have header : 1+2^low*u^e+2^low*u^e ≤ 2^(low+u^2+2) := by
    calc 1+2^low*u^e+2^low*u^e ≤ 4*2^(low+u^2) := by
           have positive : 0 < 2^(low+u^2) := by positivity
           omega
      _ = 2^(low+u^2+2) := by rw [pow_add]; ring
  have degree : 40*u^9 ≤ u^10 := by
    calc 40*u^9 ≤ u*u^9 := Nat.mul_le_mul_right _ hu
      _ = u^10 := by ring
  have square : u^2 ≤ u^9 := Nat.pow_le_pow_right (by omega) (by decide)
  have one := Nat.le_self_pow (by decide : 2≠0) u
  have exp : u^9+(low+u^2+2)+u^2 ≤ (3*u^10+4)/5 := by omega
  calc u^(u^8)*(1+2^low*u^e+2^low*u^e)*u^e ≤
        (2^(u^9)*2^(low+u^2+2))*2^(u^2) := Nat.mul_le_mul (Nat.mul_le_mul iter header) small
    _ = 2^(u^9+(low+u^2+2)+u^2) := by rw [← pow_add,← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) exp


end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage.Block

noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The actual terminal site's charged native work satisfies the cell cap of the
capacity schedule. The tariff and leaf bounds may be specialized to the native rows. -/
theorem cursor_terminal_peak {u rem low off slots e unitWork : ℕ}
    (hu : 40 ≤ u) (he : e ≤ u) (half : low ≤ u^10/2) (growth : B.peakBase ≤ u)
    (slot : off*slots*3 ≤ u^e) (hk : 2 ≤ (B.repeat (u^8)).charge+rem)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History)
    (start : (B.cursorState hk low off slots).Site → ℕ) (hs : ∀ a, start a ≤ 2^low*u^e)
    (tariff : unitWork ≤ u^e)
    (v : (((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.finish h).Site) :
    ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).chargeAt h
      (B.charges (u^8) rem (B.cursorState hk low off slots)) start v * unitWork ≤ 2^((3*u^10+4)/5) := by
  let A := B.cursorState hk low off slots
  have old : A.maxWidth ≤ 2^low*u^e := A.maxWidth_le fun x => by
    change (B.cursorState hk low off slots).width x ≤ _
    rw [B.cursorState_width]
    exact Nat.mul_le_mul_left _ slot
  have each := B.individual_terminal_charge (u^8) rem A h start (2^low*u^e) hs v
  apply (Nat.mul_le_mul each tariff).trans
  apply le_trans _ (peak_native_arithmetic hu he half)
  apply Nat.mul_le_mul_right
  exact Nat.mul_le_mul (Nat.pow_le_pow_left growth _) (by omega)

end
end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]


end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open RAM.NavigationNodeRows RAM.HistoryNodeDirectory HistoryContraction
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

namespace Run

private theorem archive_parent_valid {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ)
    (stored : r.ArchiveRowsStored b mem h C O p) (i : ℕ) (inside : O.layer.first ≤ i)
    (old : i < (r.finalArchive h C O p).1.first) :
    i< mem (b.nodes+8*i+1) ∧ mem (b.nodes+8*i+1)<(r.finalArchive h C O p).1.first+(r.finalArchive h C O p).1.count := by
  induction r generalizing b mem i with
  | done A => exact False.elim ((Nat.not_lt_of_ge inside) old)
  | step R next ih =>
    let t := h.1
    let s := p.1.sites
    have cont : s.layer.first=O.layer.first+O.layer.count := p.1.row.contiguous
    by_cases early : i<s.layer.first
    · let a := O.ord.symm ⟨i-O.layer.first,by omega⟩
      have addr : O.id a=i := by
        dsimp only [State.ArchiveSites.id,a]
        rw [Equiv.apply_symm_apply,Nat.add_sub_of_le inside]
      have written : mem (b.nodes+8*i+1)=s.id (R.parent t a) := addr ▸ stored.2.1 a
      rw [written]
      have extended := (next t).archive_bounds (tailHistory R next h) (C.2 t) s p.2
      exact ⟨early.trans_le (Nat.le_add_right _ _), (s.id_lt _).trans_le extended.2⟩
    · exact ih t (tailHistory R next h) (C.2 t) s p.2 b mem stored.2.2 i (Nat.le_of_not_gt early) old

/-- The actual S44 parent column gives a strictly ascending chronology until
the final layer, starting at the zero-based initial site allocation. -/
def archiveDirectory {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ)
    (stored : r.ArchiveRowsStored b mem h C O p) (zero : O.layer.first=0)
    (final roots : ℕ) (first : final=(r.finalArchive h C O p).1.first)
    (count : roots=(r.finalArchive h C O p).1.count) : Chronology (final+roots) where
  firstFinal := final
  bounded := Nat.le_add_right _ _
  parent i := if hi : i.val<final then ⟨mem (b.nodes+8*i.val+1), by
    have bound := (r.archive_parent_valid h C O p b mem stored i.val
      (by rw [zero]; exact Nat.zero_le _) (hi.trans_eq first)).2
    exact bound.trans_eq (congrArg₂ Nat.add first.symm count.symm)⟩ else i
  later i hi := by
    rw [dite_eq_left hi]
    exact (r.archive_parent_valid h C O p b mem stored i.val (by rw [zero];omega) (hi.trans_eq first)).1

theorem archiveDirectory_parent {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ)
    (stored : r.ArchiveRowsStored b mem h C O p) (zero : O.layer.first=0)
    (final roots : ℕ) (first : final=(r.finalArchive h C O p).1.first)
    (count : roots=(r.finalArchive h C O p).1.count) (i : Fin (final+roots)) (hi : i.val<final) :
    ((r.archiveDirectory h C O p b mem stored zero final roots first count).parent i).val = mem (b.nodes+8*i.val+1) := by
  simp only [archiveDirectory,dite_eq_left hi]

/-- Following the published absolute parent IDs reaches the true terminal tensor site. -/
theorem root_of_archive {n : ℕ} (D : Chronology n) (b : Banks) (mem : ℕ→ℕ)
    (parent : ∀ i : Fin n, i.val<D.firstFinal → (D.parent i).val=mem (b.nodes+8*i.val+1))
    {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (stored : r.ArchiveRowsStored b mem h C O p)
    (first : D.firstFinal=(r.finalArchive h C O p).1.first)
    (a : A.Site) (j : Fin n) (addr : j.val=O.id a) :
    D.root j = ((r.finalArchive h C O p).2 (r.rawDestination h a)).val := by
  induction r generalizing j with
  | done A =>
    change D.firstFinal=O.layer.first at first
    change j.val=O.layer.first+(O.ord a).val at addr
    rw [Chronology.root,dite_eq_right (show ¬j.val<D.firstFinal by omega)]
    change j.val-D.firstFinal=(O.ord a).val
    omega
  | step R next ih =>
    let t := h.1
    let s := p.1.sites
    have co : s.layer.first=O.layer.first+O.layer.count := p.1.row.contiguous
    have fin := ((next t).archive_bounds (tailHistory R next h) (C.2 t) s p.2).1
    have lim : O.layer.first+O.layer.count≤D.firstFinal := co ▸ (fin.trans_eq first.symm)
    have old : j.val<D.firstFinal := addr.symm ▸ (O.id_lt a).trans_le lim
    rw [Chronology.root,dite_eq_left old]
    apply ih t (tailHistory R next h) (C.2 t) s p.2 stored.2.2 first (R.parent t a) (D.parent j)
    rw [parent j old,addr]
    exact stored.2.1 a


end Run
end
end ThreeFlat.Diagonal.PhysicalStage




namespace ThreeFlat.Diagonal.PhysicalStage

open HistoryContraction RAM.NavigationNodeRows
noncomputable section

/-- A predicate can refer to the actual chronological row, its branch number,
its old owner numbering, and that branch's fresh local charge. -/
abbrev Move.VisitPredicate (F : Type) [Field F] :=
  ∀ {d l D L : ℕ} {A : State d l} (R : Move F A D L) (t : Fin R.rules.count)
    (O : A.ArchiveSites) (charge : (R.next t).Site→ℕ), R.ArchiveStep t O charge → Prop

namespace Run
variable {F : Type} [Field F]

/-- The predicate holds on each of the specific rows carried by this dependent archive path. -/
def ArchiveVisits (vis : Move.VisitPredicate F) :
    {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) → (C : r.Charges) →
      (O : A.ArchiveSites) → r.ArchivePath h C O → Prop
  | _, _, _, .done _, _, _, _, _ => True
  | _, _, _, .step R next, h, C, O, p =>
    vis R h.1 O (C.1 h.1) p.1 ∧
      ArchiveVisits vis (next h.1) (tailHistory R next h) (C.2 h.1) p.1.sites p.2

private theorem archiveVisits_transport (vis : Move.VisitPredicate F) {d l : ℕ} {A : State d l}
    (r : Run F A) {h h' : r.plan.History} (e : h=h') (C : r.Charges) (O : A.ArchiveSites)
    (p : r.ArchivePath h C O) (witness : ArchiveVisits vis r h C O p) :
    ArchiveVisits vis r h' C O (e ▸ p) := by cases e;exact witness

/-- A separately checked real head row and its actual tail form one verified path. -/
theorem joined_visits {d l D L : ℕ} {A : State d l} (R : Move F A D L) (next : ∀ t,Run F (R.next t))
    (C : (Run.step R next).Charges) (O : A.ArchiveSites) (j : Fin R.rules.count)
    (h : (next j).plan.History) (row : R.ArchiveStep j O (C.1 j))
    (p : (next j).ArchivePath h (C.2 j) row.sites) (vis : Move.VisitPredicate F)
    (head : vis R j O (C.1 j) row) (rest : ArchiveVisits vis (next j) h (C.2 j) row.sites p) :
    ArchiveVisits vis (Run.step R next) (joinHistory R next j h) C O (joinArchivePath R next C O j h row p) :=
  ⟨head,archiveVisits_transport vis (next j) (tailHistory_joinHistory R next j h).symm
    (C.2 j) row.sites p rest⟩

/-- Reinterpret the very same selected rows by pointwise implication. -/
theorem ArchiveVisits.mono {vis vis' : Move.VisitPredicate F}
    (imp : ∀ {d l D L : ℕ} {A : State d l} (R : Move F A D L) (j : Fin R.rules.count)
      (O : A.ArchiveSites) (charge : (R.next j).Site→ℕ) (row : R.ArchiveStep j O charge),
      vis R j O charge row → vis' R j O charge row) :
    {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) → (C : r.Charges) →
      (O : A.ArchiveSites) → (p : r.ArchivePath h C O) →
        ArchiveVisits vis r h C O p → ArchiveVisits vis' r h C O p
  | _, _, _, .done _, _, _, _, _, _ => True.intro
  | _, _, _, .step R next, h, C, O, p, seen =>
    ⟨imp R h.1 O (C.1 h.1) p.1 seen.1,
      ArchiveVisits.mono imp (next h.1) (tailHistory R next h) (C.2 h.1) p.1.sites p.2 seen.2⟩

end Run
end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM

/-- All earlier data addresses and all earlier headers survive the rest of the native
navigation passes. The two changing control registers are accounted for explicitly. -/
def SavedFrame {W : ℕ} (cur ctr : Word W) (headerEnd nextHeader nextHeap : ℕ)
    (issued latest : Memory W) : Prop :=
  ∀ i,i≠cur.val→i≠ctr.val→(i<nextHeader ∨ headerEnd≤ i)→i<nextHeap→latest i=issued i

/-- The two-control navigation loop preserves the actual source-degree header
word that the selected history body later reads. -/
theorem SavedFrame.familyDegree {W K headerEnd d : ℕ} {cur ctr : Word W} {out later : Memory W}
    (c : NavigationDirectory.Cursor) (q : NavigationDirectory.Stage)
    (frame : SavedFrame cur ctr headerEnd (NavigationDirectory.allocate K c q).next.header
      (NavigationDirectory.allocate K c q).next.heap out later)
    (beforeHeap : c.header+64≤c.heap)
    (control : (NavigationDirectory.allocate K c q).next.heap≤cur.val)
    (counter : (NavigationDirectory.allocate K c q).next.heap≤ctr.val)
    (native : (out (c.header+48)).val=d) : (later (c.header+48)).val=d := by
  have head : (NavigationDirectory.allocate K c q).next.header=c.header+64 := by cases q <;> rfl
  have heap := NavigationDirectory.heap_step K c q
  rw [frame _ (by omega) (by omega) (Or.inl (by omega)) (by omega)]
  exact native

theorem SavedFrame.transfer {W : ℕ} {cur ctr : Word W} {h c n endHeap : ℕ} {out m m' : Memory W}
    (f : SavedFrame cur ctr h c n out m) (limit : n≤endHeap) (same : ∀ i,i<endHeap→m' i=m i) :
    SavedFrame cur ctr h c n out m' :=
  fun i hc ht hdr small=>(same i (small.trans_le limit)).trans (f i hc ht hdr small)

end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage.Block
noncomputable section
variable {F : Type} [Field F] (B : Block F)

/-- The terminal peak theorem controls real intermediate tape allocations,
including all sites below the selected terminal tensor. -/
theorem cursor_all_levels_peak {u rem low off slots e unitWork : ℕ}
    (hu : 40≤u) (he : e≤u) (half : low≤u^10/2) (growth : B.peakBase≤u)
    (slot : off*slots*3≤u^e) (hk : 2≤(B.repeat (u^8)).charge+rem)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History)
    (start : (B.cursorState hk low off slots).Site→ℕ) (hs : ∀ x,start x≤2^low*u^e) (tariff : unitWork≤u^e) :
    Run.LevelsCapped unitWork (2^((3*u^10+4)/5)) ((B.repeat (u^8)).run rem (B.cursorState hk low off slots))
      h (B.charges (u^8) rem (B.cursorState hk low off slots)) start := by
  apply Run.levels_capped_of_terminal
  exact B.cursor_terminal_peak hu he half growth slot hk h start hs tariff

end
end ThreeFlat.Diagonal.PhysicalStage.Block

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]
namespace Run

/-- Half-port word counts and original clipped-pair counts remain chargeable
at every physical level before the terminal root. -/
def PortFloors : {d l : ℕ} → {A : State d l} → (r : Run F A) →
    (h : r.plan.History) → r.Charges → (A.Site→ℕ) → (A.Site→ℕ) → Prop
  | _,_,A,.done _,_,_,work,pairs=>∀ x,1+A.incidentWidth x+pairs x≤work x
  | _,_,A,.step R next,h,C,work,pairs=>(∀ x,1+A.incidentWidth x+pairs x≤work x) ∧
    PortFloors (next h.1) (tailHistory R next h) (C.2 h.1) (R.push h.1 (C.1 h.1) work)
      (fiberMass (R.parent h.1) pairs)

theorem port_floors {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (floor : r.LocalFloor C) (work pairs : A.Site→ℕ)
    (start : ∀ x,1+A.incidentWidth x+pairs x≤work x) : PortFloors r h C work pairs := by
  induction r with
  | done _=>exact start
  | step R next ih=>
    refine ⟨start,ih h.1 (tailHistory R next h) (C.2 h.1) (floor h.1).2 _ _ ?_⟩
    intro v
    apply Nat.add_le_add ((floor h.1).1 v)
    apply Finset.sum_le_sum
    intro x _
    have:=start x.val
    omega

end Run

theorem Block.port_floors (B : Block F) (n rem : ℕ) (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) (work pairs : A.Site→ℕ)
    (start : ∀ x,1+A.incidentWidth x+pairs x≤work x) :
    Run.PortFloors ((B.repeat n).run rem A) h (B.charges n rem A) work pairs :=
  Run.port_floors _ h _ ((B.repeat n).certified_floor _ (B.factor_bound n) rem A) work pairs start

end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
noncomputable section
variable {F : Type} [Field F]
namespace Block
variable (B : Block F)

theorem terminalSevenRows_onLanes {u lanes n rem : ℕ} (age : 40≤u) (degree : 2^B.exponent 0≤u)
    (A : State (2^B.exponent 0) lanes) (budget : lanes=(B.repeat n).charge+rem)
    (h : (Program.recast budget A ((B.repeat n).run rem (budget ▸ A))).plan.History) :
    7*(2*((Program.recast budget A ((B.repeat n).run rem (budget ▸ A))).terminalLayer h).degree+2)≤TickWorkspace.stride u := by
  rw [B.terminalDegree_onLanes A budget h]
  let V:=2^(u^10)
  have uV : u≤V:=Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_self_pow (by decide) u))
  have square : V^2≤V^4:=Nat.pow_le_pow_right (by omega) (by decide)
  change 7*(2*2^B.exponent 0+2)≤V^4
  apply le_trans _ square
  have factor:=Nat.mul_le_mul_right V (show 40≤V by omega)
  nlinarith


end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
