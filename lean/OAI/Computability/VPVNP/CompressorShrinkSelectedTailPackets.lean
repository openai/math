import OAI.Computability.VPVNP.CompressorShrinkSelectedScans
import OAI.Computability.VPVNP.CompressorShrinkSelectedPlan
import OAI.Computability.VPVNP.CompressorRecordsSelectedFinish
import OAI.Computability.VPVNP.CompressorHeaderOperands

/-! # The four chronological placement, role and child-directory packets -/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedTailPackets

open BurstRAM Compression BlockPlanner PhaseRecipe SourceTransport DescriptorSpace SelectedArena
open ShrinkHistoryTrace
open scoped Fin.CommRing Classical

variable {a g w : ℕ} (I : SelectedPlan.Inputs) (X : State a (packingLaneBits a g))
  (term : Word w) (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w)
local notation "stride" => (I.termStride : Word w)
local notation "selectors" => (I.selectorBits : Word w)

/-- The four post-comparison visits write placements, write role rows, clear child counters,
then collect children by their new site. -/
def tail (a : ℕ) := [SelectedPlan.placement I,SelectedPlan.roles I,SelectedPlan.clearChildren I,SelectedPlan.children I a]

theorem split : SelectedPlan.visits I a =
    ([SelectedPlan.clear I]++List.ofFn (SelectedPlan.axis I)++[SelectedPlan.compare I]) ++ tail I a := by
  simp only [SelectedPlan.visits,tail,List.append_assoc,List.cons_append,List.nil_append]

/-- Requires the size, term, old outgoing-incidence, and preliminary operand expressions used
by the four tail visits to read only addresses in `D`. -/
structure Footprint (D : ℕ → Prop) (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) : Prop where
  sites : I.oldSites.ReadsFrom D pub st m
  newSites : I.newSites.ReadsFrom D pub st m
  slots : I.oldSlots.ReadsFrom D pub st m
  motifs : I.motifs.ReadsFrom D pub st m
  term : I.termBase.ReadsFrom D pub st m
  oldOut : I.oldActualOut.ReadsFrom D pub st m
  prior : ∀ j, (I.preliminary j).ReadsFrom D pub st m

variable (D : ℕ → Prop) (pub : Fin 5 → Word w) (st : Word w)
open SelectedPlan in
private theorem supported (m : Memory w) (h : Footprint I D pub st m)
    (layoutAddr : D ((layoutCell I).eval pub st m).val) :
    ∀ v ∈ tail I a, HeaderOperands.Supported D pub st m v := by
  let safe := fun (e : Expr) => e.ReadsFrom D pub st m
  have sc : safe (scoreBase I) := ⟨h.term,h.motifs,trivial⟩
  have pl : safe (placementBase I) := ⟨sc,trivial⟩
  have co (c : Fin 4) : safe (placementColumn I c) := ⟨pl,trivial,h.sites⟩
  have ro : safe (roleBase I) := ⟨pl,trivial,h.sites⟩
  have en : safe (roleEnd I) := ⟨ro,trivial,h.slots⟩
  have rows : safe (childRows I) := ⟨en,h.newSites⟩
  have la : safe (layout I) := ⟨⟨sc,trivial⟩,layoutAddr⟩
  intro v hv
  simp only [tail,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl
  · refine ⟨trivial,h.sites,?_⟩
    intro j; change (placementBank I j).ReadsFrom D pub st m
    fin_cases j <;> first | exact h.prior _ | exact la | exact co _
  · refine ⟨trivial,h.slots,?_⟩
    intro j; change (rolesBank I j).ReadsFrom D pub st m
    fin_cases j <;> first | exact h.prior _ | exact h.oldOut | exact co _ | exact ro | trivial
  · exact ⟨trivial,h.newSites,fun _ => en⟩
  · refine ⟨trivial,h.sites,?_⟩
    intro j; change (childBank I a j).ReadsFrom D pub st m
    fin_cases j <;> first | exact h.sites | exact h.newSites | exact co _ | exact rows | exact en | trivial

variable (L : DescriptorSpace.Layout)
local notation "H" => levelStart L 0

/-- A source run of the visit with instruction fuel at most 65, whose header operand
expressions read only from `D` at entry. -/
def Source (v : BlockPlanner.Visit) (m : Memory w) (rs : List (Report w)) :=
  ∃ fuel bits, fuel≤65 ∧ HeaderPacket.Run L pub st v m rs fuel bits ∧ HeaderOperands.Supported D pub st m v

private theorem packet (v : BlockPlanner.Visit) (n f : ℕ) (bank : Fin v.worker.params → Word w) (m : Memory w) (rs : List (Report w))
    (pos : 0<f) (hf : f≤65) (size : n<2^w) (start : v.initial.eval pub st m=0) (stop : v.stop.eval pub st m=(n : Word w))
    (args : (fun j => (v.params j).eval pub st m)=bank)
    (run : runSegment (v.worker.table.instantiate w bank).program f (some 0) m (List.replicate n [])=some rs)
    (shape : StageFrame.Scanned 0 n rs) (rd : Reads (H≤·) (eventLog rs)) (wr : Writes (H≤·) (eventLog rs))
    (supp : HeaderOperands.Supported D pub st m v) : Source D pub st L v m rs := by
  refine ⟨f,List.replicate n [],hf,⟨pos,?_,?_,rd,wr⟩,supp⟩
  · dsimp only; rw [args,start]; exact run
  · rw [start,stop]; exact shape.toProgress size

private theorem roleEnd_value (m : Memory w) (rd : SelectedPlan.Reads I X p₀ T term pub st m) :
    (SelectedPlan.roleEnd I).eval pub st m = SelectedFinish.counts X term stride := by
  change (SelectedPlan.roleBase I).eval pub st m + 4*I.oldSlots.eval pub st m = _
  rw [SelectedPlan.roles_head I X p₀ T term pub st m rd,rd.slots,DemandRAM.count_eq X]
  change (SelectedArena.roleBase X term stride : Word w)+4*(DemandRAM.absoluteCount X : Word w) =
    ((SelectedArena.roleBase X term stride+4*DemandRAM.absoluteCount X : ℕ) : Word w)
  push_cast; rfl

private theorem rows_value (m : Memory w) (rd : SelectedPlan.Reads I X p₀ T term pub st m) :
    (SelectedPlan.childRows I).eval pub st m = SelectedFinish.rows X term stride := by
  change (SelectedPlan.roleEnd I).eval pub st m + I.newSites.eval pub st m = _
  rw [roleEnd_value I X term p₀ T pub st m rd,rd.nextSites]
  exact (Nat.cast_add ..).symm

/-- The entry memories for the four tail visits, taken after scoring, after placement, after
writing roles, and after clearing child counters. -/
def inputs (m : Memory w) (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w) :=
  [p.afterScores m,p.afterPositions m,p.final m,q.middle (p.final m)]

/-- The source reports from placement, role writes, child-counter clearing, and child
collection concatenated in execution order. -/
def reports (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w) :=
  p.positions ++ (p.roles ++ (q.clear ++ q.collect))

open private room_vals from OAI.Computability.VPVNP.CompressorRecordsSelectedPreimages

set_option maxHeartbeats 1200000 in
/-- Each of the four visits uses the memory left by its predecessor,
including the selected layout bit and the newly materialized owner column. -/
theorem walk {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
    (s : SelectedScore.Selection B X) (m : Memory w) (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w)
    (exec : SelectedStage.Execution X term stride selectors p₀ T m p)
    (stored : SelectedStage.Stored B X term stride p₀ s m p)
    (built : SelectedFinish.Built B X term stride selectors p₀ s m p q)
    {side : Bool} (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g side)
    (old : OldInputs X term stride p₀ T) (room : SelectedFinish.stop X term stride ≤ 2^w)
    (floor : H≤ inputFloor p₀) (oldOut : H≤T.actualOut.val) (termFloor : H≤term.val)
    (data : ∀ x, H≤x → D x)
    (raw : ∀ r ∈ inputs m p q, SelectedPlan.Reads I X p₀ T term pub st r ∧ Footprint I D pub st r) :
    SourceWalk (Source D pub st L) (tail I a) (p.afterScores m) (reports p q) := by
  obtain ⟨fit,cval,rval⟩ := room_vals X term stride room
  let sh : Fin 14 → Word w := selectedWords X term stride p₀ (p.afterScores m)
  let bank := SelectedFinish.params X term stride sh
  let area := SelectedFinish.areas X term stride p₀ ((p.afterScores m) (origin X term stride+2)) room
  have prec : ShrinkPreimages.Areas X sh (SelectedFinish.counts X term stride) (SelectedFinish.rows X term stride) := area
  have sizes := prec.dimensions
  have fN : ShrinkPreimages.oldCount X<2^w := sizes.1 ▸ (bank 0).isLt
  have fV : ShrinkPreimages.newCount X<2^w := sizes.2.1 ▸ (bank 2).isLt
  have endFit : placementBase X term stride+4*positions X+4*DemandRAM.absoluteCount X < 2^w := fit
  have gN : DemandRAM.oldCount X < 2^w := by rw [DemandRAM.count_eq X]; omega
  have cLo : H ≤ SelectedFinish.countStart X term stride := by
    change H≤term.val+motifs X*(stride).val+3+4*positions X+4*DemandRAM.absoluteCount X
    omega
  have pLo : H ≤ placementBase X term stride := by change H≤term.val+motifs X*(stride).val+3; omega
  have rLo : H ≤ roleBase X term stride := pLo.trans (Nat.le_add_right ..)
  have here (r : Memory w) (hr : r ∈ inputs m p q) (v : BlockPlanner.Visit) (hv : v ∈ tail I a) :
      HeaderOperands.Supported D pub st r v := by
    obtain ⟨read,feet⟩ := raw r hr
    apply supported I D pub st r feet _ v hv
    apply data
    change H ≤ ((SelectedPlan.scoreBase I).eval pub st r+2).val
    rw [SelectedPlan.score_head I X p₀ T term pub st r read,← (Nat.cast_ofNat (R := Word w) (n := 2)),← Nat.cast_add,Fin.val_natCast]
    have hf : origin X term stride+2<2^w := by change origin X term stride+3+_+_<2^w at endFit; omega
    rw [Nat.mod_eq_of_lt hf]; change H≤term.val+motifs X*(stride).val+2; omega
  obtain ⟨pr,pw,rr,rw'⟩ := selected_access B X term stride selectors p₀ T s m p exec stored old hp fit
  have pl := (raw (p.afterScores m) (by simp [inputs])).1
  have ro := (raw (p.afterPositions m) (by simp [inputs])).1
  have cl := (raw (p.final m) (by simp [inputs])).1
  have ap := (raw (q.middle (p.final m)) (by simp [inputs])).1
  have posShape : StageFrame.Scanned 0 (positions X) p.positions :=
    emptyScanned _ 65 (fun mem i r h => congrArg Report.result (Option.some.inj (h.symm.trans (ShrinkRAM.visit_native sh mem i))))
      (Nat.zero_add _) _ _ exec.positions
  have roleShape : StageFrame.Scanned 0 (DemandRAM.oldCount X) p.roles :=
    emptyScanned _ 65 (fun mem i r h => congrArg Report.result (Option.some.inj (h.symm.trans (DemandRAM.visit_native _ mem i))))
      (Nat.zero_add _) _ _ exec.roles
  have hpos : Source D pub st L (SelectedPlan.placement I) (p.afterScores m) p.positions :=
    packet D pub st L (SelectedPlan.placement I) (positions X) 65 sh _ _ (by decide) le_rfl fN rfl pl.sites
      (SelectedPlan.placement_bank I X p₀ T term pub st _ pl fit) exec.positions posShape
      (fun a v h => floor.trans (pr a v h).1) (fun a v h => pLo.trans (pw a v h).1)
      (here _ (by simp [inputs]) _ (by simp [tail]))
  have hrole : Source D pub st L (SelectedPlan.roles I) (p.afterPositions m) p.roles :=
    packet D pub st L (SelectedPlan.roles I) _ 65 (demandWords X term stride p₀ T) _ _ (by decide) le_rfl gN rfl ro.slots
      (SelectedPlan.roles_bank I X p₀ T term pub st _ ro) exec.roles roleShape
      (fun a v h => (rr a v h).elim (fun b => oldOut.trans b.1) (fun b => pLo.trans b.1))
      (fun a v h => rLo.trans (rw' a v h).1) (here _ (by simp [inputs]) _ (by simp [tail]))
  obtain ⟨clearShape,cr,cw⟩ := clear_scanned _ _ (prec.countEnd.trans (SelectedFinish.rows X term stride).isLt.le)
    _ _ built.raw.clear
  have hclear : Source D pub st L (SelectedPlan.clearChildren I) (p.final m) q.clear :=
    packet D pub st L (SelectedPlan.clearChildren I) _ 8 (fun _ => SelectedFinish.counts X term stride) _ _ (by decide) (by decide) fV rfl cl.nextSites
      (funext fun _ => roleEnd_value I X term p₀ T pub st _ cl) built.raw.clear clearShape
      (fun a v h => (cr a v h).elim) (fun a v h => (cval.symm ▸ cLo).trans (cw a v h).1)
      (here _ (by simp [inputs]) _ (by simp [tail]))
  have arg := SelectedPlan.child_bank I X p₀ T term pub st _ ap sh rfl
  rw [roleEnd_value I X term p₀ T pub st _ ap,rows_value I X term p₀ T pub st _ ap] at arg
  have own : H ≤ (bank 1).val := by
    change H ≤ (placementWord X term stride 0).val
    rw [column_value X term stride fit,Fin.val_zero,Nat.zero_mul,Nat.add_zero]; exact pLo
  have cnt : H ≤ (bank 3).val := cval.symm ▸ cLo
  have rows : H ≤ (bank 5).val := rval.symm ▸ (cLo.trans (Nat.le_add_right ..))
  obtain ⟨ar,aw⟩ := SlotFillFootprint.append_run prec.regions built.raw.collect
  have happ : Source D pub st L (SelectedPlan.children I a) (q.middle (p.final m)) q.collect :=
    packet D pub st L (SelectedPlan.children I a) _ 23 bank _ _ (by decide) (by decide) fN rfl ap.sites arg built.raw.collect
      (append_scanned _ _ _ _ built.raw.collect)
      (fun a v h => (ar a v h).elim (fun b => own.trans b.1) (fun b => cnt.trans b.1))
      (fun a v h => (aw a v h).elim (fun b => cnt.trans b.1) (fun b => rows.trans b.1))
      (here _ (by simp [inputs]) _ (by simp [tail]))
  exact .next hpos (.next hrole (.next hclear (SourceWalk.singleton happ)))

end CompressorRecords.SelectedTailPackets

end

end VPVNP
end Computability
end OAI
