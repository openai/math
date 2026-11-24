import OAI.Computability.VPVNP.CompressorRecordsSelectedFinish
import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# Linking the selected shrinking placement and role scans

A completed row returns the next ordinal. Its four writes lie in the
placement or role array. The online dispatcher's tag, ordinal, directory
length and installed frame therefore stay ready throughout the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkHistoryTrace

open BurstRAM Schedule OrdinalRun PrimedStackRAM
open scoped Fin.CommRing

variable {w n : ℕ} {Q : Type*} {d : ℕ}

/-- Link a deterministic ordinal scan after checking the single-call
return and the four physical writes for every live ordinal. -/
private theorem ordinal_valid (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → Word w) (P : BurstRAM.Program w Q) (fuel : ℕ)
    (nativeEvents : Memory w → Word w → List (Event w))
    (one : ∀ m i, execute P fuel (P.start i) m [] = some ⟨nativeEvents m i,some (i+1)⟩)
    (stable : ∀ j < n, ∀ m, Preserved (C worker).params ports m (after m (nativeEvents m (j : Word w))))
    (fit : n < 2^w) (m : Memory w) (reports : List (Report w))
    (ready : Ready C worker ports pub (n : Word w) m)
    (run : runSegment P fuel (some 0) m (List.replicate n []) = some reports) :
    ValidTrace C worker ports pub (n : Word w) 0 m reports ∧
      Preserved (C worker).params ports m (after m (eventLog reports)) := by
  let cursor (i : ℕ) : Word w := i
  have active (j : ℕ) (hj : j<n) : cursor j < cursor n := by
    change j%(2^w) < n%(2^w)
    rwa [Nat.mod_eq_of_lt (hj.trans fit),Nat.mod_eq_of_lt fit]
  have advance (j : ℕ) (hj : j<n) (m : Memory w) (_ : True) (bits : List Bool) (rep : Report w)
      (h : execute P fuel (P.start (cursor j)) m bits = some rep) :
      rep.result = some (cursor (j+1)) ∧ True ∧ Preserved (C worker).params ports m (after m rep.events) := by
    have eq := (execute_prefix_unique (one m (cursor j)) (show execute P fuel (P.start (cursor j)) m ([] ++ bits) = some rep from h)).2
    subst rep
    exact ⟨by simp [cursor], trivial, stable j hj m⟩
  obtain ⟨trace,_,keep⟩ := OrdinalRun.validTrace C worker ports P fuel pub (cursor n) cursor n (fun _ _ => True)
    active le_rfl advance 0 _ m reports (by simp) trivial ready run
  exact ⟨trace,keep⟩

open private store_other from OAI.Computability.VPVNP.CompressorRecordsShrinkScan
open private store_outside from OAI.Computability.VPVNP.CompressorRecordsDemandScan

theorem placement_valid (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → Word w) (p : Fin 14 → Word w)
    (fit : n < 2^w) (m : Memory w) (reports : List (Report w)) (ready : Ready C worker ports pub (n : Word w) m)
    (apart : ∀ (j : ℕ), j < n → ∀ (t : Fin 4) x, ControlCell (C worker).params ports x → x ≠ ShrinkRAM.outAddr p t (j : Word w))
    (run : runSegment ((template ShrinkRAM.visit 0).instantiate w p).program 65 (some 0) m (List.replicate n []) = some reports) :
    ValidTrace C worker ports pub (n : Word w) 0 m reports ∧
      Preserved (C worker).params ports m (after m (eventLog reports)) := by
  apply ordinal_valid C worker ports pub _ 65 (ShrinkRAM.events p) (ShrinkRAM.visit_native p) _ fit m reports ready run
  intro j hj mem x hx
  rw [ShrinkRAM.visit_after]
  exact store_other p mem _ _ x fun t => apart j hj t x hx

theorem roles_valid (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → Word w) (p : Fin 11 → Word w)
    (fit : n < 2^w) (m : Memory w) (reports : List (Report w)) (ready : Ready C worker ports pub (n : Word w) m)
    (apart : ∀ (j : ℕ), j < n → ∀ (t : Fin 4) x, ControlCell (C worker).params ports x → x ≠ DemandRAM.fieldAddr p (j : Word w) t)
    (run : runSegment ((template DemandRAM.visit 0).instantiate w p).program 65 (some 0) m (List.replicate n []) = some reports) :
    ValidTrace C worker ports pub (n : Word w) 0 m reports ∧
      Preserved (C worker).params ports m (after m (eventLog reports)) := by
  apply ordinal_valid C worker ports pub _ 65 (DemandRAM.events p) (DemandRAM.visit_native p) _ fit m reports ready run
  intro j hj mem x hx
  rw [DemandRAM.visit_after]
  exact store_outside p mem _ x fun t => apart j hj t x hx

/-- A native clear before appending either child rows or local-map rows. -/
theorem clear_valid (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → Word w) (base : Word w) (fit : n < 2^w) (room : base.val+n ≤ 2^w)
    (m : Memory w) (rs : List (Report w)) (ready : Ready C worker ports pub (n : Word w) m)
    (apart : ∀ x, ControlCell (C worker).params ports x → x < base.val ∨ base.val+n ≤ x)
    (run : runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ => base)).program 8
      (some 0) m (List.replicate n []) = some rs) :
    ValidTrace C worker ports pub (n : Word w) 0 m rs ∧
      Preserved (C worker).params ports m (after m (eventLog rs)) := by
  apply ordinal_valid C worker ports pub _ 8 (fun _ i => (SliceRAM.clearReport base i).events)
    (fun mem i => SliceRAM.clearVisit_native base i mem) _ fit m rs ready run
  intro j hj mem x hx
  have he : (base+(j : Word w)).val = base.val+j := by
    rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (hj.trans fit),Nat.mod_eq_of_lt (by omega)]
  have neq : x ≠ (base+(j : Word w)).val := by have := apart x hx; omega
  change writeMemory mem _ 0 x = mem x
  exact ite_eq_right neq

open private collectUpdate_frame from OAI.Computability.VPVNP.CompressorSlotFrames

/-- The guarded preimage worker checks the owner and the row counter before
appending. Every successful call preserves all the indicated controller cells. -/
theorem append_valid (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → Word w) (p : Fin 6 → Word w) (areas : RowRegions p)
    (m : Memory w) (rs : List (Report w)) (ready : Ready C worker ports pub (p 0) m)
    (apart : ∀ x, ControlCell (C worker).params ports x → OutsidePreimageWrites p x)
    (run : runSegment ((template collectPreimage 3).instantiate w p).program 23 (some 0) m
      (List.replicate (p 0).val []) = some rs) :
    ValidTrace C worker ports pub (p 0) 0 m rs ∧
      Preserved (C worker).params ports m (after m (eventLog rs)) := by
  let M := (template collectPreimage 3).instantiate w p
  let cursor (j : ℕ) : Word w := j
  have live (j : ℕ) (hj : j < (p 0).val) : cursor j < p 0 := by
    change j%(2^w) < (p 0).val
    rwa [Nat.mod_eq_of_lt (hj.trans (p 0).isLt)]
  let I := fun j mem => ∃ tail, runSegment M.program 23 (some (cursor j)) mem
    (List.replicate ((p 0).val-j) []) = some tail
  have advance (j : ℕ) (hj : j < (p 0).val) (mem : Memory w) (inv : I j mem) (bits : List Bool) (rep : Report w)
      (h : execute M.program 23 (M.program.start (cursor j)) mem bits = some rep) :
      rep.result = some (cursor (j+1)) ∧ I (j+1) (after mem rep.events) ∧ Preserved (C worker).params ports mem (after mem rep.events) := by
    let i := cursor j
    obtain ⟨tail,ht⟩ := inv
    rw [show (p 0).val-j=(p 0).val-(j+1)+1 by omega,List.replicate_succ,runSegment] at ht
    cases head : execute M.program 23 (M.program.start i) mem [] with
    | none => rw [head] at ht; contradiction
    | some r =>
      have eqn : r = rep := (execute_prefix_unique (suffix := bits) head h).2
      subst r
      rw [head] at ht
      obtain ⟨rest,next,_⟩ := Option.map_eq_some_iff.mp ht
      by_cases ok : i < p 0 ∧ ownerAt p mem i < p 2 ∧ mem (countAt p (ownerAt p mem i)).val < p 4
      · have one := collectPreimage_native p mem i ok.1 ok.2.1 ok.2.2
        have eq := Option.some.inj (head.symm.trans one)
        subst rep
        have succ : i+1=cursor (j+1) := by simp [i,cursor]
        refine ⟨congrArg some succ,⟨rest,?_⟩,?_⟩
        · exact succ ▸ next
        · intro x hx
          change after mem (collectEvents p mem i) x = mem x
          rw [after_collectEvents]
          exact collectUpdate_frame areas mem i ok.2.1 ok.2.2 x (apart x hx)
      · change execute M.program (1+collectPreimage.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ mem [] = _ at head
        rw [execute_template,run_eq_trace,collectPreimage_invalid p i _ mem ok] at head
        contradiction
  have last : p 0 ≤ cursor (p 0).val := by change _ ≤ (p 0).val % (2^w); rw [Nat.mod_eq_of_lt (p 0).isLt]
  have start : I 0 m := ⟨rs,by simpa only [Nat.sub_zero,Nat.cast_zero,cursor] using run⟩
  obtain ⟨trace,_,keep⟩ := OrdinalRun.validTrace C worker ports M.program 23 pub (p 0) cursor (p 0).val
    I live last advance 0 _ m rs (by simp) start ready run
  exact ⟨trace,keep⟩

open Compression SelectedArena

/-- Exact numerical ranges of the two output tables on the selected
branch, including the permutation from old ports to absolute arc IDs. -/
theorem selected_ranges {a g : ℕ} (X : State a (packingLaneBits a g)) (term stride : Word w)
    (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (m : Memory w) {b : Bool}
    (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g b) (fit : Fits X term stride) :
    (∀ (j : ℕ), j < positions X → ∀ t : Fin 4,
      let a := ShrinkRAM.outAddr (selectedWords X term stride p₀ m) t (j : Word w)
      placementBase X term stride ≤ a ∧ a < roleBase X term stride) ∧
    (∀ (j : ℕ), j < DemandRAM.oldCount X → ∀ t : Fin 4,
      let a := DemandRAM.fieldAddr (demandWords X term stride p₀ T) (j : Word w) t
      roleBase X term stride ≤ a ∧ a < endAddr X term stride) := by
  have room : roleBase X term stride + 4*DemandRAM.absoluteCount X < 2^w := fit
  have hn : placementBase X term stride + 4*positions X = roleBase X term stride := rfl
  constructor
  · intro j hj t
    let bit := m (origin X term stride+2)
    have hcols := output_column X term stride p₀ bit fit t
    have ht := Nat.mul_le_mul_right (positions X) t.isLt
    rw [Nat.succ_mul] at ht
    have sj : ((j : Word w)).val = j := Nat.mod_eq_of_lt (by omega)
    dsimp only [selectedWords,ShrinkRAM.outAddr,Fin.val_add]
    rw [hcols,sj,Nat.mod_eq_of_lt (by omega)]
    omega
  · intro j hj t
    let E := BundleKeys.oldArcOrder (a := a) (g := g) X.baseIndex
    let edge := E.symm ⟨j,hj⟩
    have base := role_base_val X term stride p₀ T fit
    have sizes := DemandRAM.count_eq X
    have sj : ((j : Word w)).val = (E edge).val := by
      rw [show E edge = ⟨j,hj⟩ from Equiv.apply_symm_apply E _]
      exact Nat.mod_eq_of_lt (by omega)
    rw [DemandRAM.fieldAddr_exact X (demand_params X term stride p₀ T hp) (by rw [base]; exact room.le) edge sj t,base]
    have he : (DemandRAM.absoluteIndex X edge).val < DemandRAM.absoluteCount X := (DemandRAM.absoluteIndex X edge).isLt
    have ht := t.isLt
    change _ ∧ _ < roleBase X term stride + 4*DemandRAM.absoluteCount X
    omega

/-- The two report groups of the actual selected score/placement/role
execution pass the guarded scheduler at their chronological input memories. -/
theorem selected_valid {a g : ℕ} (X : State a (packingLaneBits a g)) (term stride selectors : Word w)
    (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w) (m : Memory w) (p : SelectedStage.Passes w)
    (exec : SelectedStage.Execution X term stride selectors p₀ T m p) {b : Bool}
    (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g b) (fit : Fits X term stride)
    (C : Catalog d) (positionsID rolesID : Fin d) (ports : Ports w)
    (pp : Fin (C positionsID).params → Word w) (rp : Fin (C rolesID).params → Word w)
    (pr : Ready C positionsID ports pp (positions X : Word w) (p.afterScores m))
    (rr : Ready C rolesID ports rp (DemandRAM.oldCount X : Word w) (p.afterPositions m))
    (psep : ∀ x, ControlCell (C positionsID).params ports x → x < placementBase X term stride ∨ roleBase X term stride ≤ x)
    (rsep : ∀ x, ControlCell (C rolesID).params ports x → x < roleBase X term stride ∨ endAddr X term stride ≤ x) :
    ValidTrace C positionsID ports pp (positions X : Word w) 0 (p.afterScores m) p.positions ∧
    ValidTrace C rolesID ports rp (DemandRAM.oldCount X : Word w) 0 (p.afterPositions m) p.roles := by
  have room : placementBase X term stride+4*positions X+4*DemandRAM.absoluteCount X < 2^w := fit
  have cnt := DemandRAM.count_eq X
  obtain ⟨rng,rng'⟩ := selected_ranges X term stride p₀ T (p.afterScores m) hp fit
  refine ⟨(placement_valid C positionsID ports pp _ (by omega) _ _ pr ?_ exec.positions).1,
    (roles_valid C rolesID ports rp _ (by omega) _ _ rr ?_ exec.roles).1⟩
  · intro j hj t x hx
    have ha := rng j hj t
    have ho := psep x hx
    omega
  · intro j hj t x hx
    have ha := rng' j hj t
    have ho := rsep x hx
    omega

/-- The collector and counter clear at the two addresses following the
selected placement/role arena pass the online guards in the same memory. -/
theorem selected_finish_valid {a g : ℕ} (X : State a (packingLaneBits a g)) (term stride : Word w)
    (p₀ : Fin 14 → Word w) (layoutWord : Word w) (side : Bool) (m : Memory w) (pass : SelectedFinish.Passes w)
    (room : SelectedFinish.stop X term stride ≤ 2^w)
    (exec : SelectedFinish.Collected X term stride (shrinkWords X term stride p₀ layoutWord) side m pass)
    (C : Catalog d) (clearID appendID : Fin d) (ports : Ports w) (cp : Fin (C clearID).params → Word w)
    (ap : Fin (C appendID).params → Word w)
    (cr : Ready C clearID ports cp (ShrinkPreimages.newCount X : Word w) m)
    (ar : Ready C appendID ports ap (ShrinkPreimages.oldCount X : Word w) (pass.middle m))
    (cs : ∀ x, ControlCell (C clearID).params ports x →
      x < SelectedFinish.countStart X term stride ∨ SelectedFinish.rowStart X term stride ≤ x)
    (as : ∀ x, ControlCell (C appendID).params ports x →
      x < SelectedFinish.countStart X term stride ∨ SelectedFinish.stop X term stride ≤ x) :
    ValidTrace C clearID ports cp (ShrinkPreimages.newCount X : Word w) 0 m pass.clear ∧
    ValidTrace C appendID ports ap (ShrinkPreimages.oldCount X : Word w) 0 (pass.middle m) pass.collect := by
  let p := SelectedFinish.params X term stride (shrinkWords X term stride p₀ layoutWord)
  have areas := SelectedFinish.areas X term stride p₀ layoutWord room
  obtain ⟨ho,hn,hcap⟩ := areas.dimensions
  change (p 0).val=ShrinkPreimages.oldCount X at ho
  change (p 2).val=ShrinkPreimages.newCount X at hn
  change (p 4).val=ShrinkPreimages.capacity a at hcap
  have endEq := ShrinkPreimages.oldCount_eq X
  have pos : 0 < ShrinkPreimages.oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
  have capRoom : SelectedFinish.countStart X term stride+ShrinkPreimages.newCount X+ShrinkPreimages.oldCount X ≤ 2^w := room
  have cval : (SelectedFinish.counts X term stride).val = SelectedFinish.countStart X term stride := Nat.mod_eq_of_lt (by omega)
  have rval : (SelectedFinish.rows X term stride).val = SelectedFinish.rowStart X term stride :=
    Nat.mod_eq_of_lt (by unfold SelectedFinish.rowStart; omega)
  have hw : p 0 = (ShrinkPreimages.oldCount X : Word w) := by
    apply Fin.ext
    rw [Fin.val_natCast,Nat.mod_eq_of_lt areas.sizes.1]
    exact ho
  refine ⟨(clear_valid C clearID ports cp (SelectedFinish.counts X term stride) areas.sizes.2.1
    (by rw [cval]; omega) m pass.clear cr (by simpa only [cval,SelectedFinish.rowStart] using cs) exec.clear).1,?_⟩
  rw [← hw]
  apply (append_valid C appendID ports ap p areas.regions (pass.middle m) pass.collect (hw ▸ ar) _ (ho.symm ▸ exec.collect)).1
  intro x hx
  change (x < (SelectedFinish.counts X term stride).val ∨ (SelectedFinish.counts X term stride).val+(p 2).val ≤ x) ∧
    (x < (SelectedFinish.rows X term stride).val ∨ (SelectedFinish.rows X term stride).val+(p 2).val*(p 4).val ≤ x)
  rw [cval,rval,hn,hcap,←endEq]
  have h := as x hx
  dsimp only [SelectedFinish.stop,SelectedFinish.rowStart] at h ⊢
  omega

end CompressorRecords.ShrinkHistoryTrace

end VPVNP
end Computability
end OAI
