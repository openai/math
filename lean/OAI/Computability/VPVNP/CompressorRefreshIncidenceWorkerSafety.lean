import OAI.Computability.VPVNP.CompressorRecordRefreshPrepareAllocation
import OAI.Computability.VPVNP.CompressorRefreshStageFrame
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Per-call memory regions of refreshed incidence workers

The actual-slot worker reads the scratch directory, ROM or selected supplies
below the output incidence region. Its three writes are in the output
columns. The lane-zero base worker then uses one actual-output read and
three base-column writes inside that same region.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.IncidenceWorkerSafety

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh
open SpectralGeometry MotifConversion NewSlots Allocation SourceTransport

variable {w : ℕ}

/-- An inclusive lower bound and exclusive upper bound in the packed allocation. -/
def interval (lo hi x : ℕ) := lo ≤ x ∧ x < hi

private theorem packed_lt {q Q i d : ℕ} (hq : q<Q) (hi : i<d) : q*d+i < Q*d :=
  calc q*d+i < q*d+d := Nat.add_lt_add_left hi _
       _ = (q+1)*d := (Nat.succ_mul ..).symm
       _ ≤ Q*d := Nat.mul_le_mul_right _ hq

private theorem address_in {base n : ℕ} (fit : base+n ≤ 2^w) (i : W w) (hi : i.val<n) :
    interval base (base+n) (word base+i).val := by
  rw [Fin.val_add,show (word (bits := w) base).val = base from Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left hi _⟩

private theorem encoded_lt {i n : ℕ} (h : i<n) : (word (bits := w) i).val < n := (Nat.mod_le ..).trans_lt h

private theorem word_key {a b : ℕ} (i j : W w) (hi : i.val < a) (hj : j.val < b) :
    (i * word b + j).val < a*b := by
  rw [Fin.val_add,Fin.val_mul,Fin.val_ofNat,Nat.mul_mod_mod,Nat.mod_add_mod]
  exact (Nat.mod_le ..).trans_lt (packed_lt hi hj)

private def readPart (kind : Kind) (p : Public w) (m : Memory w) (i : W w) : List (Event w) :=
  let ticks := fun n => List.replicate n (Event.tick : Event w)
  let read := fun a : W w => Event.read a (m a.val)
  match kind with
  | .external => ticks 3 ++ [read (p 5+i)] ++ ticks 2 ++ [read (p 6+i)] ++ ticks 3
  | .expander =>
    let j := BinaryOp.mod.eval (BinaryOp.div.eval i (p 3)) (p 0)
    let e := j*p 1+p 4
    ticks 14 ++ [read (p 7+e)] ++ ticks 2 ++ [read (p 8+e)] ++ ticks 7 ++
      [read (p 9+(i*p 1+p 4))] ++ ticks 8
  | .padding => ticks 24

private theorem split_events (kind : Kind) (p : Public w) (m : Memory w) (i : W w) :
    let s := row kind p m i
    let ticks := fun n => List.replicate n (Event.tick : Event w)
    NewSlots.events kind p m i = readPart kind p m i ++ ticks 2 ++ [.write (p 10+s.src) s.dst] ++
      ticks 2 ++ [.write (p 11+s.dst) s.src] ++ ticks 2 ++ [.write (p 12+s.src) s.width] ++ ticks 2 := by
  cases kind <;> rfl

private theorem port_event_reads (kind : Kind) (p : Public w) (m : Memory w) (i : W w)
    (region : ℕ → Prop) (hr : ∀ a ∈ inputs kind p i, region a.val) :
    Reads region (NewSlots.events kind p m i) := by
  intro addr v h
  rw [split_events] at h
  cases kind with
  | external =>
    simp [readPart] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> apply hr <;> simp [inputs]
  | expander =>
    simp [readPart] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> apply hr <;> simp [inputs]
  | padding => simp [readPart] at h

private theorem port_event_writes (kind : Kind) (p : Public w) (m : Memory w) (i : W w)
    (region : ℕ → Prop) (hw : ∀ c, region ((row kind p m i).address p c).val) :
    Writes region (NewSlots.events kind p m i) := by
  intro addr v h
  rw [split_events] at h
  cases kind <;> simp [readPart] at h
  all_goals rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
  all_goals first | exact hw .outgoing | exact hw .incoming | exact hw .width

section Slots

variable {a g a₀ dH t stride start : ℕ} {K : Type*} [_root_.Field K] {c₁ c₂ : ℝ}
  (X : State a (a+g)) (E : RegularArcGraph (Fin (2^a)) dH)
  (hdH : 0 < dH) (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock K (expanderSupply E hdH conn) (2^a₀) c₁ c₂)
  (hd : dH+1 ≤ 2^a₀) (choice : DyadicRefreshChoice X E hdH conn F)

local notation "P" => plan X a₀ dH t stride start
local notation "N" => Fintype.card X.Base * 2^a * 2^g
local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "int" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv a) (splitWidths X) E hdH conn F choice
local notation "I" => Plan.inputs P w
local notation "T" => Plan.output P w
local notation "bank" => AllSlots.words (2^a) (2^g) I T

private theorem input_range (c : RefreshSlot dH (2^a₀)) (fit : AllSlots.Fits (a₀ := a₀) X w)
    (room : (P).stop ≤ 2^w) (i : Fin N) (addr : W w)
    (used : addr ∈ inputs (kindOf c) (bank c) (word i.val)) : interval start (P).next addr.val := by
  have hs : start ≤ (P).demand := Nat.le_add_right ..
  have hdt : (P).demand ≤ (P).supply := by dsimp only [Plan.supply,Plan.term]; omega
  have hst : (P).supply + N*dH = (P).targetPort := rfl
  have htr : (P).targetPort + 2^a*dH = (P).reverseSlot := rfl
  have hrn : (P).reverseSlot + 2^a*dH = (P).next := rfl
  have hn : (P).next ≤ 2^w := by dsimp only [Plan.stop] at room; omega
  let b := word (bits := w) i.val
  have hb := encoded_lt (w := w) i.isLt
  cases c with
  | inl c =>
    change addr ∈ [(P).scratch w 2+b,(P).scratch w 4+b] at used
    have hj : b.val < (P).segments := hb.trans_le (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
    rcases List.mem_cons.mp used with rfl | h
    · have hr := Plan.scratch_interval P (by omega) 2 (by decide) b hj
      exact ⟨hr.1,hr.2.trans_le (by omega)⟩
    · obtain rfl := List.mem_singleton.mp h
      have hr := Plan.scratch_interval P (by omega) 4 (by decide) b hj
      exact ⟨hr.1,hr.2.trans_le (by omega)⟩
  | inr c =>
    cases c with
    | inr _ => exact (List.not_mem_nil used).elim
    | inl k =>
      let p := bank (.inr (.inl k) : RefreshSlot dH (2^a₀))
      let v := BinaryOp.mod.eval (BinaryOp.div.eval b (p 3)) (p 0)
      have hv : v.val < 2^a := by
        change (_ % (word (bits := w) (2^a)).val) % 2^w < _
        rw [show (word (bits := w) (2^a)).val = 2^a from Nat.mod_eq_of_lt fit.ports]
        exact (Nat.mod_le ..).trans_lt (Nat.mod_lt _ (Nat.two_pow_pos a))
      let e := v*p 1+p 4
      let z := b*p 1+p 4
      have he : e.val < 2^a*dH := word_key _ _ hv (encoded_lt k.isLt)
      have hz : z.val < N*dH := word_key _ _ hb (encoded_lt k.isLt)
      change addr ∈ [word (P).targetPort+e,word (P).reverseSlot+e,word (P).supply+z] at used
      rcases List.mem_cons.mp used with rfl | used
      · have ⟨lo,hi⟩ := address_in (base := (P).targetPort) (by omega) e he
        constructor <;> omega
      rcases List.mem_cons.mp used with rfl | used
      · have ⟨lo,hi⟩ := address_in (base := (P).reverseSlot) (by omega) e he
        constructor <;> omega
      obtain rfl := List.mem_singleton.mp used
      have ⟨lo,hi⟩ := address_in (base := (P).supply) (by omega) z hz
      constructor <;> omega

include hd in
private theorem output_bounds (c : RefreshSlot dH (2^a₀)) (fit : AllSlots.Fits (a₀ := a₀) X w)
    (ref : Memory w) (initial : AllSlots.SourceTables X E hdH conn F choice I ref) (i : Fin N) :
    let r := row (kindOf c) (bank c) ref (word i.val)
    r.src.val < (P).capacity ∧ r.dst.val < (P).capacity := by
  let s := (O).symm i
  have hi : i = O s := ((O).apply_symm_apply i).symm
  let p := bank c
  have dims : Dimensions p (Fintype.card X.Base) (2^a) (2^g) dH (2^a₀) :=
    ⟨Nat.mod_eq_of_lt fit.ports, Nat.mod_eq_of_lt (by have := fit.degree; omega),
      Nat.mod_eq_of_lt fit.degree,Nat.mod_eq_of_lt fit.lanes,fit.ids⟩
  have h : NewSlots.Represents X.baseIndex (bitWordFinEquiv g) (row (kindOf c) p ref (word i.val))
      (slotRecord (splitSlots X) (bitWordFinEquiv a) (splitWidths X) E.toSlotGraph hd int s c) := by
    rw [hi]
    rcases c with k | k | k
    · cases Subsingleton.elim k 0
      exact external_record X.baseIndex (bitWordFinEquiv g) hd dims (splitSlots X) (bitWordFinEquiv a)
        (splitWidths X) E.toSlotGraph int s (initial.target s) (initial.total s)
    · exact expander_record X.baseIndex (bitWordFinEquiv g) hd dims (splitSlots X) (bitWordFinEquiv a)
        (splitWidths X) E.toSlotGraph int s k (Nat.mod_eq_of_lt (by change k.val < 2^w; have := fit.degree; have := k.isLt; omega))
        (initial.targetPort (s.2,k)) (initial.reverseSlot (s.2,k)) (initial.supply s k)
    · exact padding_record X.baseIndex (bitWordFinEquiv g) hd dims (splitSlots X) (bitWordFinEquiv a)
        (splitWidths X) E.toSlotGraph int s k (Nat.mod_eq_of_lt (by change k.val < 2^w; have := fit.degree; have := k.isLt; omega))
  exact ⟨h.1 ▸ (arcs X.baseIndex (bitWordFinEquiv g) _).isLt,h.2.1 ▸ (arcs X.baseIndex (bitWordFinEquiv g) _).isLt⟩

/-- Throughout one slot scan, the complete read interval still agrees with
the reference memory at the beginning of that scan. -/
def SlotInvariant (alloc : Allocation.Plan) (ref m : Memory w) : Prop := Agree (interval alloc.start alloc.next) ref m

include hd in
theorem slot_step (c : RefreshSlot dH (2^a₀)) (fit : AllSlots.Fits (a₀ := a₀) X w)
    (room : (P).stop ≤ 2^w) (ref : Memory w) (initial : AllSlots.SourceTables X E hdH conn F choice I ref)
    (j : ℕ) (hj : j<N) (m : Memory w) (inv : SlotInvariant P ref m) :
    let es := NewSlots.events (kindOf c) (bank c) m (word j)
    SlotInvariant P ref (after m es) ∧ Reads (interval start (P).stop) es ∧ Writes (interval start (P).stop) es := by
  let i : Fin N := ⟨j,hj⟩
  let p := bank c
  have same (a : W w) (ha : a ∈ inputs (kindOf c) p (word j)) :
      m a.val = ref a.val := (inv _ (input_range X c fit room i a ha)).symm
  have hr : row (kindOf c) p m (word j) = row (kindOf c) p ref (word j) := by
    generalize hb : word (bits := w) j = b at same ⊢
    generalize hk : kindOf c = k at same ⊢
    cases k <;> simp [inputs] at same
    · simp only [row,same.1,same.2]
    · simp only [row,same.1,same.2.1,same.2.2]
    · rfl
  have h := output_bounds X E hdH conn F hd choice c fit ref initial i
  have bound (col : Column) : interval (P).next (P).stop ((row (kindOf c) p m (word j)).address p col).val := by
    rw [hr]
    cases col with
    | outgoing => exact (P).column_interval room 3 _ h.1
    | incoming => exact (P).column_interval room 4 _ h.2
    | width => exact (P).column_interval room 5 _ h.1
  have writes := port_event_writes (kindOf c) p m (word j) _ bound
  have order : start ≤ (P).next := by
    dsimp only [Plan.next,Plan.reverseSlot,Plan.targetPort,Plan.supply,Plan.term,Plan.demand]
    change start ≤ start+_+_+_+_+_+_
    omega
  have stop : (P).next ≤ (P).stop := Nat.le_add_right ..
  refine ⟨fun x hx => (inv x hx).trans (SourceTransport.after_outside m writes (by
    intro he; exact (Nat.not_lt_of_ge he.1) hx.2)).symm,?_,fun x v hx => ?_⟩
  · apply port_event_reads
    intro a ha
    have hh := input_range X c fit room i a ha
    exact ⟨hh.1,hh.2.trans_le stop⟩
  · obtain ⟨lo,hi⟩ := writes x v hx
    exact ⟨order.trans lo,hi⟩

open Schedule OrdinalRun

include hd in
/-- The raw genuine slot reports carry the dense ordinal sequence and their
full footprint before scheduler cells are installed. -/
theorem slot_scan (c : RefreshSlot dH (2^a₀)) (fit : AllSlots.Fits (a₀ := a₀) X w)
    (room : (P).stop ≤ 2^w) (ref m : Memory w) (initial : AllSlots.SourceTables X E hdH conn F choice I ref)
    (inv : SlotInvariant P ref m) (rs : List (Report w))
    (run : let M := (template (code (kindOf c)) 0).instantiate w (bank c)
      runSegment M.program (1+(code (kindOf c)).length) (some 0) m (List.replicate N []) = some rs) :
    StageFrame.Scanned 0 N rs ∧ SlotInvariant P ref (after m (eventLog rs)) ∧
      Reads (interval start (P).stop) (eventLog rs) ∧ Writes (interval start (P).stop) (eventLog rs) := by
  let M := (template (code (kindOf c)) 0).instantiate w (bank c)
  exact StageFrame.scan M.program (1+(code (kindOf c)).length) 0 N
    (fun _ m => SlotInvariant P ref m) (NewSlots.events (kindOf c) (bank c))
    (interval start (P).stop) (interval start (P).stop)
    (fun j _ _ m => NewSlots.native _ _ m (word j))
    (fun j _ hj m hin => slot_step X E hdH conn F hd choice c fit room ref initial j hj m hin)
    (Nat.zero_le _) m rs inv (by simpa using run)

set_option maxHeartbeats 600000 in
include hd in
/-- Replay one complete fixed-slot pass inside a guarded row. The memory may
differ from the reference before the allocation, including the active frame. -/
theorem slot_valid {d : ℕ} (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → W w) (c : RefreshSlot dH (2^a₀)) (fit : AllSlots.Fits (a₀ := a₀) X w)
    (room : (P).stop ≤ 2^w) (ref m : Memory w) (initial : AllSlots.SourceTables X E hdH conn F choice I ref)
    (inv : SlotInvariant P ref m)
    (separate : ∀ x, ControlCell (C worker).params ports x → ¬ interval start (P).stop x)
    (ready : Ready C worker ports pub (word N) m) (rs : List (Report w))
    (run : let M := (template (code (kindOf c)) 0).instantiate w (bank c)
      runSegment M.program (1+(code (kindOf c)).length) (some 0) m (List.replicate N []) = some rs) :
    ValidTrace C worker ports pub (word N) 0 m rs ∧ SlotInvariant P ref (after m (eventLog rs)) ∧
      Reads (interval start (P).stop) (eventLog rs) ∧ Writes (interval start (P).stop) (eventLog rs) ∧
      Preserved (C worker).params ports m (after m (eventLog rs)) := by
  have npos : 0 < (P).capacity := by change 0 < N * 2^a₀; positivity
  have nfit : N < 2^w := by
    have hn : N ≤ (P).capacity := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a₀)
    change (P).next+6*(P).capacity ≤ _ at room
    omega
  obtain ⟨shape,last,rd,wr⟩ := slot_scan X E hdH conn F hd choice c fit room ref m initial inv rs run
  obtain ⟨valid,keep⟩ := StageFrame.Scanned.guarded C worker ports pub shape nfit _ wr separate m ready
  exact ⟨valid,last,rd,wr,keep⟩

end Slots

section Base

open IncidenceDirectory

variable {a l : ℕ} (alloc : Allocation.Plan) (Y : State a l)
local notation "T" => alloc.output w
local notation "p" => BaseOutput.params T a l

private theorem base_source_lt (cap : BaseOutput.actualCount Y = alloc.capacity) (room : alloc.stop ≤ 2^w)
    (j : ℕ) (hj : j < BaseOutput.baseCount Y) : (BaseOutput.source p (word j)).val < alloc.capacity := by
  have fits : alloc.capacity < 2^w := by
    have hp : 0 < alloc.capacity := cap ▸ (by dsimp only [BaseOutput.actualCount]; positivity)
    change alloc.next+6*alloc.capacity ≤ 2^w at room; omega
  have hb := Nat.mul_le_mul_right (2^a) (Nat.le_mul_of_pos_right (Fintype.card Y.Base) (Nat.two_pow_pos l))
  change BaseOutput.baseCount Y ≤ BaseOutput.actualCount Y at hb
  have hD : (2^a) < 2^w :=
    (Nat.le_mul_of_pos_left _ Fintype.card_pos).trans_lt (hb.trans_lt (cap ▸ fits))
  have hi := hj.trans (hb.trans_lt (cap ▸ fits))
  have hd : (p 0).val = 2^a := Nat.mod_eq_of_lt hD
  have hval : (word (bits := w) j).val = j := Nat.mod_eq_of_lt hi
  have hv : j / 2^a < Fintype.card Y.Base := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos a)).mpr hj
  have hm : j % 2^a < 2^a := Nat.mod_lt _ (Nat.two_pow_pos a)
  have div : (BinaryOp.div.eval (word (bits := w) j) (p 0)).val = j / 2^a := by
    change ((word (bits := w) j).val/(p 0).val) % _ = _
    rw [hval,hd]; exact Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt hi)
  have rem : (BinaryOp.mod.eval (word (bits := w) j) (p 0)).val = j % 2^a := by
    change ((word (bits := w) j).val % (p 0).val) % _ = _
    rw [hval,hd]; exact Nat.mod_eq_of_lt (hm.trans hD)
  have slot : ((BinaryOp.div.eval (word (bits := w) j) (p 0))*(p 1)).val < Fintype.card Y.Base*2^l := by
    rw [Fin.val_mul,div]
    exact (Nat.mod_le ..).trans_lt ((Nat.mul_le_mul_left _ (Nat.mod_le (2^l) _)).trans_lt
      (Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos l)))
  rw [← cap]
  exact word_key _ _ slot (rem ▸ hm)

theorem base_step (cap : BaseOutput.actualCount Y = alloc.capacity) (room : alloc.stop ≤ 2^w)
    (layout : (T).Layout Y) (j : ℕ) (hj : j<BaseOutput.baseCount Y) (m : Memory w)
    (prev : BaseOutput.Prefix T Y m j) :
    let es := BaseOutput.events p m (word j)
    BaseOutput.Prefix T Y (after m es) (j+1) ∧ Reads (interval alloc.start alloc.stop) es ∧
      Writes (interval alloc.start alloc.stop) es := by
  let es := BaseOutput.events p m (word j)
  let M := (template BaseOutput.visit 0).instantiate w p
  obtain ⟨rs,run,nxt,_,_,_⟩ := BaseOutput.scan_run T Y layout m j 1 prev (by omega)
  change runSegment M.program 29 (some (word j)) m [[]] = some rs at run
  rw [runSegment,BaseOutput.visit_native] at run
  have eq : [⟨es,some (word j+1)⟩] = rs := Option.some.inj run
  subst rs
  have post : BaseOutput.Prefix T Y (after m es) (j+1) := by simpa only [eventLog,List.flatMap_cons,
    List.flatMap_nil,List.append_nil] using nxt
  have low : alloc.start ≤ alloc.next := by
    dsimp only [Plan.next,Plan.reverseSlot,Plan.targetPort,Plan.supply,Plan.term,Plan.demand]
    omega
  have col (c : Fin 6) (i : W w) (hi : i.val < alloc.capacity) :
      interval alloc.start alloc.stop (((T).column c)+i).val := by
    obtain ⟨hl,hu⟩ := alloc.column_interval room c i hi
    exact ⟨low.trans hl,hu⟩
  have hb := Nat.mul_le_mul_right (2^a) (Nat.le_mul_of_pos_right (Fintype.card Y.Base) (Nat.two_pow_pos l))
  change BaseOutput.baseCount Y ≤ BaseOutput.actualCount Y at hb
  let e := (baseOrder Y).symm ⟨j,hj⟩
  have idx : (basePort (w := w) Y e) = word j := by
    rw [basePort_number]; simp [e,CursorRAM.encode,word]
  have matchEq := (BaseOutput.read_row T Y layout m prev.actual e).1
  rw [idx] at matchEq
  have destLt : (BaseOutput.destination p (BaseOutput.mate p m (word j))).val < alloc.capacity := by
    rw [matchEq,basePort_number]
    exact (encoded_lt (w := w) (baseOrder Y (Y.slots.base.target e)).isLt).trans_le (hb.trans cap.le)
  refine ⟨post,?_,?_⟩
  · intro x v h
    simp [BaseOutput.events] at h
    exact h.1 ▸ col 3 _ (base_source_lt alloc Y cap room j hj)
  · intro x v h
    simp [BaseOutput.events] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact col 0 _ ((encoded_lt (w := w) hj).trans_le (hb.trans cap.le))
    · exact col 1 _ destLt
    · exact col 2 _ ((encoded_lt (w := w) hj).trans_le (hb.trans cap.le))

open Schedule OrdinalRun

/-- Raw lane-zero scan footprint and completed prefix, independent of the
scheduler's installation of the base worker's public bank. -/
theorem base_scan (cap : BaseOutput.actualCount Y = alloc.capacity) (room : alloc.stop ≤ 2^w)
    (layout : (T).Layout Y) (m : Memory w) (actual : (T).ActualColumns Y m)
    (rs : List (Report w)) (run : let M := (template BaseOutput.visit 0).instantiate w p
      runSegment M.program 29 (some 0) m (List.replicate (BaseOutput.baseCount Y) []) = some rs) :
    StageFrame.Scanned 0 (BaseOutput.baseCount Y) rs ∧
      BaseOutput.Prefix T Y (after m (eventLog rs)) (BaseOutput.baseCount Y) ∧
      Reads (interval alloc.start alloc.stop) (eventLog rs) ∧ Writes (interval alloc.start alloc.stop) (eventLog rs) := by
  let M := (template BaseOutput.visit 0).instantiate w p
  exact StageFrame.scan M.program 29 0 (BaseOutput.baseCount Y)
    (fun j m => BaseOutput.Prefix T Y m j) (BaseOutput.events p)
    (interval alloc.start alloc.stop) (interval alloc.start alloc.stop)
    (fun j _ _ m => BaseOutput.visit_native p m (word j))
    (fun j _ hj m hin => base_step alloc Y cap room layout j hj m hin) (Nat.zero_le _) m rs
    ⟨actual,fun _ h => (Nat.not_lt_zero _ h).elim⟩ (by simpa using run)

set_option maxHeartbeats 600000 in
/-- The lane-zero base pass preserves its actual columns and its growing
prefix under the scheduler guards, using the same raw report sequence. -/
theorem base_valid {d : ℕ} (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → W w) (cap : BaseOutput.actualCount Y = alloc.capacity)
    (room : alloc.stop ≤ 2^w) (layout : (T).Layout Y)
    (separate : ∀ x, ControlCell (C worker).params ports x → ¬ interval alloc.start alloc.stop x)
    (m : Memory w) (actual : (T).ActualColumns Y m) (ready : Ready C worker ports pub (word (BaseOutput.baseCount Y)) m)
    (rs : List (Report w)) (run : let M := (template BaseOutput.visit 0).instantiate w p
      runSegment M.program 29 (some 0) m (List.replicate (BaseOutput.baseCount Y) []) = some rs) :
    ValidTrace C worker ports pub (word (BaseOutput.baseCount Y)) 0 m rs ∧
      BaseOutput.Prefix T Y (after m (eventLog rs)) (BaseOutput.baseCount Y) ∧
      Reads (interval alloc.start alloc.stop) (eventLog rs) ∧ Writes (interval alloc.start alloc.stop) (eventLog rs) ∧
      Preserved (C worker).params ports m (after m (eventLog rs)) := by
  have pos : 0 < alloc.capacity := cap ▸ (by dsimp only [BaseOutput.actualCount]; positivity)
  have lt : alloc.capacity < 2^w := by change alloc.next+6*alloc.capacity ≤ _ at room; omega
  have le := Nat.mul_le_mul_right (2^a) (Nat.le_mul_of_pos_right (Fintype.card Y.Base) (Nat.two_pow_pos l))
  change BaseOutput.baseCount Y ≤ BaseOutput.actualCount Y at le
  obtain ⟨shape,last,rd,wr⟩ := base_scan alloc Y cap room layout m actual rs run
  obtain ⟨valid,keep⟩ := StageFrame.Scanned.guarded C worker ports pub shape ((le.trans cap.le).trans_lt lt)
    _ wr separate m ready
  exact ⟨valid,last,rd,wr,keep⟩

end Base

end CompressorRecords.PortRefresh.IncidenceWorkerSafety

end VPVNP
end Computability
end OAI
