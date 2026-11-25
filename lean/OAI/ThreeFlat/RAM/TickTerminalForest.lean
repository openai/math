import OAI.ThreeFlat.RAM.TickTerminalRoot
import OAI.ThreeFlat.RAM.TickTerminalRecords

namespace OAI
/-! # Width-independent native emission of an ordered forest of selected roots -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal HistoryTerminalTape HistoryCompiledRows BitNetwork.Ordered
open Diagonal.HistoryTerminalJoin BitLayout
open scoped Fin.CommRing BigOperators Classical

variable {W p n H : ℕ} {F : Type*} [Field F] [Fintype F] {arity : Fin n→ℕ}

def rootSum (f : Fin n→ℕ) (k : ℕ) := ∑ i : Fin k, if h : i.val<n then f ⟨i.val,h⟩ else 0

private theorem rootSum_zero (f : Fin n→ℕ) : rootSum f 0=0 := by simp [rootSum]

private theorem rootSum_step (f : Fin n→ℕ) (k : ℕ) :
    rootSum f (k+1)=rootSum f k+(if h : k<n then f ⟨k,h⟩ else 0) := by
  rw [rootSum,Fin.sum_univ_castSucc]; rfl

private theorem rootSum_mono (f : Fin n→ℕ) {i j : ℕ} (h : i≤j) : rootSum f i≤rootSum f j := by
  induction j,h using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => rw [rootSum_step]; exact ih.trans (Nat.le_add_right ..)

private theorem rootSum_fin (f : Fin n→ℕ) {k : ℕ} (h : k≤n) :
    rootSum f k=∑ i : Fin k, f (Fin.castLE h i) := by
  unfold rootSum
  apply Finset.sum_congr rfl
  intro i _
  rw [dite_eq_left (i.isLt.trans_le h)]; rfl

theorem rootSum_all (f : Fin n→ℕ) : rootSum f n=∑ i,f i := rootSum_fin f le_rfl

abbrev forest (N : ∀ i, BitNetwork F (arity i)) (pins : ∀ i, Fin (arity i)→Fin p) :=
  TickSlotForest.network (projected N pins)

def rowAddress (A : Arena) (N : ∀ i, BitNetwork F (arity i)) (i : Fin n) (r : Fin (N i).cells) (j : Fin 4) :=
  A.metadata+4*(finSigmaFinEquiv (⟨i,r⟩ : Row N)).val+j.val

omit [Field F] [Fintype F] in
private theorem rowAddress_eq (A : Arena) (N : ∀ i, BitNetwork F (arity i))
    (i : Fin n) (r : Fin (N i).cells) (j : Fin 4) :
    rowAddress A N i r j=A.metadata+4*rootSum (fun s=>(N s).cells) i.val+4*r.val+j.val := by
  rw [rowAddress,row_offset,rootSum_fin _ i.isLt.le]
  change A.metadata+4*(rowStart N i+r.val)+j.val = A.metadata+4*rowStart N i+4*r.val+j.val
  omega

/-- All four scratch banks and the control block missed by an immutable source word. -/
def free (A : Arena) (T : Root) (z : ℕ) :=
  (z<A.control ∨ A.control+5≤z) ∧ (z<A.seed ∨ A.seed+26≤z) ∧
  (z<A.commands ∨ A.commands+7*(T.halves+2)≤z) ∧ (z<A.arguments ∨ A.arguments+7*(T.halves+2)≤z) ∧
  (z<T.map ∨ T.map+T.localPins≤z)

private theorem ready_below (A : Arena) (m : Memory W) (lim : RootBounds A m) (z : ℕ) (lo : z<A.seed) :
    readyImage A m z=m z := by
  have h := lim.first
  have k := lim.disjoint
  simp only [readyImage,commandImage,seedImage,fillSegment,
    ite_eq_right (by omega : ¬(A.seed≤z ∧ z<A.seed+26)),
    ite_eq_right (by omega : ¬(A.commands≤z ∧ z<A.commands+7*((terminal A (natMemory m)).halves+2))),
    ite_eq_right (by omega : ¬(A.arguments≤z ∧ z<A.arguments+7*((terminal A (natMemory m)).halves+2)))]

private theorem framed (A : Arena) (m : Memory W) (lim : RootBounds A m)
    (span : PinSpan (terminal A (natMemory m)) (natMemory m)) (z : ℕ)
    (outside : free A (terminal A (natMemory m)) z)
    (row : let T:=terminal A (natMemory m); z<T.meta ∨ T.meta+4*T.rows≤z) : output A m z=m z := by
  obtain ⟨ctrl,seed,cmd,arg,map⟩ := outside
  have fst := lim.first
  have mid := lim.disjoint
  have endOf := lim.endArgs
  have addr : (((A.seed+5:ℕ):Word W)).val=A.seed+5 := Fin.val_cast_of_lt (by omega)
  exact output_frame A m z ⟨by rw [addr]; omega,jobs_span _ _ _ _ span z map row⟩ (by omega) seed cmd arg

/-- The local input chart consists of single-root source facts and address ranges. No
field describes a destination word or the contents of a post-execution image. -/
structure ForestRoot (A : Arena) (N : ∀ i, BitNetwork F (arity i)) (pins : ∀ i, Fin (arity i)→Fin p)
    (fixed : ℕ→Prop) (i : Fin n) (m : Memory W) : Prop where
  bounds : RootBounds A m
  span : PinSpan (terminal A (natMemory m)) (natMemory m)
  banks : PinBanks (terminal A (natMemory m)) (((A.seed+5:ℕ):Word W))
  incidences : Incidences (terminal A (natMemory m)) (natMemory m) m (pins i)
  ports : (terminal A (natMemory m)).localPins=arity i
  rowCount : (terminal A (natMemory m)).rows=(N i).cells
  hiddenCount : (HistoryStageRoot.atResult (natMemory m) (A.results+8*rootId A (natMemory m))).bits=(N i).internal
  records : Records tag (N i) (terminal A (natMemory m)).stream m
  streamBefore : let T:=terminal A (natMemory m); T.stream+4*T.rows≤A.seed
  endpointBefore : let T:=terminal A (natMemory m); T.endpoints+T.ext≤A.seed
  pinBound : let T:=terminal A (natMemory m); T.map+T.localPins≤2^W
  portsBound : 2+(terminal A (natMemory m)).localPins<2^W
  metadataFit : ∀ r j,metadata tag (N i) r j<2^W
  fixedApart : ∀ z, fixed z → let T:=terminal A (natMemory m)
    free A T z ∧ (z<T.meta ∨ T.meta+4*T.rows≤z)
  countdownApart : let T:=terminal A (natMemory m)
    let z:=A.control+4
    (z<A.seed ∨ A.seed+26≤z) ∧ (z<A.commands ∨ A.commands+7*(T.halves+2)≤z) ∧
    (z<A.arguments ∨ A.arguments+7*(T.halves+2)≤z) ∧ (z<T.map ∨ T.map+T.localPins≤z)

/-- A chart over immutable words of the selected forest, applicable to any input with
the indicated prefix counters. Root records are read at the same physical addresses by
the actual preparation procedure. -/
structure ForestRows (A : Arena) (N : ∀ i, BitNetwork F (arity i)) (pins : ∀ i, Fin (arity i)→Fin p)
    (pin : Fin p→Bool) (H : ℕ) (init : Memory W) where
  fixed : ℕ→Prop
  fixedCtrl : ∀ z,fixed z → z≠A.control+4
  totalRows : rootSum (fun i=>(N i).cells) n<2^W
  totalBits : rootSum (fun i=>(N i).internal) n<2^W
  totalCount : n<2^W
  controlFit : A.control+4<2^W
  publicPins : A.physicalPins=p
  low : cellsBase p H≤A.metadata
  metaSeed : A.metadata+4*rootSum (fun i=>(N i).cells) n≤A.seed
  metaCtrl : A.metadata+4*rootSum (fun i=>(N i).cells) n≤A.control
  seedMap : A.seed+26≤A.map
  wide : 4<2^W
  initial : init A.control=0 ∧ init (A.control+1)=(n:Word W) ∧ init (A.control+2)=0 ∧
    init (A.control+3)=0 ∧ init (A.control+4)=(n:Word W)
  physical : ∀ z<cellsBase p H, init z=TickMountedPins.memory pin z
  root : ∀ (i : Fin n) (m : Memory W), (∀ z,fixed z → m z=init z) →
    natMemory m A.control=i.val → natMemory m (A.control+1)=n →
    natMemory m (A.control+2)=rowStart N i → natMemory m (A.control+3)=bitStart N i →
    ForestRoot A N pins fixed i m

private theorem decrease_at (A : Arena) (m : Memory W) (fit : A.control+4<2^W)
    (z : ℕ) (safe : z≠A.control+4) : decrease A m z=m z := by
  simp only [decrease,countdown,Fin.val_cast_of_lt fit,writeMemory,ite_eq_right safe]

private def StateAt (A : Arena) (N : ∀ i, BitNetwork F (arity i)) (pins : ∀ i, Fin (arity i)→Fin p)
    (pin : Fin p→Bool) (H : ℕ) (init : Memory W) (D : ForestRows A N pins pin H init) (j : ℕ) (m : Memory W) :=
  natMemory m A.control=j ∧ natMemory m (A.control+1)=n ∧
  natMemory m (A.control+2)=rootSum (fun i=>(N i).cells) j ∧
  natMemory m (A.control+3)=rootSum (fun i=>(N i).internal) j ∧
  (∀ z,D.fixed z → m z=init z) ∧ (∀ z<cellsBase p H, m z=TickMountedPins.memory pin z) ∧
  ∀ (i : Fin n),i.val<j → ∀ (r : Fin (N i).cells) (c : Fin 4),
    m (rowAddress A N i r c)=HistoryFactors.metadataWord (library (forest N pins)) (finSigmaFinEquiv ⟨i,r⟩) c

variable (A : Arena) (N : ∀ i, BitNetwork F (arity i)) (pins : ∀ i, Fin (arity i)→Fin p)
variable (pin : Fin p→Bool) (init : Memory W) (D : ForestRows A N pins pin H init)

omit [Field F] in
private theorem forest_input (i : Fin n) (m : Memory W) (s : StateAt A N pins pin H init D i.val m) :
    ForestRoot A N pins D.fixed i (decrease A m) := by
  obtain ⟨a,b,c,d,f,_⟩ := s
  apply D.root i (decrease A m) (fun z h=>(decrease_at A m D.controlFit z (D.fixedCtrl z h)).trans (f z h))
  all_goals unfold natMemory
  all_goals rw [decrease_at A m D.controlFit _ (by omega)]
  · exact a
  · exact b
  · exact c.trans (rootSum_fin _ i.isLt.le)
  · exact d.trans (rootSum_fin _ i.isLt.le)

set_option maxHeartbeats 1800000 in
omit [Field F] in
private theorem forest_step (i : Fin n) (m : Memory W) (s : StateAt A N pins pin H init D i.val m) :
    StateAt A N pins pin H init D (i.val+1) (output A (decrease A m)) := by
  let b := decrease A m
  let raw := natMemory b
  let T := terminal A raw
  let cur : Word W := ((A.seed+5:ℕ):Word W)
  let ready := readyImage A b
  have h := forest_input A N pins pin init D i m s
  obtain ⟨idx,count,rowsSoFar,bitsSoFar,keep,phys,prev⟩ := s
  have breg (j : ℕ) (hj : j<4) : raw (A.control+j)=natMemory m (A.control+j) :=
    congrArg Fin.val (decrease_at A m D.controlFit _ (by omega))
  have b0 : raw A.control=i.val := by simpa only [Nat.add_zero] using (breg 0 (by decide)).trans idx
  have b1 := (breg 1 (by decide)).trans count
  have b2 := (breg 2 (by decide)).trans rowsSoFar
  have b3 := (breg 3 (by decide)).trans bitsSoFar
  have succRows := rootSum_step (fun k=>(N k).cells) i.val
  have succBits := rootSum_step (fun k=>(N k).internal) i.val
  simp only [dite_eq_left i.isLt] at succRows succBits
  have boundRows := (rootSum_mono (fun k=>(N k).cells) i.isLt).trans_lt D.totalRows
  have boundBits := (rootSum_mono (fun k=>(N k).internal) i.isLt).trans_lt D.totalBits
  have endRows : rootSum (fun k=>(N k).cells) (i.val+1) ≤ rootSum (fun k=>(N k).cells) n :=
    rootSum_mono _ i.isLt
  change rootSum (fun k=>(N k).cells) (i.val+1) = rootSum (fun k=>(N k).cells) i.val + (N i).cells at succRows
  have «meta» : T.meta=A.metadata+4*rootSum (fun k=>(N k).cells) i.val := congrArg (fun z=>A.metadata+4*z) b2
  have bits : T.beforeHidden=bitStart N i := b3.trans (rootSum_fin _ i.isLt.le)
  have cells := h.rowCount
  change T.rows=(N i).cells at cells
  have first := h.bounds.first
  have dis := h.bounds.disjoint
  have argEnd := h.bounds.endArgs
  have beforeSeed := D.metaSeed
  have beforeCtrl := D.metaCtrl
  have beforeMap := D.seedMap
  have metaStart : A.metadata ≤ T.meta := by rw [«meta»]; omega
  have rowEnd : T.meta+4*T.rows ≤ A.metadata+4*rootSum (fun k=>(N k).cells) n := by
    rw [«meta»,cells]
    omega
  have rowBelow (k : Fin n) (r : Fin (N k).cells) (j : Fin 4) :
      rowAddress A N k r j < A.metadata+4*rootSum (fun s=>(N s).cells) (k.val+1) := by
    rw [rowAddress_eq,rootSum_step,dite_eq_left k.isLt]
    change A.metadata+4*rootSum _ k.val+4*r.val+j.val <
      A.metadata+4*(rootSum _ k.val+(N k).cells)
    have hr := r.isLt
    have hj := j.isLt
    omega
  have curVal : cur.val=A.seed+5 := Fin.val_cast_of_lt (by omega)
  have saved (j : Fin 4) : retained A b (A.seed+22+j.val) := by
    have hj := j.isLt
    refine ⟨by change _≠cur.val; rw [curVal]; omega, jobs_span T raw cur ready h.span _ ?_ ?_⟩
    · left; change _<A.map; omega
    · right; exact rowEnd.trans (by omega)
  have counters := counts_out A b h.bounds saved
  have f0 : output A b A.control=((raw A.control+1:ℕ):Word W) := counters 0
  have f1 : output A b (A.control+1)=b (A.control+1) := by simpa only [raw,natMemory,Fin.cast_val_eq_self] using
    (show output A b (A.control+1)=((raw (A.control+1)):Word W) from counters 1)
  have f2 : output A b (A.control+2)=((raw (A.control+2)+T.rows:ℕ):Word W) := counters 2
  have f3 : output A b (A.control+3)=((raw (A.control+3)+(N i).internal:ℕ):Word W) := by
    rw [←h.hiddenCount]
    exact counters 3
  have before (z : ℕ) (hz : z<A.metadata+4*rootSum (fun k=>(N k).cells) n) :
      free A T z := ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),Or.inl (by omega),Or.inl (by change z<A.map; omega)⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · change (output A b A.control).val=i.val+1
    rw [f0,b0,Fin.val_cast_of_lt (Nat.lt_of_le_of_lt i.isLt D.totalCount)]
  · change (output A b (A.control+1)).val=n
    rw [f1]; exact b1
  · change (output A b (A.control+2)).val=_
    rw [f2,b2,cells,←succRows,Fin.val_cast_of_lt boundRows]
  · change (output A b (A.control+3)).val=_
    rw [f3,b3,←succBits,Fin.val_cast_of_lt boundBits]
  · intro z hz
    obtain ⟨freeZ,away⟩ := h.fixedApart z hz
    exact (framed A b h.bounds h.span z freeZ away).trans
      ((decrease_at A m D.controlFit z (D.fixedCtrl z hz)).trans (keep z hz))
  · intro z hz
    have base := D.low
    have lowMeta : z < T.meta := (hz.trans_le base).trans_le metaStart
    exact (framed A b h.bounds h.span z (before z (by omega)) (Or.inl lowMeta)).trans
      ((decrease_at A m D.controlFit z (by omega)).trans (phys z hz))
  · intro k earlier r j
    by_cases eq : k=i
    · subst k
      have rr : Records tag (N i) T.stream ready := by
        intro s t
        have sb := h.streamBefore
        change T.stream+4*T.rows≤A.seed at sb
        rw [show ready (T.stream+(4*s.val+t.val))=b _ from ready_below A b h.bounds _ (by
          have := s.isLt; have := t.isLt; omega)]
        exact h.records s t
      have inc : Incidences T raw ready (pins i) := by
        refine ⟨?_,h.incidences.covered,h.incidences.wire⟩
        intro k hk
        have eb := h.endpointBefore
        change T.endpoints+T.ext≤A.seed at eb
        exact (ready_below A b h.bounds _ (by omega)).trans (h.incidences.endpoint k hk)
      have pos := rowBelow i r j
      have keepCtrl : rowAddress A N i r j<A.control ∨ A.control+4≤rowAddress A N i r j := Or.inl (by
        have := r.isLt; have := j.isLt; omega)
      rw [output,PhysicalInputCopy.copied_outside _ _ _ _ _ keepCtrl]
      exact segment_after N pins A.metadata i T raw cur ready A.commands (loaded_tables A b dis)
        argEnd.le h.span h.banks inc h.ports D.publicPins bits
        («meta».trans (congrArg (fun z=>A.metadata+4*z) (rootSum_fin _ i.isLt.le)))
        cells rr D.wide (by have z:=h.streamBefore; change T.stream+4*T.rows≤A.seed at z; omega)
        h.pinBound h.portsBound h.metadataFit r j
    · have e : k.val< i.val := by have neq : k.val≠i.val := fun he=>eq (Fin.ext he); omega
      have pos := rowBelow k r j
      have prevBound : rootSum (fun s=>(N s).cells) (k.val+1) ≤ rootSum (fun s=>(N s).cells) i.val :=
        rootSum_mono _ e
      have prior : rowAddress A N k r j<T.meta := by rw [«meta»]; omega
      have pre : rowAddress A N k r j<A.metadata+4*rootSum (fun s=>(N s).cells) n := by
        have curPrefix := rootSum_mono (fun s=>(N s).cells) i.isLt.le
        omega
      exact (framed A b h.bounds h.span _ (before _ pre) (Or.inl prior)).trans
        ((decrease_at A m D.controlFit _ (by omega)).trans (prev k e r j))


omit [Field F] in
private theorem forest_state (k : ℕ) (hk : k≤n) : StateAt A N pins pin H init D k (images A init k) := by
  induction k with
  | zero =>
    obtain ⟨c0,c1,c2,c3,_⟩ := D.initial
    refine ⟨?_,?_,?_,?_,fun _ _=>rfl,D.physical,by intro i hi; omega⟩
    · simp only [images,natMemory,c0,Fin.val_zero]
    · simp only [images,natMemory,c1,Fin.val_cast_of_lt D.totalCount]
    · simp only [images,natMemory,c2,Fin.val_zero,rootSum_zero]
    · simp only [images,natMemory,c3,Fin.val_zero,rootSum_zero]
  | succ k ih =>
    exact forest_step A N pins pin init D ⟨k,hk⟩ (images A init k) (ih (by omega))

omit [Field F] in
/-- The true input of each emitted iteration retains the source image and true slot. -/
theorem forest_iteration (i : Fin n) :
    let m:=decrease A (images A init i.val)
    (∀ z,D.fixed z → m z=init z) ∧ natMemory m A.control=i.val := by
  have s:=forest_state A N pins pin init D i.val i.isLt.le
  refine ⟨fun z hz=>(decrease_at A _ D.controlFit z (D.fixedCtrl z hz)).trans (s.2.2.2.2.1 z hz),?_⟩
  change (decrease A _ A.control).val=i.val
  rw [decrease_at A _ D.controlFit _ (by omega)]
  exact s.1

include D

omit [Field F] in
/-- The physical checks of every iteration required by the native counted loop. -/
theorem forest_bounds (i : ℕ) (hi : i<n) : RootBounds A (decrease A (images A init i)) :=
  (forest_input A N pins pin init D ⟨i,hi⟩ (images A init i) (forest_state A N pins pin init D i hi.le)).bounds

omit [Field F] in
/-- The scan installed the genuine list length. All native root jobs preserve the
decremented countdown, including when the list starts empty. -/
theorem forest_countdown :
    (init (countdown (W:=W) A).val).val=n ∧ ∀ i<n, let b:=decrease A (images A init i)
      output A b (countdown (W:=W) A).val=b (countdown (W:=W) A).val := by
  have cv : (countdown (W:=W) A).val=A.control+4 := Fin.val_cast_of_lt D.controlFit
  constructor
  · rw [cv,D.initial.2.2.2.2,Fin.val_cast_of_lt D.totalCount]
  intro i hi b
  let k : Fin n := ⟨i,hi⟩
  let T := terminal A (natMemory b)
  have state := forest_state A N pins pin init D i hi.le
  have h := forest_input A N pins pin init D k (images A init i) state
  obtain ⟨seed,cmd,arg,map⟩ := h.countdownApart
  have raw2 : natMemory b (A.control+2)=rootSum (fun s=>(N s).cells) i :=
    (congrArg Fin.val (decrease_at A (images A init i) D.controlFit (A.control+2) (by omega))).trans state.2.2.1
  have «meta» : T.meta=A.metadata+4*rootSum (fun s=>(N s).cells) i := congrArg (fun z=>A.metadata+4*z) raw2
  have rows : T.rows=(N k).cells := h.rowCount
  have step := rootSum_step (fun s=>(N s).cells) i
  rw [dite_eq_left hi] at step
  have last : rootSum (fun s=>(N s).cells) (i+1) ≤ rootSum (fun s=>(N s).cells) n :=
    rootSum_mono _ hi
  have top := D.metaCtrl
  have fst := h.bounds.first
  have mid := h.bounds.disjoint
  have endArgs := h.bounds.endArgs
  have cursor : (((A.seed+5:ℕ):Word W)).val=A.seed+5 := Fin.val_cast_of_lt (by omega)
  rw [cv]
  apply output_frame A b _ _ (Or.inr le_rfl) seed cmd arg
  refine ⟨by rw [cursor]; omega,jobs_span T (natMemory b) _ _ h.span _ map (Or.inr ?_)⟩
  change rootSum _ (i+1)=rootSum _ i+(N k).cells at step
  rw [«meta»,rows]
  omega

omit [Field F] in
/-- The final counters equal the forest totals; every earlier root's translated
rows and every low physical source bit retain their checked values. -/
theorem forest_recorded :
    TickTerminalPadding.recorded (H:=H) (forest N pins) pin A.control A.metadata (images A init n) := by
  obtain ⟨_,_,rc,hc,_,low,actual⟩ := forest_state A N pins pin init D n le_rfl
  have rs : rootSum (fun i=>(N i).cells) n=(forest N pins).cells := rootSum_all _
  have hs : rootSum (fun i=>(N i).internal) n=(forest N pins).internal := by
    rw [rootSum_all,forest,TickSlotForest.internal]; simp [projected,BitNetwork.restrictPins]
  refine ⟨?_,?_,rows N pins A.metadata _ (fun i r j=>actual i i.isLt r j),low⟩
  · exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun z : ℕ=>(z:Word W)) (rc.trans rs))
  · exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun z : ℕ=>(z:Word W)) (hc.trans hs))


end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
