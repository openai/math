import OAI.Hierarchy.GridReceiverDirectoryFrame
import OAI.Hierarchy.GridReceiverDirectoryOrder
import OAI.Hierarchy.GridPinNativeLoops
import OAI.Hierarchy.GridReceiverDirectoryROM
import OAI.Hierarchy.GridSimulationAssign
import OAI.Hierarchy.GridRegisteredCosts

namespace OAI
/-! # Native class-major selection of the receiving tick's terminal roots

The selector reads the same key and round-robin owner as the grid compiler.
One class-major pass appends the terminal ordinal to S17 on a match. Both
live counts in S18 advance together. -/

namespace Hierarchy.GridReceiverTickDirectory
open ThreeFlat RAM PhysicalProcedure Diagonal
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open FactorBucketRAM GridPinPrefixMemory GridReceiverDirectoryOrder
open scoped Fin.CommRing

variable {W R K N d T : ℕ}

/-- Two ordinary tick-workspace inequalities and the grid's one-sector
size bound discharge every physical address of the directory builder. -/
theorem room_of_bounds {w v src n rows : ℕ} (positive : 0 < w)
    (tape : src+64*w ≤ TickWorkspace.stride v) (candidates : rows ≤ TickWorkspace.stride v)
    (smallWorkspace : TickWorkspace.base v 18+5 ≤ 15*GridDescription.sector w)
    (smallRoots : n ≤ GridPinArena.slab w) : Room (banks w v) (64*w) src n rows := by
  let g := GridPinArena.slab w
  let J := GridDescription.sector w
  have page := GridPinArena.scales w positive
  have nonzero : 0 < g := Nat.two_pow_pos _
  have positiveWord : 0 < 64*w := by omega
  change 32*g ≤ J ∧ 32*J < 2^(64*w) at page
  change n ≤ g at smallRoots
  change TickWorkspace.base v 18+5 ≤ 15*J at smallWorkspace
  have separate : TickWorkspace.base v 17+TickWorkspace.stride v ≤ TickWorkspace.base v 18 := by
    change 18*TickWorkspace.stride v+TickWorkspace.stride v ≤ 19*TickWorkspace.stride v
    omega
  have under : TickWorkspace.stride v ≤ TickWorkspace.base v 17 := by
    change TickWorkspace.stride v ≤ 18*TickWorkspace.stride v
    omega
  constructor
  · exact tape.trans under
  · exact (Nat.add_le_add_left candidates _).trans separate
  · change TickWorkspace.base v 18+5 ≤ 15*J+g; omega
  · change 15*J+g+n ≤ 15*J+3*g;omega
  · change 15*J+3*g+n ≤ 15*J+20*g;omega
  · change 15*J+20*g+2 < 2^(64*w);omega
  · exact positiveWord
  · omega
  · omega

private noncomputable def prefixIds (ht : 0 < T) (scale : ℕ) (cost : Fin N → Fin d → ℕ) (t : Fin T) (i : ℕ) :=
  (List.range i).filterMap (row ht scale cost t)

private theorem prefix_length (ht : 0 < T) (scale : ℕ) (cost : Fin N → Fin d → ℕ) (t : Fin T) (i : ℕ) :
    (prefixIds ht scale cost t i).length ≤ i :=
  (List.length_filterMap_le ..).trans_eq List.length_range

private theorem natural_state (A : Banks) (src scale : ℕ) (ht : 0 < T)
    (cost : Fin N → Fin d → ℕ) (t : Fin T)
    (L : ℕ) (length : L=((20*(scale+1)+2)^d)*N) (room : Room A W src N L)
    (classes : (20*(scale+1)+2)^d < 2^W) (ticks : T < 2^W)
    (input boot : Memory W)
    (keys : ∀ f, input (A.keys+f.val)=(factorKey scale cost f:Word W))
    (owners : ∀ f, input (A.owners+f.val)=((FactorAllocation.owner ht scale cost f).val:Word W))
    (start : Published A ([] : List (Fin N)) input boot) (tick : boot (A.scratch+1)=(t.val:Word W)) :
    ∀ i ≤ L, let mem := iterRows step (params A W N L) boot i
      Published A (prefixIds ht scale cost t i) input mem ∧ mem (A.scratch+1)=(t.val:Word W) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨start,tick⟩
  | succ i ih =>
    intro hi
    let old := iterRows step (params A W N L) boot i
    let xs := prefixIds ht scale cost t i
    obtain ⟨ok,got⟩ := ih (by omega)
    change Published A xs input old at ok
    have pos : 0 < N := by by_contra! ne; simp [show N=0 by omega] at length; omega
    let f : Fin N := ⟨i%N,Nat.mod_lt _ pos⟩
    let key := factorKey scale cost f
    let own := FactorAllocation.owner ht scale cost f
    let hit := key=i/N ∧ own.val=t.val
    have size : xs.length ≤ i := prefix_length ..
    have roomRoots := room.separate
    have roomKeys := room.key
    have roomOwners := room.owner
    have roomHigh := room.high
    have nf := f.isLt
    have read (a : ℕ) (lo : A.keys ≤ a) (hi' : a < A.scratch) : old a=input a :=
      ok.frame a (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl hi')
    have keyFit : key < 2^W := (finFunctionFinEquiv (FactorAllocation.key scale cost f)).isLt.trans classes
    have physically : iterRows step (params A W N L) boot (i+1)=nextMem A hit f.val xs.length old :=
      step_at A src L i room (by omega) f rfl xs.length size key own.val t.val keyFit
        (own.isLt.trans ticks) (t.isLt.trans ticks) old
        ((read _ (by omega) (by omega)).trans (keys f))
        ((read _ (by omega) (by omega)).trans (owners f)) got ok.controls.2.1
    have typed : prefixIds ht scale cost t (i+1) = if hit then xs++[f] else xs := by
      rw [prefixIds,List.range_succ,List.filterMap_append]
      simp only [List.filterMap_cons,List.filterMap_nil]
      rw [show row ht scale cost t i = (if key=i/N ∧ own=t then some f else none) from row_at ht scale cost t i f rfl]
      by_cases yes : hit
      · have both : key=i/N ∧ own=t := ⟨yes.1,Fin.ext yes.2⟩
        simp [yes,both,xs,prefixIds]
      · have neither : ¬(key=i/N ∧ own=t) := fun h=>yes ⟨h.1,congrArg Fin.val h.2⟩
        simp [yes,neither,xs,prefixIds]
    dsimp only
    rw [physically,typed]
    refine ⟨next_good A src L i room (by omega) xs size old input ok f hit,?_⟩
    dsimp only [nextMem,put]
    split_ifs <;> first | omega

/-- Run the selector from the two physical registered banks and the single
big-endian word on the original T input. Scratch and directory offsets are
independent of selector contents. All unaffected addresses retain their exact
incoming values, including both archive directories needed by terminal replay. -/
theorem build_spec (A : Banks) (src scale : ℕ) (ht : 0 < T) (cost : Fin N → Fin d → ℕ)
    (t : Fin T) (room : Room A W src N (((20*(scale+1)+2)^d)*N))
    (classes : (20*(scale+1)+2)^d < 2^W) (ticks : T < 2^W) :
    let L := ((20*(scale+1)+2)^d)*N
    (build A W src N L).Spec
      (fun mem => (∀ f, mem (A.keys+f.val)=(factorKey scale cost f:Word W)) ∧
        (∀ f,mem (A.owners+f.val)=((FactorAllocation.owner ht scale cost f).val:Word W)) ∧
        ∀ j < W,mem (src+j)=((t.val.testBit (W-1-j)).toNat:Word W))
      (fun mem out => Ticked A (FactorAllocation.factors scale cost (List.finRange N) t) (t.val:Word W) mem out)
      (clock W L) := by
  intro L pcs regs pubs M pc reg pub exit rom data cfg input entry pre
  obtain ⟨keys,owners,header⟩ := pre
  let blank := zeroed A input
  let raw := fun i => t.val.testBit (W-1-i)
  let cnt := A.controls
  let slot := A.scratch+1
  let boot := RAM.fillSegment slot 1 (fun a => TraceAdmission.inputWord (W:=W) raw (a-slot)) blank
  have span := room.original
  have rst := room.separate
  have key := room.key
  have own := room.owner
  have high := room.high
  have top := room.address
  have pos := room.positive
  have clear : (GridPassageRAMInit.procedure W cnt 5).Exec input blank (4+5*6) :=
    GridPassageRAMInit.exec cnt 5 input (by dsimp [cnt]; omega)
  have loaded : (TraceAdmission.inputPacker W src slot 1).Exec blank boot (1*(5*W+6)+6) := by
    apply Procedure.Spec.exec (TraceAdmission.inputPacker_run src slot 1 raw (Or.inr (by dsimp [slot]; omega))
      (by dsimp [slot]; omega) (by omega))
    intro i hi
    have read := GridPassageRAMInit.clear_out cnt 5 input (a:=src+i) (Or.inl (by dsimp [cnt]; omega))
    exact read.trans (header i (by omega))
  have outside (a : ℕ) (ha : a < slot ∨ slot+1 ≤ a) : boot a=blank a := by
    dsimp [boot,RAM.fillSegment]
    exact ite_eq_right (by omega)
  have packed : boot slot=(t.val:Word W) := by
    simp only [boot,RAM.fillSegment,ite_eq_left (show slot ≤ slot ∧ slot < slot+1 by omega),Nat.sub_self]
    have ix : ((t.val:Word W)).val=t.val := Fin.val_cast_of_lt (t.isLt.trans ticks)
    convert unpack_tick (t.val:Word W) using 1; simp [raw,ix]
  have base : Published A ([] : List (Fin N)) input boot := by
    constructor
    · intro j; exact Fin.elim0 j
    · have read (j : ℕ) (hj : j < 5) : boot (cnt+j)=0 :=
        (outside _ (.inl (by dsimp [cnt,slot]; omega))).trans (GridPassageRAMInit.clear_in cnt 5 input hj)
      exact ⟨by simpa [cnt] using read 0 (by decide),read 1 (by decide),read 2 (by decide),
        read 3 (by decide),read 4 (by decide)⟩
    · intro a _ c s
      exact (outside _ (by dsimp [slot]; omega)).trans (GridPassageRAMInit.clear_out cnt 5 input c)
  let out := iterRows step (params A W N L) boot L
  have scan : (FactorBucketRAM.procedure ops (params A W N L)).Exec boot out (3+L*34) :=
    Procedure.Spec.exec (GridPinNativeLoops.loop_spec ops step (fun reg pub v st rs m => executes reg pub v st rs m)
      (params A W N L) L room.length rfl) boot trivial
  have run : (build A W src N L).Exec input out (clock W L) := Procedure.Exec.then (Procedure.Exec.then clear loaded) scan
  obtain ⟨time,le,stop,mem,adv,hpc,eqn⟩ := run M pc reg pub exit rom data cfg input entry rfl
  subst mem
  refine ⟨time,le,stop,out,adv,hpc,?_⟩
  have result := (natural_state A src scale ht cost t L rfl room classes ticks input boot keys owners base packed L le_rfl)
  exact ⟨by simpa only [prefixIds,L,GridReceiverDirectoryOrder.rows] using result.1,result.2⟩


/-- The tick index and thresholds come from the first fields of the true
locally mounted header. All indices here are relative to its first input bit. -/
theorem header_tick {w text d ell : ℕ} (fits : text ≤ w^2) (raw : Fin (w^2) → Bool)
    (target : Word (64*w)) (args : Fin d → Word (64*w)) (sel : Fin ell → Bool) (j : Fin (64*w)) :
    (GridReceiverHeader.header text fits raw target args sel)[text+j.val]'(by
      rw [GridReceiverHeader.length]
      have hj := j.isLt
      have words : 64*w ≤ (d+1)*(64*w) := Nat.le_mul_of_pos_left _ (Nat.succ_pos d)
      omega) = target.val.testBit (64*w-1-j.val) := by
  let i := finProdFinEquiv ((0 : Fin (d+1)),j)
  have ix : i.val=j.val := by simp [i,finProdFinEquiv_apply_val]
  have lti : j.val < (d+1)*(64*w) := ix ▸ i.isLt
  unfold GridReceiverHeader.header
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simpa using lti),List.getElem_ofFn]
  have same : (⟨j.val,lti⟩ : Fin ((d+1)*(64*w))) = i := Fin.ext ix.symm
  rw [same]
  simp [i]

theorem header_threshold {w text d ell : ℕ} (fits : text ≤ w^2) (raw : Fin (w^2) → Bool)
    (target : Word (64*w)) (args : Fin d → Word (64*w)) (sel : Fin ell → Bool) (pos : 0 < w)
    (z : Fin (GridReceiverHeader.count w*(64*w))) :
    (GridReceiverHeader.header text fits raw target args sel)[text+((d+1)*(64*w)+z.val)]'(by
      rw [GridReceiverHeader.length];have := z.isLt;omega) = FactorBucketRAM.thresholdBit (64*w) z.val := by
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective z
  let W := 64*w
  have wp : 0 < W := by dsimp [W];omega
  have idx : (finProdFinEquiv (i,j)).val=i.val*W+j.val := by simp [finProdFinEquiv_apply_val,W,Nat.add_comm,Nat.mul_comm]
  have dv : (finProdFinEquiv (i,j)).val/W = i.val := by
    rw [idx,Nat.mul_comm _ W,Nat.mul_add_div wp,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have md : (finProdFinEquiv (i,j)).val%W=j.val := by
    rw [idx,Nat.mul_comm i.val W,Nat.mul_add_mod_self_left]
    exact Nat.mod_eq_of_lt j.isLt
  unfold GridReceiverHeader.header
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_ofFn,Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simpa using (finProdFinEquiv (i,j)).isLt),List.getElem_ofFn]
  change GridReceiverHeader.wordBits (64*w) (GridReceiverHeader.thresholdWords w)
    (finProdFinEquiv (i,j)) = _
  rw [GridReceiverHeader.word_at,GridReceiverHeader.threshold_at pos]
  change _ = (FactorBucket.threshold ((finProdFinEquiv (i,j)).val/W)).testBit
    (W-1-(finProdFinEquiv (i,j)).val%W)
  rw [dv,md]

/-- T runs exactly the same registered cost classifier as the outer evaluator,
then elects the roots that its incoming index names. -/
def receiver (w v text argCount N d T : ℕ) : Procedure (64*w) :=
  (GridSimulation.assign w ((2+text)+(argCount+1)*(64*w)) N d T).seq
    (build (banks w v) (64*w) (2+text) N (((20*(w+1)+2)^d)*N))

theorem receiver_hardware (w v text argCount N d T : ℕ) :
    let M := receiver w v text argCount N d T
    M.labels ≤ 512 ∧ M.registers ≤ 160 ∧ M.slots ≤ 128 := by
  let directory := build (banks w v) (64*w) (2+text) N (((20*(w+1)+2)^d)*N)
  have limits := hardware (banks w v) (64*w) (2+text) N (((20*(w+1)+2)^d)*N)
  change directory.labels ≤ 70 ∧ directory.registers ≤ 40 ∧ directory.slots ≤ 16 at limits
  change (15+((3+digitOps.length)+(3+keyOps.length)+(3+clearOps.length)+(3+ownerOps.length)))+directory.labels ≤ 512 ∧
    (8+(14+14+14+14))+directory.registers ≤ 160 ∧ (4+(12+12+12+12))+directory.slots ≤ 128
  have labels : (15+((3+digitOps.length)+(3+keyOps.length)+(3+clearOps.length)+(3+ownerOps.length))) ≤ 442 := by decide
  omega

/-- Compiling the registered keys and selecting this directory together
uses linear time in the number of terminal factors, with a structural
polynomial depending only on the fixed resource dimension. -/
theorem receiver_time (w N d : ℕ) :
    GridSimulation.assignTime w N d+clock (64*w) (((20*(w+1)+2)^d)*N) ≤
      (FactorBucketRAM.budgetConstant d+8000+34*22^d)*(w+1)^(d+2)*(N+1) := by
  let U := (w+1)^(d+2)*(N+1)
  have grow (j : ℕ) (hj : j ≤ d+2) : (w+1)^j ≤ U :=
    (Nat.pow_le_pow_right (by omega) hj).trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos N))
  have square := grow 2 (by omega)
  have prev : (w+1)^(d+1)*(N+1) ≤ U := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  have classN : ((20*(w+1)+2)^d)*N ≤ 22^d*U := calc
    _ ≤ (22*(w+1))^d*(N+1) := Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) (Nat.le_succ _)
    _ = 22^d*((w+1)^d*(N+1)) := by rw [mul_pow];ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega)))
  have compile : FactorBucketRAM.ticks w N d ≤ FactorBucketRAM.budgetConstant d*U := by
    have total := FactorBucketRAM.clock_bound w N d
    rw [Nat.mul_assoc] at total
    exact total.trans (Nat.mul_le_mul_left _ prev)
  change _ ≤ (FactorBucketRAM.budgetConstant d+8000+34*22^d)*((w+1)^(d+2))*(N+1)
  rw [Nat.mul_assoc _ _ (N+1)]
  change _ ≤ (FactorBucketRAM.budgetConstant d+8000+34*22^d)*U
  unfold GridSimulation.assignTime GridReceiverHeader.count clock
  nlinarith only [compile,square,classN]

theorem registered_rows {w D : ℕ} (p : TraceAdmission.Resources.Parameters ℕ)
    (dest : Fin p.lanes → Fin p.roots) (work : Fin p.roots → ℕ) (m : Memory (64*w))
    (reg : TraceAdmission.Resources.Registered D (14*GridDescription.sector w) p dest work m)
    (v : Fin p.roots) (j : Fin (p.directions+2)) :
    (m ((GridPinArena.assignmentBanks w).resources+(v.val*(p.directions+2)+j.val))).val=
      TraceAdmission.Resources.cost p dest work v j := by
  simpa [GridPinArena.assignmentBanks,Nat.add_assoc] using TraceAdmission.Resources.Registered.cost_read p dest work reg v j

theorem receiver_spec {w v text argCount N d T : ℕ} (pos : 0 < w) (ht : 0 < T) (hd : 0 < d)
    (cost : Fin N → Fin d → ℕ) (t : Fin T) (input : Memory (64*w))
    (nrows : N*d ≤ GridPinArena.slab w) (thresholds : 20*(w+1)+1 ≤ GridPinArena.slab w)
    (items : N ≤ GridPinArena.slab w) (groups : (20*(w+1)+2)^d ≤ GridPinArena.slab w)
    (steps : N*d*(20*(w+1)+1) < 2^(64*w)) (dim : d < 2^(64*w)) (ticks : T < 2^(64*w))
    (low : (2+text)+(argCount+1)*(64*w)+(64*w)*GridReceiverHeader.count w ≤ GridDescription.sector w)
    (room : Room (banks w v) (64*w) (2+text) N (((20*(w+1)+2)^d)*N))
    (rawThresholds : ∀ i < (64*w)*GridReceiverHeader.count w,
      input ((2+text)+(argCount+1)*(64*w)+i)=((FactorBucketRAM.thresholdBit (64*w) i).toNat:Word (64*w)))
    (rawTick : ∀ i < 64*w,input (2+text+i)=((t.val.testBit (64*w-1-i)).toNat:Word (64*w)))
    (register : ∀ (f : Fin N) (j : Fin d),
      (input ((GridPinArena.assignmentBanks w).resources+(f.val*d+j.val))).val=cost f j) :
    let L := ((20*(w+1)+2)^d)*N
    (receiver w v text argCount N d T).Spec (·=input)
      (fun _ out=>∃ mid, GridSimulation.Assigned ht cost input mid ∧
        Ticked (banks w v) (FactorAllocation.factors w cost (List.finRange N) t) (t.val:Word (64*w)) mid out)
      (GridSimulation.assignTime w N d+clock (64*w) L) := by
  intro L
  let A := banks w v
  let thresholdsAt := (2+text)+(argCount+1)*(64*w)
  have run : (GridSimulation.assign w thresholdsAt N d T).Spec (·=input)
      (fun _ out=>GridSimulation.Assigned ht cost input out) (GridSimulation.assignTime w N d) :=
    GridSimulation.assign_spec pos ht hd cost input nrows thresholds items groups steps dim ticks low rawThresholds register
  have keyFit : (20*(w+1)+2)^d < 2^(64*w) := by have a := GridPinArena.scales w pos; omega
  apply PhysicalProcedure.Procedure.Spec.seq run (build_spec A (2+text) w ht cost t room keyFit ticks)
  intro _ out assigned
  refine ⟨assigned.key,assigned.owner,?_⟩
  intro i hi
  have first : 2+text+i < 14*GridDescription.sector w := by
    have lim : 64*w ≤ (argCount+1)*(64*w) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    omega
  rw [assigned.frame _ (by
    unfold GridSimulation.protectedAddress FactorBucketRAM.untouched FactorBucketRAM.Outside
    dsimp [GridPinArena.assignmentBanks]; omega),rawTick i hi]

/-- The post-registration controller interface. Its only data inputs are the
surviving actual bit header and the resource table certified by the native
registration pass. The following tick and threshold reads are both derived. -/
theorem receiver_registered {w v text args ell D T : ℕ} (pos : 0 < w) (ht : 0 < T)
    (bound : text ≤ w^2) (self : Fin (w^2) → Bool) (parameters : Fin args → Word (64*w))
    (selector : Fin ell → Bool) (p : TraceAdmission.Resources.Parameters ℕ)
    (dest : Fin p.lanes → Fin p.roots) (work : Fin p.roots → ℕ) (t : Fin T) (input : Memory (64*w))
    (reg : TraceAdmission.Resources.Registered D (14*GridDescription.sector w) p dest work input)
    (nrows : p.roots*(p.directions+2) ≤ GridPinArena.slab w)
    (thresholds : 20*(w+1)+1 ≤ GridPinArena.slab w) (items : p.roots ≤ GridPinArena.slab w)
    (groups : (20*(w+1)+2)^(p.directions+2) ≤ GridPinArena.slab w)
    (steps : p.roots*(p.directions+2)*(20*(w+1)+1) < 2^(64*w))
    (dim : p.directions+2 < 2^(64*w)) (ticks : T < 2^(64*w))
    (low : (2+text)+(args+1)*(64*w)+(64*w)*GridReceiverHeader.count w ≤ GridDescription.sector w)
    (room : Room (banks w v) (64*w) (2+text) p.roots (((20*(w+1)+2)^(p.directions+2))*p.roots))
    (hold : let hdr := GridReceiverHeader.header text bound self (t.val:Word (64*w)) parameters selector
      ∀ x : Fin hdr.length, input (2+x.val)=((hdr[x.val]).toNat:Word (64*w))) :
    let cost := TraceAdmission.Resources.cost p dest work
    let rows := ((20*(w+1)+2)^(p.directions+2))*p.roots
    (receiver w v text args p.roots (p.directions+2) T).Spec (·=input)
      (fun _ out=>∃ mid, GridSimulation.Assigned ht cost input mid ∧
        Ticked (banks w v) (FactorAllocation.factors w cost (List.finRange p.roots) t) (t.val:Word (64*w)) mid out)
      (GridSimulation.assignTime w p.roots (p.directions+2)+clock (64*w) rows) := by
  intro cost rows
  apply receiver_spec pos ht (by omega) cost t input nrows thresholds items groups steps dim ticks low room
  · intro i hi
    have fi : i < GridReceiverHeader.count w*(64*w) := by simpa [Nat.mul_comm] using hi
    let bitIndex : Fin (GridReceiverHeader.count w*(64*w)) := ⟨i,fi⟩
    have rd := hold ⟨text+((args+1)*(64*w)+i),by rw [GridReceiverHeader.length]; omega⟩
    rw [header_threshold bound self (t.val:Word (64*w)) parameters selector pos bitIndex] at rd
    simpa [Nat.add_assoc] using rd
  · intro i hi
    let bitIndex : Fin (64*w) := ⟨i,hi⟩
    have wordFit := Fin.val_cast_of_lt (t.isLt.trans ticks)
    have inHeader : text+i < (GridReceiverHeader.header text bound self (t.val:Word (64*w)) parameters selector).length := by
      rw [GridReceiverHeader.length]
      have words : 64*w ≤ (args+1)*(64*w) := Nat.le_mul_of_pos_left _ (Nat.succ_pos args)
      omega
    have rd := hold ⟨text+i,inHeader⟩
    rw [header_tick bound self (t.val:Word (64*w)) parameters selector bitIndex] at rd
    simpa [bitIndex,wordFit,Nat.add_assoc] using rd
  · exact registered_rows p dest work input reg

/-- An owner guard can read the scalar owner bank directly at the ordinal
published in S17. Its value equals the mounted incoming target word. -/
theorem selected_owner_read {w v N d T : ℕ} (ht : 0 < T) (cost : Fin N → Fin d → ℕ)
    (t : Fin T) (src : ℕ) (room : Room (banks w v) (64*w) src N (((20*(w+1)+2)^d)*N))
    {input mid out : Memory (64*w)} (reg : GridSimulation.Assigned ht cost input mid)
    (pub : Ticked (banks w v) (FactorAllocation.factors w cost (List.finRange N) t) (t.val:Word (64*w)) mid out)
    (j : Fin (FactorAllocation.factors w cost (List.finRange N) t).length) :
    let A := banks w v
    out (A.owners+(out (A.roots+j.val)).val)=out (A.scratch+1) := by
  let A := banks w v
  let ids := FactorAllocation.factors w cost (List.finRange N) t
  let f := ids[j.val]
  have elected : t=FactorAllocation.owner ht w cost f :=
    (FactorAllocation.mem_factors_iff_owner ht w cost f t).mp (List.getElem_mem ..)
  have roots := room.separate
  have key := room.key
  have owner := room.owner
  have high := room.high
  have nf := f.isLt
  have count : ids.length ≤ ((20*(w+1)+2)^d)*N := by
    simpa only [prefixIds,GridReceiverDirectoryOrder.rows] using
      prefix_length ht w cost t (((20*(w+1)+2)^d)*N)
  change A.roots+(((20*(w+1)+2)^d)*N) ≤ A.controls at roots
  change A.controls+5 ≤ A.keys at key
  change A.keys+N ≤ A.owners at owner
  change A.owners+N ≤ A.scratch at high
  have frame : out (A.owners+f.val)=mid (A.owners+f.val) :=
    pub.frame _ (.inr (by change A.roots+ids.length ≤ A.owners+f.val; omega))
      (.inr (by change A.controls+5 ≤ A.owners+f.val; omega))
      (.inl (by change A.owners+f.val < A.scratch; omega))
  have ordinal : out (A.roots+j.val)=(f.val:Word (64*w)) := pub.roots j
  have ownerWord : mid (A.owners+f.val)=((FactorAllocation.owner ht w cost f).val:Word (64*w)) := reg.owner f
  change out (A.owners+(out (A.roots+j.val)).val)=out (A.scratch+1)
  rw [ordinal,Fin.val_cast_of_lt (nf.trans room.nfit),frame,ownerWord,←elected,pub.targetAt]

end Hierarchy.GridReceiverTickDirectory

end OAI
