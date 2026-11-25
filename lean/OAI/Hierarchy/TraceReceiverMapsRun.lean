import OAI.Hierarchy.TraceReceiverMapProgram

namespace OAI
/-! # Counted execution and retained pin maps for the selected terminal roots -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
open RAM.TickTerminalRoot

variable {W : ℕ}

/-- A word outside every native workspace write of the mounted terminal root. -/
structure KeptByRoot (A : Arena) (m : Memory W) (a : ℕ) : Prop where
  jobs : retained A m a
  state : a<A.control ∨ A.control+4≤a
  seed : a<A.seed ∨ A.seed+26≤a
  commands : a<A.commands ∨ A.commands+7*((terminal A (natMemory m)).halves+2)≤a
  arguments : a<A.arguments ∨ A.arguments+7*((terminal A (natMemory m)).halves+2)≤a

theorem KeptByRoot.read {A : Arena} {m : Memory W} {a : ℕ} (h : KeptByRoot A m a) :
    RAM.TickTerminalRoot.output A m a=m a := output_frame A m a h.jobs h.state h.seed h.commands h.arguments

def mapSeed (A : Arena) (tasks header : ℕ) (m : Memory W) :=
  TraceReceiverMapSave.seedImage header tasks A.control (decrease A m)

def mapStep (A : Arena) (tasks header dst len : ℕ) (m : Memory W) : Memory W :=
  let out := RAM.TickTerminalRoot.output A (mapSeed A tasks header m)
  fillSegment dst len (fun a=>out (A.map+(a-dst))) out

def mapImages (A : Arena) (tasks header : ℕ) (dst len : ℕ → ℕ) (m : Memory W) : ℕ → Memory W
  | 0 => m
  | i+1 => mapStep A tasks header (dst i) (len i) (mapImages A tasks header dst len m i)

def mapStepCost (A : Arena) (tasks header len : ℕ) (m : Memory W) :=
  let raw := natMemory (mapSeed A tasks header m)
  (4+3*(2*(TraceReceiverMapSave.seedWord W header tasks A.control).binds+4)) +
    (oneCost W A (terminal A raw) raw + (13+22*len))

structure MapBounds (A : Arena) (tasks header dst len : ℕ) (m : Memory W) : Prop where
  headFit : header+3 < 2^W
  headerBelow : header+3 ≤ dst
  dstFit : dst+len < 2^W
  srcFit : A.map+len ≤ 2^W
  scratch : A.map+len ≤ dst ∨ dst+len ≤ A.map
  unaffected : ∀ a,TraceReceiverMapSave.sample tasks A.control (decrease A m) a →
    a<header ∨ header+3≤a
  root : RootBounds A (mapSeed A tasks header m)
  headerKept : ∀ j : Fin 3, KeptByRoot A (mapSeed A tasks header m) (header+j.val)
  destination : let raw:=decrease A m
    (RAM.HistoryCommandTable.readTask raw (TraceReceiverMapSave.taskWord tasks A.control raw)).pinMap=(dst:Word W)
  count : let raw:=decrease A m
    let t:=RAM.HistoryCommandTable.readTask raw (TraceReceiverMapSave.taskWord tasks A.control raw)
    (RAM.HistoryCommandTable.readNode raw t.child).pins=(len:Word W)

theorem mapStep_run (A : Arena) (tasks header dst len : ℕ) (m : Memory W)
    (h : MapBounds A tasks header dst len m) :
    ((TraceReceiverMapSave.seed W header tasks A.control).seq (TraceReceiverMapSave.one W A header)).Spec
      (·=decrease A m) (fun _ z=>z=mapStep A tasks header dst len m) (mapStepCost A tasks header len m) := by
  let raw := decrease A m
  let m0 := mapSeed A tasks header m
  let out := RAM.TickTerminalRoot.output A m0
  have saved := TraceReceiverMapSave.seed_at header tasks A.control raw h.headFit
  have kept (i : Fin 3) : out (header+i.val)=m0 (header+i.val) := (h.headerKept i).read
  have k0 : out header=((header+1:ℕ):Word W) := (kept 0).trans saved.1
  have k1 : out (header+1)=(dst:Word W) := (kept 1).trans (saved.2.1.trans h.destination)
  have k2 : out (header+2)=(len:Word W) := (kept 2).trans (saved.2.2.trans h.count)
  have hf := h.headFit
  have hb := h.headerBelow
  have hv : (header:Word W).val=header := Fin.val_cast_of_lt (by omega)
  have h1 : ((header+1:ℕ):Word W).val=header+1 := Fin.val_cast_of_lt (by omega)
  have h2 : (((header+1:ℕ):Word W)+1).val=header+2 := by
    rw [←Nat.cast_one (R:=Word W),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
  have a : (TraceReceiverMapSave.seed W header tasks A.control).Spec (·=raw) (fun _ x=>x=m0)
      (4+3*(2*(TraceReceiverMapSave.seedWord W header tasks A.control).binds+4)) := TraceReceiverMapSave.seed_run header tasks A.control raw h.headFit h.unaffected
  have b : (TraceReceiverMapSave.one W A header).Spec (·=m0)
      (fun _ x=>x=fillSegment dst len (fun a=>out (A.map+(a-dst))) out)
      (oneCost W A (terminal A (natMemory m0)) (natMemory m0)+(13+22*len)) := TraceReceiverMapSave.run A header dst len m0 h.root h.dstFit h.srcFit (by
    change out (out (header:Word W).val).val=_
    rw [hv,k0,h1,k1]) (by
    change out (out (header:Word W).val+1).val=_
    rw [hv,k0,h2,k2]) (Or.inl (by rw [hv];omega)) (by
    change (out (header:Word W).val).val < dst ∨ _
    rw [hv,k0,h1]; exact Or.inl (by omega)) h.scratch
  intro pp rr kk machine
  exact Procedure.Spec.mono (A:=(TraceReceiverMapSave.seed W header tasks A.control).seq
    (TraceReceiverMapSave.one W A header)) (a.seq b (fun _ _ hr=>hr))
    (fun _ hr=>hr) (fun _ _ hr=>hr.choose_spec.2) le_rfl machine

/-- Exact preservation relative to the decremented loop memory. -/
theorem mapStep_frame (A : Arena) (tasks header dst len a : ℕ) (m : Memory W)
    (seed : a<header ∨ header+3≤a) (save : a<dst ∨ dst+len≤a)
    (keep : KeptByRoot A (mapSeed A tasks header m) a) :
    mapStep A tasks header dst len m a=decrease A m a := by
  have off : ¬(dst≤a ∧ a<dst+len) := by omega
  have hout : ¬(header≤a ∧ a<header+3) := by omega
  calc
    mapStep A tasks header dst len m a = TickTerminalRoot.output A (mapSeed A tasks header m) a := by
      simp only [mapStep,fillSegment,ite_eq_right off]
    _ = mapSeed A tasks header m a := keep.read
    _ = decrease A m a := by simp only [mapSeed,TraceReceiverMapSave.seedImage,fillSegment,ite_eq_right hout]

theorem mapStep_at (A : Arena) (tasks header dst len : ℕ) (m : Memory W) (i : Fin len) :
    mapStep A tasks header dst len m (dst+i.val)=
      RAM.TickTerminalRoot.output A (mapSeed A tasks header m) (A.map+i.val) := by
  have hit : dst≤dst+i.val ∧ dst+i.val<dst+len := by have := i.isLt;omega
  simp only [mapStep,fillSegment,ite_eq_left hit,Nat.add_sub_cancel_left]

/-- The actual selected count is decremented by the hardware. Each previous
root is charged by its own physical program and pin count. -/
theorem maps_run (A : Arena) (tasks header : ℕ) (dst len : ℕ → ℕ) (m : Memory W) (n : ℕ)
    (initial : (m (countdown (W:=W) A).val).val=n)
    (lim : ∀ i<n, MapBounds A tasks header (dst i) (len i) (mapImages A tasks header dst len m i))
    (outside : (countdown (W:=W) A).val<header ∨ header+3≤(countdown (W:=W) A).val)
    (free : ∀ i<n, (countdown (W:=W) A).val<dst i ∨ dst i+len i≤(countdown (W:=W) A).val)
    (keep : ∀ i<n,KeptByRoot A (mapSeed A tasks header (mapImages A tasks header dst len m i))
      (countdown (W:=W) A).val) :
    (maps W A tasks header).Spec (·=m) (fun _ z=>z=mapImages A tasks header dst len m n)
      (4+7*n+∑ j ∈ Finset.range n,let i:=n-(j+1)
        mapStepCost A tasks header (len i) (mapImages A tasks header dst len m i)) := by
  let c := countdown (W:=W) A
  let imgs := mapImages A tasks header dst len m
  let inv (z : ℕ) (x : Memory W) := z≤n ∧ x=imgs (n-z)
  let cost (k : ℕ) := let i:=n-(k+1);mapStepCost A tasks header (len i) (imgs i)
  have run : (maps W A tasks header).Spec (fun x=>inv n x ∧ (x c.val).val=n)
      (fun _ x=>inv 0 x) (4+7*n+∑ k ∈ Finset.range n,cost k) := Procedure.counted_cost
    ((TraceReceiverMapSave.seed W header tasks A.control).seq (TraceReceiverMapSave.one W A header)) c n cost inv (by
      intro z x invariant counter
      obtain ⟨bound,eqn⟩ := invariant
      let i := n-(z+1)
      have hi : i<n := by dsimp [i];omega
      change x=imgs i at eqn
      subst x
      intro _ _ _ machine
      refine Procedure.Spec.mono (A:=(TraceReceiverMapSave.seed W header tasks A.control).seq (TraceReceiverMapSave.one W A header)) (mapStep_run A tasks header (dst i) (len i) (imgs i) (lim i hi))
        (pre':=fun q => q=writeMemory (imgs i) c (imgs i c.val-1))
        (post':=fun _ q => (q c.val).val=z ∧ inv z q)
        (fun _ hr=>hr) ?_ le_rfl machine
      rintro _ _ rfl
      refine ⟨?_,by change z≤n ∧ _=imgs (n-z);rw [show n-z=i+1 by dsimp [i];omega];exact ⟨by omega,rfl⟩⟩
      rw [mapStep_frame A tasks header (dst i) (len i) c.val (imgs i) outside (free i hi) (keep i hi)]
      change (writeMemory _ c (_-1) c.val).val=_
      simp only [writeMemory,ite_true]
      rw [←Fin.cast_val_eq_self ((imgs i) c.val),←Nat.cast_one (R:=Word W),
        ←Nat.cast_sub (show 1≤((imgs i) c.val).val by omega),
        Fin.val_cast_of_lt (by have := ((imgs i) c.val).isLt;omega)]
      omega)
  intro _ _ _ machine
  exact Procedure.Spec.mono (A:=maps W A tasks header)
    (pre':=fun x=>x=m) (post':=fun _ x=>x=imgs n) (@run)
    (by rintro x rfl;exact ⟨⟨le_rfl,by simp [imgs,mapImages]⟩,initial⟩)
    (by rintro _ _ ⟨_,hr⟩;simpa using hr) le_rfl machine

def nativeRootCost (A : Arena) (tasks header : ℕ) (dst len : ℕ → ℕ) (m : Memory W) (i : ℕ) :=
  let raw := natMemory (mapSeed A tasks header (mapImages A tasks header dst len m i))
  oneCost W A (terminal A raw) raw

private theorem seedWord_binds_uniform (W header tasks ctrl : ℕ) :
    (TraceReceiverMapSave.seedWord W header tasks ctrl).binds =
      (TraceReceiverMapSave.seedWord 1 0 0 0).binds := by
  simp only [TraceReceiverMapSave.seedWord,Term.select,Term.load,Term.binary,Term.literal,
    Term.binds_letThen,Term.binds_rename,Term.binds]

private theorem add_root_costs (n base rate amount : ℕ) (roots lengths : ℕ → ℕ) :
    base+rate*n+(4+7*n+∑ i ∈ Finset.range n,(amount+13+roots i+22*lengths i)) =
      base+4+(rate+(amount+20))*n+(∑ i ∈ Finset.range n,roots i)+22*(∑ i ∈ Finset.range n,lengths i) := by
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id,←Finset.mul_sum]
  ring

/-- All costs introduced by the task and saved-map scans, with the legacy
terminal cost isolated for the original per-node tariff. -/
theorem maps_clock (A : Arena) (tasks header : ℕ) (dst len : ℕ → ℕ) (m : Memory W) (n : ℕ) :
    before_clock n+(4+7*n+∑ j ∈ Finset.range n,let i:=n-(j+1)
      mapStepCost A tasks header (len i) (mapImages A tasks header dst len m i)) =
    before_clock 0+4+
      (before_per_root+(4+3*(2*(TraceReceiverMapSave.seedWord 1 0 0 0).binds+4)+20))*n+
      (∑ i ∈ Finset.range n,nativeRootCost A tasks header dst len m i)+22*(∑ i ∈ Finset.range n,len i) := by
  let step (i : ℕ) := mapStepCost A tasks header (len i) (mapImages A tasks header dst len m i)
  let amount := 4+3*(2*(TraceReceiverMapSave.seedWord 1 0 0 0).binds+4)
  have sum : (∑ j ∈ Finset.range n,step (n-(j+1)))=∑ j ∈ Finset.range n,step j := by
    rw [←Finset.sum_range_reflect step n]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  have split (i : ℕ) : step i = amount+13+nativeRootCost A tasks header dst len m i+22*len i := by
    simp only [step,mapStepCost,nativeRootCost,seedWord_binds_uniform W header tasks A.control,amount]
    omega
  change before_clock n+(4+7*n+∑ i ∈ Finset.range n,step (n-(i+1)))=_
  rw [sum,before_rate]
  simp_rw [split]
  exact add_root_costs n (before_clock 0) before_per_root amount (nativeRootCost A tasks header dst len m) len

/-- Preserve any prior word across a consecutive range of terminal roots. -/
theorem maps_frame (A : Arena) (tasks header : ℕ) (dst len : ℕ → ℕ) (m : Memory W)
    {start stop a : ℕ} (le : start ≤ stop) (control : a≠(countdown (W:=W) A).val)
    (seed : a<header ∨ header+3≤a)
    (save : ∀ i, start ≤ i → i < stop → a<dst i ∨ dst i+len i≤a)
    (kept : ∀ i, start ≤ i → i < stop →
      KeptByRoot A (mapSeed A tasks header (mapImages A tasks header dst len m i)) a) :
    mapImages A tasks header dst len m stop a=mapImages A tasks header dst len m start a := by
  induction stop,le using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have hnext := mapStep_frame A tasks header (dst k) (len k) a
      (mapImages A tasks header dst len m k) seed (save k hk (by omega)) (kept k hk (by omega))
    simp only [decrease,writeMemory,ite_eq_right control] at hnext
    exact hnext.trans (ih (fun i h1 h2=>save i h1 (by omega)) (fun i h1 h2=>kept i h1 (by omega)))

/-- The final task-specific array contains the true S14 pin values immediately
after this root, including after every later reuse of that scratch range. -/
theorem maps_saved (A : Arena) (tasks header : ℕ) (dst len : ℕ → ℕ) (m : Memory W)
    {n i : ℕ} (hi : i<n) (j : Fin (len i))
    (ctrl : dst i+j.val≠(countdown (W:=W) A).val)
    (seed : dst i+j.val<header ∨ header+3≤dst i+j.val)
    (disjoint : ∀ k,i<k → k<n → dst i+j.val<dst k ∨ dst k+len k≤dst i+j.val)
    (keep : ∀ k,i<k → k<n → KeptByRoot A (mapSeed A tasks header (mapImages A tasks header dst len m k))
      (dst i+j.val)) :
    mapImages A tasks header dst len m n (dst i+j.val)=
      RAM.TickTerminalRoot.output A (mapSeed A tasks header (mapImages A tasks header dst len m i)) (A.map+j.val) := by
  calc
    _ = mapImages A tasks header dst len m (i+1) (dst i+j.val) :=
      maps_frame A tasks header dst len m (by omega) ctrl seed disjoint keep
    _ = _ := mapStep_at A tasks header (dst i) (len i) (mapImages A tasks header dst len m i) j

end Hierarchy.TraceReceiverTasks

end OAI
