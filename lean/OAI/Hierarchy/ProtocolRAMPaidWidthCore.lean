import OAI.Hierarchy.ProtocolRAMRepairScatter
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.ProbeRouteOccurrences

namespace OAI
/-! # Positive sparse native width compilation and repeated-edge double counting -/

noncomputable section
namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {W edges : ℕ}

/-- One sparse slice of the true history. The address and amount may depend on the
accepted record. All quantities are read before this slice performs its scatters. -/
structure Slice where
  count : ℕ
  owner : Bank
  parity : Bank
  edge : Expr
  amount : Expr

def Slice.columns (s : Slice) (bank : Bank) (edges : ℕ) : Columns :=
  ⟨s.owner,s.parity,destination bank.base edges s.edge,s.amount,.lit 0⟩

def Slice.load (s : Slice) (m : Memory W) (e : Fin edges) := ∑ i : Fin s.count,
  if (s.edge.eval m (i.val:Word W)).val=e.val then (s.amount.eval m (i.val:Word W)).val else 0

structure Slice.Fits (s : Slice) (bank : Bank) (edges src W : ℕ) : Prop where
  bound : bank.base+edges<src
  room : src+2*s.count<2^W
  pair : (RepairHistogram.pair (s.columns bank edges)).Fits W src
  edge : s.edge.Fits W bank.base
  amount : s.amount.Fits W bank.base
  owner : s.owner.base+s.owner.size≤bank.base
  parity : s.parity.base+s.parity.size≤bank.base

def Slice.Out (s : Slice) (bank : Bank) (edges src : ℕ) (m : Memory W) :=
  RepairHistogram.result (s.columns bank edges) src s.count m

theorem Slice.address_eq (s : Slice) (bank : Bank) (m : Memory W) (i : Fin s.count) (edges : ℕ) (bound : bank.base+edges<2^W) :
    address (s.columns bank edges) m i=bank.base+min (s.edge.eval m (i.val:Word W)).val edges :=
  destination_val _ _ _ _ _ bound

theorem Slice.exec (s : Slice) (bank : Bank) (edges src : ℕ) (m : Memory W) (h : s.Fits bank edges src W)
    (dir : PairDirectory (s.columns bank edges) m s.count) :
    (code W src s.count (s.columns bank edges)).Exec m (s.Out bank edges src m) (ticks s.count (s.columns bank edges)) := by
  apply RepairHistogram.run _ _ _ _ dir h.pair h.room
  intro i
  have h1 := h.bound
  have h2 := h.room
  rw [s.address_eq bank m i edges (by omega)]
  have := min_le_right (s.edge.eval m (i.val:Word W)).val edges
  omega

theorem Slice.frame (s : Slice) (bank : Bank) (edges src : ℕ) (m : Memory W) (h : s.Fits bank edges src W)
    (x : ℕ) (low : x<bank.base) : s.Out bank edges src m x=m x := by
  have h1 := h.bound
  have h2 := h.room
  unfold Out RepairHistogram.result
  rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ (by intro i;rw [s.address_eq bank m i edges (by omega)];omega)]
  exact ProtocolRAMGeneratedWrite.frame_image src (2*s.count) (RepairHistogram.pair (s.columns bank edges)) m x (.inl (by omega))

theorem Slice.read (s : Slice) (bank : Bank) (src : ℕ) (m : Memory W) (h : s.Fits bank edges src W) (e : Fin edges)
    (room : (m (bank.base+e.val)).val+s.load m e<2^W) :
    (s.Out bank edges src m (bank.base+e.val)).val=(m (bank.base+e.val)).val+s.load m e := by
  let p := s.columns bank edges
  have h1 := h.bound
  have h2 := h.room
  have old := ProtocolRAMGeneratedWrite.frame_image src (2*s.count) (RepairHistogram.pair p) m (bank.base+e.val)
    (.inl (by have := e.isLt;omega))
  have eq : (∑ i : Fin s.count, if address p m i=bank.base+e.val then delta p m i else 0)=s.load m e := by
    apply Finset.sum_congr rfl
    intro i _
    have same : address p m i=bank.base+e.val ↔ (s.edge.eval m (i.val:Word W)).val=e.val := by
      rw [s.address_eq bank m i edges (by omega)]
      have lt := e.isLt
      omega
    have credit : delta p m i=(s.amount.eval m (i.val:Word W)).val := by
      simp only [delta,p,columns,Expr.eval,Nat.cast_zero,sub_zero]
    change (if address p m i=bank.base+e.val then delta p m i else 0)=_
    by_cases chosen : address p m i=bank.base+e.val
    · rw [ite_eq_left chosen,ite_eq_left (same.mp chosen),credit]
    · rw [ite_eq_right chosen,ite_eq_right (fun h=>chosen (same.mpr h))]
  have bound : (ProtocolRAM.image src (2*s.count) (RepairHistogram.pair p) m (bank.base+e.val)).val+
      (∑ i : Fin s.count,if address p m i=bank.base+e.val then delta p m i else 0)<2^W := by
    rw [old,eq]
    exact room
  exact (ProtocolRAMWeightedScatter.read_nat (address p m) (delta p m)
    (ProtocolRAM.image src (2*s.count) (RepairHistogram.pair p) m) (bank.base+e.val) bound).trans
    (congrArg₂ (·+·) (congrArg Fin.val old) eq)

/-- Mathematical quantity computed from the actual frozen history. All entry types
use the common physical edge ordinal and therefore contribute to one edge width. -/
def total (ss : List Slice) (m : Memory W) (e : Fin edges) := (ss.map (fun s => s.load m e)).sum

def applyAll (bank : Bank) (edges src : ℕ) : List Slice → Memory W → Memory W
  | [],m => m
  | s::ss,m => applyAll bank edges src ss (s.Out bank edges src m)

def scans (W edges src : ℕ) (bank : Bank) : List Slice → Procedure W
  | [] => scan W 0 0 (.lit 0)
  | s::ss => (code W src s.count (s.columns bank edges)).seq (scans W edges src bank ss)

def scanTime (edges : ℕ) (bank : Bank) (ss : List Slice) := 4+(ss.map (fun s=>ticks s.count (s.columns bank edges))).sum

def seed (bank : Bank) (edges : ℕ) : Pass := ⟨bank.base,edges,.lit 0⟩
def native (W edges src : ℕ) (bank : Bank) (ss : List Slice) : Procedure W :=
  ((seed bank edges).procedure W).seq (scans W edges src bank ss)
def output (bank : Bank) (edges src : ℕ) (ss : List Slice) (m : Memory W) :=
  applyAll bank edges src ss ((seed bank edges).apply m)
def clock (bank : Bank) (edges : ℕ) (ss : List Slice) := 4+6*edges+scanTime edges bank ss

def Mounted (bank : Bank) (edges src : ℕ) (ss : List Slice) (m : Memory W) :=
  ∀ s∈ss,s.Fits bank edges src W ∧ PairDirectory (s.columns bank edges) m s.count

theorem mounted_frame (bank : Bank) (edges src : ℕ) (ss : List Slice) (m u : Memory W)
    (ready : Mounted bank edges src ss m) (low : ∀x<bank.base,u x=m x) : Mounted bank edges src ss u := by
  intro s hs
  obtain ⟨h,dir⟩ := ready s hs
  have read (b : Bank) (safe : b.base+b.size≤bank.base) (r : Word W) : b.read u r=b.read m r := by
    have small := Nat.mod_lt r.val (Nat.two_pow_pos b.bits)
    change r.val%b.size<b.size at small
    exact low _ (by omega)
  exact ⟨h,⟨fun e=>(read s.parity h.parity _).trans (dir.first e),
    fun e=>(read s.parity h.parity _).trans_ne (dir.second e),fun e=>(read s.owner h.owner _).trans (dir.firstRow e),
    fun e=>(read s.owner h.owner _).trans (dir.secondRow e)⟩⟩

theorem total_frame (bank : Bank) (src : ℕ) (ss : List Slice) (m u : Memory W) (e : Fin edges)
    (fits : ∀s∈ss,s.Fits bank edges src W) (low : ∀x<bank.base,u x=m x) : total ss u e=total ss m e := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  apply Finset.sum_congr rfl
  intro i _
  simp only [eval_below _ _ m u (fits s hs).edge low,eval_below _ _ m u (fits s hs).amount low]

theorem scans_exec (bank : Bank) (src : ℕ) (ss : List Slice) (m : Memory W) (h : Mounted bank edges src ss m) :
    (scans W edges src bank ss).Exec m (applyAll bank edges src ss m) (scanTime edges bank ss) := by
  induction ss generalizing m with
  | nil =>
    have empty : image 0 0 (.lit 0) m=m := by funext x;simp [image,fillSegment]
    have executed : (scan W 0 0 (.lit 0)).Exec m (image 0 0 (.lit 0) m) 4 :=
      scan_exec 0 0 (.lit 0) m trivial (Nat.two_pow_pos W)
    rw [empty] at executed
    change (scan W 0 0 (.lit 0)).Exec m m 4
    intro P R K
    exact @executed P R K
  | cons s ss ih =>
    have head := h s List.mem_cons_self
    have later : Mounted bank edges src ss m := fun t ht=>h t (List.mem_cons_of_mem _ ht)
    have moved := mounted_frame bank edges src ss m _ later (s.frame bank edges src m head.1)
    have sum : scanTime edges bank (s::ss)=ticks s.count (s.columns bank edges)+scanTime edges bank ss := by
      simp [scanTime];omega
    rw [sum]
    change ((code W src s.count (s.columns bank edges)).seq (scans W edges src bank ss)).Exec m
      (applyAll bank edges src ss (s.Out bank edges src m)) (ticks s.count (s.columns bank edges)+scanTime edges bank ss)
    apply Procedure.Exec.then (b:=s.Out bank edges src m)
    · exact s.exec bank edges src m head.1 head.2
    · exact ih _ moved

theorem scans_frame (bank : Bank) (src : ℕ) (ss : List Slice) (m : Memory W) (x : ℕ)
    (fit : ∀s∈ss,s.Fits bank edges src W) (low : x<bank.base) : applyAll bank edges src ss m x=m x := by
  induction ss generalizing m with
  | nil => rfl
  | cons s ss ih =>
    exact (ih _ (fun t ht=>fit t (List.mem_cons_of_mem _ ht))).trans (s.frame bank edges src m (fit s List.mem_cons_self) x low)

theorem scans_read (bank : Bank) (src : ℕ) (ss : List Slice) (m : Memory W) (e : Fin edges)
    (fit : ∀s∈ss,s.Fits bank edges src W) (room : (m (bank.base+e.val)).val+total ss m e<2^W) :
    (applyAll bank edges src ss m (bank.base+e.val)).val=(m (bank.base+e.val)).val+total ss m e := by
  induction ss generalizing m with
  | nil => simp [applyAll,total]
  | cons s ss ih =>
    have h := fit s List.mem_cons_self
    have next : ∀t∈ss,t.Fits bank edges src W := fun t ht=>fit t (List.mem_cons_of_mem _ ht)
    have tail := total_frame bank src ss m (s.Out bank edges src m) e next (s.frame bank edges src m h)
    have split : total (s::ss) m e=s.load m e+total ss m e := by simp [total]
    rw [split] at room ⊢
    have first := s.read bank src m h e (by omega)
    change (applyAll bank edges src ss (s.Out bank edges src m) _).val=_
    rw [ih _ next (by rw [first,tail];omega),first,tail,Nat.add_assoc]

theorem exec (bank : Bank) (src : ℕ) (ss : List Slice) (m : Memory W) (room : bank.base+edges<2^W)
    (h : Mounted bank edges src ss m) : (native W edges src bank ss).Exec m (output bank edges src ss m) (clock bank edges ss) := by
  let z := (seed bank edges).apply m
  have start : ((seed bank edges).procedure W).Exec m z (4+6*edges) := by
    rw [show 4+6*edges=4+edges*(2*(Expr.lit 0).work+4) from by simp [Expr.work,Nat.mul_comm]]
    exact scan_exec bank.base edges (.lit 0) m trivial room
  apply Procedure.Exec.then start
  exact scans_exec bank src ss _ (mounted_frame bank edges src ss m z h
    (fun x hx=>ProtocolRAMGeneratedWrite.frame_image bank.base edges (.lit 0) m x (.inl hx)))

theorem read (bank : Bank) (src : ℕ) (ss : List Slice) (m : Memory W) (e : Fin edges)
    (fit : ∀s∈ss,s.Fits bank edges src W) (room : total ss m e<2^W) :
    (output bank edges src ss m (bank.base+e.val)).val=total ss m e := by
  let u := (seed bank edges).apply m
  have zero : u (bank.base+e.val)=0 := ProtocolRAMGeneratedWrite.read_image bank.base edges (.lit 0) m e
  have same := total_frame bank src ss m u e fit (fun x hx=>ProtocolRAMGeneratedWrite.frame_image bank.base edges (.lit 0) m x (.inl hx))
  have r := scans_read bank src ss u e fit (by simpa only [zero,Fin.val_zero,zero_add,same] using room)
  change (applyAll bank edges src ss u (bank.base+e.val)).val=total ss m e
  simpa only [zero,Fin.val_zero,zero_add,same] using r

theorem frame (bank : Bank) (edges src : ℕ) (ss : List Slice) (m : Memory W) (x : ℕ)
    (fit : ∀s∈ss,s.Fits bank edges src W) (low : x<bank.base) : output bank edges src ss m x=m x :=
  (scans_frame bank src ss _ x fit low).trans (ProtocolRAMGeneratedWrite.frame_image bank.base edges (.lit 0) m x (.inl low))

private theorem sparse_cheap (W src count : ℕ) (p : Columns) : CheapCode (code W src count p) :=
  @cheap_seq W (scan W src (2*count) (pair p)) (ProtocolRAMWeightedScatter.program W src count)
    (fun {_P _R _K} pc reg pub exit i=>scan_cheap W src (2*count) (pair p) pc reg pub exit i)
    (fun {_P _R _K} pc reg pub exit i=>ProtocolRAMWeightedScatter.cheap W src count pc reg pub exit i)

set_option maxHeartbeats 1600000 in
private theorem scans_cheap (W edges src : ℕ) (bank : Bank) (ss : List Slice) :
    CheapCode (scans W edges src bank ss) := by
  induction ss with
  | nil =>
    change CheapCode (scan W 0 0 (.lit 0))
    intro P R K pc reg pub exit i
    exact scan_cheap W 0 0 (.lit 0) pc reg pub exit i
  | cons s ss ih =>
    change CheapCode ((code W src s.count (s.columns bank edges)).seq (scans W edges src bank ss))
    exact @cheap_seq W (code W src s.count (s.columns bank edges)) (scans W edges src bank ss)
      (@sparse_cheap W src s.count (s.columns bank edges)) (@ih)

theorem cheap (W edges src : ℕ) (bank : Bank) (ss : List Slice) : CheapCode (native W edges src bank ss) :=
  @cheap_seq W ((seed bank edges).procedure W) (scans W edges src bank ss)
    (fun {_P _R _K} pc reg pub exit i=>scan_cheap W bank.base edges (.lit 0) pc reg pub exit i)
    (fun {_P _R _K} pc reg pub exit i=>scans_cheap W edges src bank ss pc reg pub exit i)

theorem clock_eq (bank : Bank) (edges : ℕ) (ss : List Slice) : clock bank edges ss =
    8+6*edges+(ss.map (fun s=>7+s.count*(4*(RepairHistogram.pair (s.columns bank edges)).work+20))).sum := by
  have per (s : Slice) : ticks s.count (s.columns bank edges)=7+s.count*(4*(RepairHistogram.pair (s.columns bank edges)).work+20) := by
    unfold ticks;ring
  simp only [clock,scanTime,per]
  omega

/-- Repeated uses of the same physical tree or core edge are counted from the
actual traversal positions. The amount is the true archived root word at each visit. -/
theorem walks_load {J : Type*} [Fintype J] (s : Slice) (m : Memory W) (e : Fin edges)
    (walk : J→List (Fin edges)) (bits : J→ℕ) (enum : Fin s.count≃(Σ j, Fin (walk j).length))
    (index : ∀ i, (s.edge.eval m (i.val:Word W)).val=((walk (enum i).1)[(enum i).2.val]'(enum i).2.isLt).val)
    (amount : ∀ i, (s.amount.eval m (i.val:Word W)).val=bits (enum i).1) :
    s.load m e=AdaptiveProbe.routeLoad walk bits e := by
  unfold Slice.load
  simp only [index,amount,Fin.val_inj]
  rw [enum.sum_comp (fun o=>if (walk o.1)[o.2.val]'o.2.isLt=e then bits o.1 else 0),Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun j _=>AdaptiveProbe.sum_positions_eq_count (walk j) e (bits j))

/-- Charge the installed physical edges at the same prices as their source
occurrences, even when many occurrences have the same common edge identifier. -/
theorem slice_toll (s : Slice) (m : Memory W) (physical : Fin s.count→Fin edges) (len : Fin edges→ℝ)
    (read : ∀ i,(s.edge.eval m (i.val:Word W)).val=(physical i).val) :
    (∑ e : Fin edges,(s.load m e:ℝ)*len e)=∑ i : Fin s.count,((s.amount.eval m (i.val:Word W)).val:ℝ)*len (physical i) := by
  simp only [Slice.load,read,Fin.val_inj,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

def Slice.toll (s : Slice) (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) :=
  ∑ e : Fin edges,len e*((s.load m e:ℝ)/payload)

theorem total_toll (ss : List Slice) (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) :
    (∑ e : Fin edges,len e*((total ss m e:ℝ)/payload))=(ss.map (fun s=>s.toll m len payload)).sum := by
  induction ss with
  | nil => simp [total]
  | cons s ss ih =>
    have add (e : Fin edges) : total (s::ss) m e=s.load m e+total ss m e := by simp [total]
    simp only [add,Nat.cast_add,add_div,mul_add,Finset.sum_add_distrib,ih,List.map_cons,List.sum_cons,Slice.toll]

theorem physical_toll (s : Slice) (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) (physical : Fin s.count→Fin edges)
    (read : ∀ i,(s.edge.eval m (i.val:Word W)).val=(physical i).val) :
    s.toll m len payload=(∑ i : Fin s.count,((s.amount.eval m (i.val:Word W)).val:ℝ)*len (physical i))/payload := by
  rw [←slice_toll s m physical len read,Finset.sum_div]
  exact Finset.sum_congr rfl (fun e _=>by ring)

/-- Zero and dummy receipts have no pricing requirement. Every positive receipt
must name its actual original physical edge and its true native unit price. -/
theorem visible_toll (s : Slice) (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) (price : Fin s.count→ℝ)
    (hit : ∀ i,(s.amount.eval m (i.val:Word W)).val≠0 →
      ∃ e : Fin edges,(s.edge.eval m (i.val:Word W)).val=e.val ∧ len e=price i) :
    s.toll m len payload=(∑ i : Fin s.count,((s.amount.eval m (i.val:Word W)).val:ℝ)*price i)/payload := by
  have raw : (∑ e : Fin edges,(s.load m e:ℝ)*len e) = ∑ i : Fin s.count,((s.amount.eval m (i.val:Word W)).val:ℝ)*price i := by
    simp only [Slice.load,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero,Finset.sum_mul,ite_mul,zero_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    by_cases off : (s.amount.eval m (i.val:Word W)).val=0
    · simp [off]
    · obtain ⟨e,which,rate⟩ := hit i off
      simp [which,Fin.val_inj,rate]
  rw [←raw,Finset.sum_div]
  exact Finset.sum_congr rfl (fun e _=>by ring)

theorem walks_toll {J : Type*} [Fintype J] (s : Slice) (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ)
    (walk : J→List (Fin edges)) (bits : J→ℕ) (enum : Fin s.count≃(Σ j, Fin (walk j).length))
    (index : ∀ i, (s.edge.eval m (i.val:Word W)).val=((walk (enum i).1)[(enum i).2.val]'(enum i).2.isLt).val)
    (amount : ∀ i, (s.amount.eval m (i.val:Word W)).val=bits (enum i).1) :
    s.toll m len payload=∑ j : J,((walk j).map len).sum*((bits j:ℝ)/payload) := by
  unfold Slice.toll
  simp only [walks_load s m _ walk bits enum index amount]
  exact AdaptiveProbe.stock_route_bill len walk bits payload

end Hierarchy.ProtocolRAM.PaidWidths

end
end OAI
