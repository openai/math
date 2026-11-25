import OAI.Hierarchy.TraceReceiverGridWindow
import OAI.Hierarchy.TraceReceiverRootBounds

namespace OAI
/-! # Forward control and fixed input banks of the selected terminal root loop -/
noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal RAM
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan HistoryContraction
open RAM.TickTerminalRoot RAM.HistoryTerminalTape
open scoped Classical Fin.CommRing BigOperators

variable {w u p suffix wire n : ℕ}

def extent (f : Fin n → ℕ) (i : ℕ) := if hi : i<n then f ⟨i,hi⟩ else 0

def scanned (f : Fin n → ℕ) (i : ℕ) := ∑ k ∈ Finset.range i,extent f k

theorem scanned_at (f : Fin n → ℕ) (i : Fin n) : scanned f i.val=Tree.before f i := by
  unfold scanned Tree.before
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [extent,dite_eq_left (j.isLt.trans i.isLt)]
  rfl

theorem scanned_end (f : Fin n → ℕ) : scanned f n=∑ i,f i := by
  unfold scanned
  rw [←Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun j _=>by simp [extent,j.isLt])

theorem scanned_le (f : Fin n → ℕ) {i : ℕ} (hi : i≤n) : scanned f i≤∑ j,f j := by
  rw [←scanned_end f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (by intros;omega)

/-- The parent pointer and the five-word selected tasks are also read after
their native preparation, outside all S14 and destination-map writes. -/
def Stable (u B tasks n a : ℕ) : Prop :=
  ((TickWorkspace.base u 10≤a ∧ a<TickWorkspace.base u 14) ∨
    (TickWorkspace.base u 17≤a ∧ a<TickWorkspace.base u 18) ∨
    (TickWorkspace.base u 18+5≤a ∧ a<B+16)) ∨
  (B+16≤a ∧ a<B+20) ∨ (tasks≤a ∧ a<tasks+5*n)

def Reached (u B tasks n : ℕ) (start live : Memory (64*w)) : Prop :=
  ∀ a,Stable u B tasks n a → live a=start a

structure Controls (u n : ℕ) (rows bits : Fin n → ℕ) (i : ℕ) (m : Memory (64*w)) : Prop where
  ordinal : (m (TickWorkspace.base u 18)).val=i
  count : (m (TickWorkspace.base u 18+1)).val=n
  rowsRead : (m (TickWorkspace.base u 18+2)).val=scanned rows i
  bitsRead : (m (TickWorkspace.base u 18+3)).val=scanned bits i

private theorem region {a : ℕ} (large : 7≤w) (age : u^10≤5*w) (ns : 5*n≤GridReceiverBanks.gap w)
    (room : Stable u (GridReceiverBanks.base w) (GridReceiverBanks.tasks w).tasks n a) :
    a≠TickWorkspace.base u 18+4 ∧
    (a<GridReceiverBanks.mapHeader w ∨ GridReceiverBanks.mapHeader w+3≤a) ∧
    a<(GridReceiverBanks.tasks w).maps ∧
    ((TickWorkspace.base u 10≤a ∧ a<TickWorkspace.base u 14) ∨
      (TickWorkspace.base u 17≤a ∧ a<TickWorkspace.base u 18) ∨ TickWorkspace.base u 18+4≤a) := by
  obtain ⟨bank,roof,slots⟩ := TraceFactorReceiver.Gather.grid_window large age
  have low := TickWorkspace.apart (u:=u) (by decide : 14<18)
  have high := TickWorkspace.apart (u:=u) (by decide : 18<45)
  change (( _ ∨ _ ∨ _) ∨ _ ∨
      (GridReceiverBanks.base w+GridReceiverBanks.gap w≤a ∧ a<GridReceiverBanks.base w+GridReceiverBanks.gap w+5*n)) at room
  change a≠TickWorkspace.base u 18+4 ∧
    (a<GridReceiverBanks.base w+24 ∨ GridReceiverBanks.base w+24+3≤a) ∧
    a<GridReceiverBanks.base w+2*GridReceiverBanks.gap w ∧ _
  rcases room with (h|h|h)|h|h <;> omega

private theorem seeded_eq {w u p start prefixBase hdrTab head a : ℕ} (m : Memory (64*w))
    (cf : TickWorkspace.base u 18+4 < 2^(64*w))
    (ctrl : a≠TickWorkspace.base u 18+4) (off : a<head ∨ head+3≤a) :
    TraceReceiverTasks.mapSeed (mounted u p start prefixBase) hdrTab head m a=m a := by
  have cur : (countdown (W:=64*w) (mounted u p start prefixBase)).val=TickWorkspace.base u 18+4 :=
    Fin.val_cast_of_lt cf
  have neg : ¬(head≤a ∧ a<head+3) := by omega
  simp only [TraceReceiverTasks.mapSeed,TraceReceiverMapSave.seedImage,fillSegment,ite_eq_right neg,decrease,writeMemory,
    cur,ite_eq_right ctrl]

/-- The countdown write and the three-word copy header cannot change
a single input used by the native selected-root dispatcher. -/
theorem seeded_frame (large : 7≤w) (age : u^10≤5*w) (jobs : 5*n≤GridReceiverBanks.gap w)
    (m : Memory (64*w)) :
    let D:=GridReceiverBanks.tasks w
    Reached u (GridReceiverBanks.base w) D.tasks n m
      (TraceReceiverTasks.mapSeed (mounted u p (2+suffix) wire) D.tasks (GridReceiverBanks.mapHeader w) m) := by
  intro D a ha
  obtain ⟨ctrl,off,_,_⟩ := region large age jobs ha
  have high := TickWorkspace.apart (u:=u) (by decide : 18<45)
  obtain ⟨bank,roof,space⟩ := TraceFactorReceiver.Gather.grid_window large age
  exact seeded_eq m (by omega) ctrl off

/-- All four arithmetic control words stay at their pre-root values until
the actual terminal routine updates them at the end of the iteration. -/
theorem seeded_control (large : 7≤w) (age : u^10≤5*w) (m : Memory (64*w)) (j : Fin 4) :
    let A:=mounted u p (2+suffix) wire
    TraceReceiverTasks.mapSeed A (GridReceiverBanks.tasks w).tasks (GridReceiverBanks.mapHeader w) m (A.control+j.val)
      =m (A.control+j.val) := by
  intro A
  have high := TickWorkspace.apart (u:=u) (by decide : 18<45)
  obtain ⟨bank,roof,space⟩ := TraceFactorReceiver.Gather.grid_window large age
  have h:=j.isLt
  apply seeded_eq m (by omega)
  · change TickWorkspace.base u 18+j.val≠_;omega
  · apply Or.inl
    change TickWorkspace.base u 18+j.val<GridReceiverBanks.base w+24
    omega

/-- S12/S13, S17, the retained original directory and heap, the compact parent
and the entire task table survive every output write of this real root. -/
theorem step_frame (large : 7≤w) (age : u^10≤5*w) (jobs : 5*n≤GridReceiverBanks.gap w)
    (dst len : ℕ) (dstHigh : (GridReceiverBanks.tasks w).maps≤dst) (m : Memory (64*w))
    (page : TickWorkspace.base u 18+TickWorkspace.stride u<2^(64*w))
    (compact : CompactRootAt u p (2+suffix) wire (TraceReceiverTasks.mapSeed (mounted u p (2+suffix) wire)
      (GridReceiverBanks.tasks w).tasks (GridReceiverBanks.mapHeader w) m)) :
    let D:=GridReceiverBanks.tasks w
    Reached u (GridReceiverBanks.base w) D.tasks n m
      (TraceReceiverTasks.mapStep (mounted u p (2+suffix) wire) D.tasks (GridReceiverBanks.mapHeader w) dst len m) := by
  intro D a ha
  let A:=mounted u p (2+suffix) wire
  let z:=TraceReceiverTasks.mapSeed A D.tasks (GridReceiverBanks.mapHeader w) m
  obtain ⟨hc,hs,hm,band⟩ := region large age jobs ha
  have kept : TraceReceiverTasks.KeptByRoot A z a := by
    rcases band with h|h|h
    · exact TraceReceiverRootBounds.kept_archive compact page a (Or.inl h)
    · exact TraceReceiverRootBounds.kept_archive compact page a (Or.inr h)
    · exact TraceReceiverRootBounds.kept_high compact page a h
  have cf := compact.space
  have cur : (countdown (W:=64*w) A).val=TickWorkspace.base u 18+4 :=
    Fin.val_cast_of_lt (by change TickWorkspace.base u 18+4 < 2^(64*w); omega)
  rw [TraceReceiverTasks.mapStep_frame A D.tasks _ dst len a m hs (Or.inl (hm.trans_le dstHigh)) kept]
  simp only [decrease,writeMemory,cur,ite_eq_right hc]

/-- The four canonical control outputs of one physical terminal, before
casting them back to the native word width. -/
private theorem seed_fields (A : Arena) (raw : ℕ→ℕ) (j : Fin 4) :
    seedWords A raw (Fin.natAdd 22 j) =
    (![raw A.control+1,raw (A.control+1),
      raw (A.control+2)+(HistoryStageRoot.atResult raw (A.results+8*rootId A raw)).rows,
      raw (A.control+3)+(HistoryStageRoot.atResult raw (A.results+8*rootId A raw)).bits] : Fin 4→ℕ) j := by
  change Fin.append _ _ (Fin.natAdd 22 j)=_
  exact Fin.append_right _ _ j

theorem controls_step {n : ℕ} (rows bits : Fin n → ℕ) (i : Fin n) (len dst : ℕ)
    (large : 7≤w) (age : u^10≤5*w) (m : Memory (64*w))
    (state : Controls u n rows bits i.val m) (count : n<2^(64*w))
    (rowFit : (∑ j,rows j)<2^(64*w)) (bitFit : (∑ j,bits j)<2^(64*w))
    (page : TickWorkspace.base u 18+TickWorkspace.stride u<2^(64*w))
    (above : TickWorkspace.base u 18+4≤dst)
    (compact : CompactRootAt u p (2+suffix) wire (TraceReceiverTasks.mapSeed (mounted u p (2+suffix) wire)
      (GridReceiverBanks.tasks w).tasks (GridReceiverBanks.mapHeader w) m))
    (fields : let A:=mounted u p (2+suffix) wire
      let raw:=natMemory (TraceReceiverTasks.mapSeed A (GridReceiverBanks.tasks w).tasks (GridReceiverBanks.mapHeader w) m)
      let z:=HistoryStageRoot.atResult raw (A.results+8*rootId A raw)
      z.rows=rows i ∧ z.bits=bits i) :
    Controls u n rows bits (i.val+1)
      (TraceReceiverTasks.mapStep (mounted u p (2+suffix) wire) (GridReceiverBanks.tasks w).tasks
        (GridReceiverBanks.mapHeader w) dst len m) := by
  let A:=mounted u p (2+suffix) wire
  let D:=GridReceiverBanks.tasks w
  let hdr:=GridReceiverBanks.mapHeader w
  let b:=TraceReceiverTasks.mapSeed A D.tasks hdr m
  let raw:=natMemory b
  let z:=HistoryStageRoot.atResult raw (A.results+8*rootId A raw)
  let step:=TraceReceiverTasks.mapStep A D.tasks hdr dst len m
  have hc (j : Fin 4) : b (A.control+j.val)=m (A.control+j.val) := seeded_control large age m j
  have h0 : raw A.control=i.val := (congrArg Fin.val (hc 0)).trans state.ordinal
  have h1 : raw (A.control+1)=n := (congrArg Fin.val (hc 1)).trans state.count
  have h2 : raw (A.control+2)=scanned rows i.val := (congrArg Fin.val (hc 2)).trans state.rowsRead
  have h3 : raw (A.control+3)=scanned bits i.val := (congrArg Fin.val (hc 3)).trans state.bitsRead
  have data : z.rows=rows i ∧ z.bits=bits i := fields
  have reads (j : Fin 4) : step (A.control+j.val) =
      ((![raw A.control+1,raw (A.control+1),raw (A.control+2)+z.rows,raw (A.control+3)+z.bits]
        : Fin 4→ℕ) j : Word (64*w)) :=
    (TraceReceiverRootBounds.map_controls D.tasks hdr dst len m compact page above j).trans
      (congrArg (fun a : ℕ=>(a:Word (64*w))) (seed_fields A raw j))
  have next (f : Fin n → ℕ) : scanned f (i.val+1)=scanned f i.val+f i := by
    simp only [scanned,Finset.sum_range_succ,extent,dite_eq_left i.isLt]
  have iroom := i.isLt
  have rr := (scanned_le rows (show i.val+1≤n by omega)).trans_lt rowFit
  have br := (scanned_le bits (show i.val+1≤n by omega)).trans_lt bitFit
  constructor
  · have e : step A.control=((raw A.control+1:ℕ):Word (64*w)) := reads 0
    rw [h0] at e
    exact (congrArg Fin.val e).trans (Fin.val_cast_of_lt (by omega))
  · have e : step (A.control+1)=(raw (A.control+1):Word (64*w)) := reads 1
    rw [h1] at e
    exact (congrArg Fin.val e).trans (Fin.val_cast_of_lt count)
  · have e : step (A.control+2)=((raw (A.control+2)+z.rows:ℕ):Word (64*w)) := reads 2
    rw [h2,data.1,←next rows] at e
    exact (congrArg Fin.val e).trans (Fin.val_cast_of_lt rr)
  · have e : step (A.control+3)=((raw (A.control+3)+z.bits:ℕ):Word (64*w)) := reads 3
    rw [h3,data.2,←next bits] at e
    exact (congrArg Fin.val e).trans (Fin.val_cast_of_lt br)

end Hierarchy.TraceReceiverForward

end

end OAI
