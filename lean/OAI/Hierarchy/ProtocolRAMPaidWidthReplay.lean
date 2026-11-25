import OAI.Hierarchy.ProtocolRAMCalendarPrefixLayout
import OAI.Hierarchy.ProtocolRAMPaidWidthPrefixFrame

namespace OAI
/-! # Sequential native replay of cumulative widths into protected per-date banks -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixWidths
open Computability.VPVNP.BurstRAM PrivateRAM PaidWidths
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators



variable {edges W : ℕ} (L : Layout edges) (rows : ℕ→List Slice)

/-- Dates range from zero through the final date, so the initial zero vector has
a real initialized bank. Every stage is the existing sparse native paid-width routine. -/
def program (W : ℕ) : ℕ→Procedure W
  | 0 => PaidWidths.native W edges L.scratch (L.bank 0) (rows 0)
  | j+1 => (program W j).seq (PaidWidths.native W edges L.scratch (L.bank (j+1)) (rows (j+1)))

def image (m : Memory W) : ℕ→Memory W
  | 0 => PaidWidths.output (L.bank 0) edges L.scratch (rows 0) m
  | j+1 => PaidWidths.output (L.bank (j+1)) edges L.scratch (rows (j+1)) (image m j)

def time : ℕ→ℕ
  | 0 => PaidWidths.clock (L.bank 0) edges (rows 0)
  | j+1 => time j+PaidWidths.clock (L.bank (j+1)) edges (rows (j+1))

set_option maxHeartbeats 1600000 in
theorem cheap (n : ℕ) : CheapCode (program L rows W n) := by
  induction n with
  | zero => exact @PaidWidths.cheap W edges L.scratch (L.bank 0) (rows 0)
  | succ n ih =>
    exact @cheap_seq W (program L rows W n)
      (PaidWidths.native W edges L.scratch (L.bank (n+1)) (rows (n+1))) (@ih)
      (@PaidWidths.cheap W edges L.scratch (L.bank (n+1)) (rows (n+1)))

theorem time_le (n c : ℕ) (cap : ∀ j≤n,PaidWidths.clock (L.bank j) edges (rows j)≤c) :
    time L rows n≤(n+1)*c := by
  induction n with
  | zero => simpa [time] using cap 0 le_rfl
  | succ n ih =>
    have old := ih (fun j h=>cap j (Nat.le_succ_of_le h))
    simpa only [time,Nat.succ_mul] using Nat.add_le_add old (cap (n+1) le_rfl)

/-- Native input bounds and the frozen archive are certified on the initial memory.
No hypothesis mentions the state obtained by executing an earlier prefix. -/
structure Ready (archiveMemory : Memory W) (last : ℕ) : Prop where
  extent : ∀ j≤last,(L.bank j).base+edges<2^W
  mounted : ∀ j≤last,PaidWidths.Mounted (L.bank j) edges L.scratch (rows j) archiveMemory
  immutable : ∀ j≤last,∀ s∈rows j,Archived W L.archive s
  fits : ∀ j≤last,∀ e : Fin edges,PaidWidths.total (rows j) archiveMemory e<2^W

structure Receipt (m : Memory W) (j : ℕ) : Prop where
  ran : (program L rows W j).Exec m (image L rows m j) (time L rows j)
  kept : ∀ a<L.archive,image L rows m j a=m a
  read : ∀ i≤j,∀ e : Fin edges,(image L rows m j ((L.bank i).base+e.val)).val=
    PaidWidths.total (rows i) m e

private theorem one (m u : Memory W) {last : ℕ} (valid : Ready L rows m last) (j : ℕ) (hj : j≤last)
    (same : ∀ a<L.archive,u a=m a) :
    let bank := L.bank j
    let out := PaidWidths.output bank edges L.scratch (rows j) u
    (PaidWidths.native W edges L.scratch bank (rows j)).Exec u out (PaidWidths.clock bank edges (rows j)) ∧
    (∀ a<bank.base,out a=u a) ∧ ∀ e : Fin edges,(out (bank.base+e.val)).val=PaidWidths.total (rows j) m e := by
  intro bank out
  have mounted := mounted_of_archive bank edges L.scratch L.archive (rows j) m u
    (valid.immutable j hj) (valid.mounted j hj) same
  have stable (e : Fin edges) := total_of_archive L.archive (rows j) m u e (valid.immutable j hj) same
  refine ⟨PaidWidths.exec bank L.scratch (rows j) u (valid.extent j hj) mounted,
    fun a h=>PaidWidths.frame bank edges L.scratch (rows j) u a (fun s hs=>(mounted s hs).1) h,?_⟩
  intro e
  exact (PaidWidths.read bank L.scratch (rows j) u e (fun s hs=>(mounted s hs).1)
    ((stable e).trans_lt (valid.fits j hj e))).trans (stable e)

theorem replay (m : Memory W) (last : ℕ) (valid : Ready L rows m last) : Receipt L rows m last := by
  have atDate (j : ℕ) (hj : j≤last) : Receipt L rows m j := by
    induction j with
    | zero =>
      obtain ⟨ran,kept,read⟩ := one L rows m m valid 0 hj (fun _ _=>rfl)
      refine ⟨ran,fun a ha=>kept a (ha.trans_le (L.archive_le 0)),?_⟩
      intro i hi e
      have eq : i=0 := by omega
      subst i
      exact read e
    | succ j ih =>
      have prev := ih (Nat.le_trans (Nat.le_succ j) hj)
      obtain ⟨ran,kept,read⟩ := one L rows m (image L rows m j) valid (j+1) hj prev.kept
      refine ⟨Procedure.Exec.then prev.ran ran,fun a ha=>(kept a (ha.trans_le (L.archive_le _))).trans (prev.kept a ha),?_⟩
      intro i hi e
      rcases Nat.eq_or_lt_of_le hi with eq | lt
      · subst i
        exact read e
      · have early := L.before lt
        have pos := e.isLt
        exact (congrArg Fin.val (kept ((L.bank i).base+e.val) (by omega))).trans
          (prev.read i (by omega) e)
  exact atDate last le_rfl

end Hierarchy.ProtocolRAM.Calendar.PrefixWidths

end
end OAI
