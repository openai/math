import OAI.Hierarchy.ProtocolRAMCalendarStripTrees

namespace OAI
/-! # Exact space and native word bounds for both real tree traversal pages -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CatalogueRows PurchaseFrozen
open StockCommit
open scoped Classical
variable {z W k q depth : ℕ}
local notation "N" => Stages z (2^W)
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def treeRowsFactor (d k degree depth : ℕ) := ((2*rounds d+1)*(2*k))*degree^depth

def treePageFactor (c : Mesh) (rows n k : ℕ) :=
  (events c).length*(12*(rows*(n+(n+1)*(k*2)))+8)

def treePagesFactor (c : Mesh) (d k degree depth : ℕ) :=
  treePageFactor c (treeRowsFactor d k degree depth) (PayloadStrip.edgeCount (2*rounds d+1)) k+
  treePageFactor c (treeRowsFactor d k degree depth) (ChainStrip.edgeCount depth) k

theorem treeRows_eq (a : Attempt) :
    treeRows s c b G F a=treeRowsFactor (2^W) k s.sampler.degree depth*2^z := by
  have native : treeRows s c b G F a=PurchaseFrozen.count z (2^W) k*paths z s.sampler.degree depth := by
    cases a <;> rfl
  rw [native,PurchaseFrozen.count_eq]
  unfold treeRowsFactor PurchaseFrozen.paths
  ac_rfl

theorem treePage_rows_le (base n : ℕ) :
    (treePage s c b G F base n).maxRows≤treeRowsFactor (2^W) k s.sampler.degree depth*2^z := by
  change Finset.univ.sup (treePage s c b G F base n).rows ≤ _
  apply Finset.sup_le
  intro i _
  change (match (events c)[i] with | .attempt a=>treeRows s c b G F a | .feed _=>0)≤_
  split
  · exact (treeRows_eq s c b G F _).le
  · exact Nat.zero_le _

/-- Rounded banks have exact row counts even if the calendar is empty or
contains only feed operations. -/
theorem treePage_maxRows (base n : ℕ) :
    (treePage s c b G F base n).maxRows=
      if ∃ a,Event.attempt a∈events c then treeRowsFactor (2^W) k s.sampler.degree depth*2^z else 0 := by
  classical
  let page := treePage s c b G F base n
  split_ifs with hit
  · apply Nat.le_antisymm (treePage_rows_le s c b G F base n)
    obtain ⟨a,scheduled⟩ := hit
    let i : Fin (events c).length := ⟨(events c).idxOf (.attempt a),List.idxOf_lt_length_of_mem scheduled⟩
    have h : (events c)[i]=.attempt a := List.getElem_idxOf i.isLt
    have per : page.rows i=treeRows s c b G F a := by
      change (match (events c)[i] with | .attempt a=>treeRows s c b G F a | .feed _=>0)=_
      rw [h]
    exact (treeRows_eq s c b G F a).symm.le.trans (per.symm.le.trans (page.bounded i))
  · apply Nat.eq_zero_of_le_zero
    change Finset.univ.sup page.rows ≤ 0
    apply Finset.sup_le
    intro i _
    change (match (events c)[i] with | .attempt a=>treeRows s c b G F a | .feed _=>0)≤0
    cases he : (events c)[i] with
    | attempt a =>
      have member : (events c)[i] ∈ events c := List.getElem_mem (l:=events c) i.isLt
      rw [he] at member
      exact False.elim (hit ⟨a,member⟩)
    | feed _ => exact le_rfl

/-- Additive endpoint measured in physical words, including the address padding
of every row/port pair. -/
theorem treePage_exact (base n : ℕ) :
    (treePage s c b G F base n).stop =
      base+(events c).length*(12*((if ∃ a,Event.attempt a∈events c then
        treeRowsFactor (2^W) k s.sampler.degree depth*2^z else 0)*(n+(n+1)*(k*2)))+8) := by
  change base+(events c).length*(12*((treePage s c b G F base n).maxRows*Fintype.card (Strip.TreeLink n k))+8)=_
  rw [treePage_maxRows,Strip.tree_card]

/-- The common allocator pays the two eight-word row-layout pads, even when
no actual attempt occurs; all other space is indexed by a real row and link. -/
theorem treePages_exact (base : ℕ) :
    let rows := if ∃ a,Event.attempt a∈events c then
      treeRowsFactor (2^W) k s.sampler.degree depth*2^z else 0
    let links := fun n : ℕ=>n+(n+1)*(k*2)
    (boughtPage s c b G F base).stop = base+(events c).length*
      (12*(rows*(links (PayloadStrip.edgeCount N)+links (ChainStrip.edgeCount depth)))+16) := by
  dsimp only []
  simp only [boughtPage,payloadPage,treePage_exact]
  ring

theorem treePage_bound (base n : ℕ) :
    (treePage s c b G F base n).stop≤
      base+treePageFactor c (treeRowsFactor (2^W) k s.sampler.degree depth) n k*2^z := by
  have bound := (treePage s c b G F base n).linear z _ (treePage_rows_le s c b G F base n)
  change _≤base+((events c).length*(12*(treeRowsFactor (2^W) k s.sampler.degree depth*
    Fintype.card (Strip.TreeLink n k))+8))*2^z at bound
  simpa only [treePageFactor,Strip.tree_card] using bound

theorem treePages_bound (base : ℕ) :
    (boughtPage s c b G F base).stop≤base+treePagesFactor c (2^W) k s.sampler.degree depth*2^z := by
  let phase := treeRowsFactor (2^W) k s.sampler.degree depth
  let p := payloadPage s c b G F base
  have payload := treePage_bound s c b G F base (PayloadStrip.edgeCount N)
  have bought := treePage_bound s c b G F p.stop (ChainStrip.edgeCount depth)
  have stages : N=2*rounds (2^W)+1 := template_length ..
  change p.stop≤base+treePageFactor c phase (PayloadStrip.edgeCount N) k*2^z at payload
  change (boughtPage s c b G F base).stop≤p.stop+treePageFactor c phase (ChainStrip.edgeCount depth) k*2^z at bought
  have fixed : treePageFactor c phase (PayloadStrip.edgeCount N) k =
      treePageFactor c phase (PayloadStrip.edgeCount (2*rounds (2^W)+1)) k :=
    congrArg (fun length=>treePageFactor c phase (PayloadStrip.edgeCount length) k) stages
  rw [fixed] at payload
  unfold treePagesFactor
  rw [Nat.add_mul]
  exact bought.trans (by dsimp only [phase] at payload ⊢;omega)

theorem treePages_word_room (base startFactor : ℕ)
    (start : base≤heapEnd z (2^W) copies+startFactor*2^z)
    (large : startFactor+treePagesFactor c (2^W) k s.sampler.degree depth+1≤2^z) :
    (boughtPage s c b G F base).stop<2^wordBits z (2^W) copies := by
  apply (treePages_bound s c b G F base).trans_lt
  apply lt_of_le_of_lt _ (append_room large)
  rw [Nat.add_mul]
  omega

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
