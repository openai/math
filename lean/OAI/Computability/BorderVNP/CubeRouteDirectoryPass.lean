import OAI.Computability.BorderVNP.CubeRouteDataFields
import OAI.Computability.BorderVNP.CubeTeamOwnedPublicPrefix
import OAI.Computability.BorderVNP.CubeISALocalRowGroupLayout
import OAI.Computability.BorderVNP.CubeRouteScheduledWriters

/-! # Native assignment of each receiving cell followed by the complete label-pair directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube VPVNP.BurstRAM LocalRow

variable (ar : Layout) (frame controls : ℕ) (axis : Fin (ar.n+1)) (R : ℕ)
local notation "banks" => ar.cellWriter frame controls axis
local notation "pairs" => ar.pairWriter frame
local notation "wl" => LocalRow.weightLayout ar frame axis.val
local notation "tl" => LocalRow.teamLayout ar R

/-- Select the first least-loaded physical team for the grouping digit of this cell's real label. -/
def Layout.receivingOwner (input : ℕ → ℕ) (c : ℕ) : Fin (R+1) :=
  TeamNative.owner R ((wl).weight input) ((wl).symbol input c)

/-- The postcondition of the two native directory stages, with all raw demand and pin words retained. -/
structure DirectoryImage (input scheduled after : ℕ → ℕ) : Prop where
  /-- The three-word label-pair directory, including all of its outside words. -/
  pairRows : PairDirectory.Image pairs ((banks).written scheduled (banks).cells) (pairs).count after
  /-- The physical owner and bank address for every placed cell. -/
  hostRows : ∀ c < ar.cells, after (ar.hostDirectory+c*2) = (ar.receivingOwner frame axis R input c).val ∧
    after (ar.hostDirectory+c*2+1) = ar.cellBank+c*ar.cellStride
  /-- All words below the secondary header remain as they were at the grouping exit. -/
  beforeHeader : ∀ j < ar.header.header, after j=scheduled j

private theorem Layout.pair_fields_after_cells (m : ℕ → ℕ)
    (old : (pairs).Fields m) (low : frame+112 ≤ ar.header.header) : (pairs).Fields ((banks).written m (banks).cells) := by
  obtain ⟨head,lab,grp,own,pair,host,rec,stop⟩ := ar.writer_order
  have earlier (j : ℕ) (h : j < ar.hostDirectory) :=
    (banks).written_outside m (banks).cells j (Or.inl h)
  constructor <;> first | exact (earlier _ (by change frame+56 < _; omega)).trans old.alphabet |
    exact (earlier _ (by change frame+59 < _; omega)).trans old.symbols |
    exact (earlier _ (by change frame+60 < _; omega)).trans old.axes |
    exact (earlier _ (by change frame+63 < _; omega)).trans old.header |
    exact (earlier _ (by change ar.header.header+7 < _; omega)).trans old.blocks |
    exact (earlier _ (by change frame+91 < _; omega)).trans old.table

/-- The group assignment's stored owners and actual chosen label words determine every receiving-team lookup. -/
theorem Layout.receivingOwner_eq (input scheduled : ℕ → ℕ)
    (res : GroupWeights.ScheduleResult wl tl input scheduled) (pos : 0 < ar.header.d)
    (c : ℕ) (hc : c < ar.cells) : (banks).owner scheduled c = (ar.receivingOwner frame axis R input c).val := by
  obtain ⟨_,lab,grp,_,_,_,_,_⟩ := ar.writer_order
  have ts : ar.groupWeights ≤ ar.teamTotals := Nat.le_add_right ..
  have keep := res.other (ar.publicBase+c)
    (fun _ _ => by change _ ≠ ar.groupWeights+_; omega)
    (fun _ => by change _ ≠ ar.teamTotals+_; omega)
    (fun _ _ => by change _ ≠ ar.ownerBase+_; omega)
  change scheduled (ar.ownerBase+(scheduled (ar.publicBase+c)/ar.header.d^axis.val)%ar.header.d) = _
  rw [keep]
  exact res.owners ((wl).symbol input c) (Nat.mod_lt _ pos)

/-- A true run of the cell-bank installer and the pair writer. Its cost is linear in the
number of cells plus the number of ordered label pairs times their dimension. -/
theorem Layout.directoryPass_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (input : ℕ → ℕ) (res : GroupWeights.ScheduleResult wl tl input (readings m))
    (base : (pub 0).val = frame) (cf : (banks).Fields (readings m)) (pf : (pairs).Fields (readings m))
    (two : 2 ≤ ar.header.d) (bank : 0 < Cube.Tally.bankWidth ar.n ar.b ar.h ar.K ar.s)
    (low : frame+112 ≤ ar.header.header) (ctl : controls+10 < ar.header.header) (room : ar.stop < 2^w) :
    BoundedRun pub mac (.seq CellBanks.install PairDirectory.directory) s m
      ((CellBanks.setup.slots+ar.cells*15+1)+(30+(pairs).count*(24+27*(ar.n+1))))
      (fun z => DirectoryImage ar frame controls axis R input (readings m) z.mem) := by
  have pos : 0 < ar.header.d := by omega
  have pairFit := ar.pairWriter_fits frame two bank low room
  have first := CellBanks.install_run pub mac banks s m base cf (ar.cellWriter_fits frame controls axis pos low ctl room)
  apply first.seq
  intro t mt hm
  change readings mt = (banks).written (readings m) (banks).cells at hm
  have fs := ar.pair_fields_after_cells frame controls axis (readings m) pf low
  rw [← hm] at fs
  obtain ⟨es,u,mu,run,_,_⟩ := PairDirectory.run_directory pub mac pairs t mt pairFit base fs
  obtain ⟨cost,im⟩ := PairDirectory.directory_image_of_run pub mac pairs pairFit base fs run
  have image := im.image
  change PairDirectory.Image pairs (readings mt) (pairs).count (readings mu) at image
  rw [hm] at image
  refine ⟨es,u,mu,run,cost,image,?_,?_⟩
  · intro c hc
    have h := (banks).written_at (readings m) (i:=(banks).cells) (c:=c) hc
    have start : (pairs).table+3*(pairs).count = ar.hostDirectory := by
      change ar.pairDirectory+3*(ar.alphabet*ar.alphabet) = ar.pairDirectory+3*ar.alphabet^2
      rw [pow_two]
    have word₀ := image.outside (ar.hostDirectory+c*2) (.inr (by omega))
    have word₁ := image.outside (ar.hostDirectory+c*2+1) (.inr (by omega))
    rw [Nat.mul_comm c 2] at word₀ word₁ ⊢
    exact ⟨word₀.trans (h.1.trans (ar.receivingOwner_eq frame controls axis R input _ res pos c hc)),word₁.trans h.2⟩
  · intro j hj
    obtain ⟨hh,lab,grp,own,pair,_,_,_⟩ := ar.writer_order
    exact (image.outside j (.inl (by change j < ar.pairDirectory; omega))).trans
      ((banks).written_outside _ _ j (.inl (by change j < ar.hostDirectory; omega)))

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
