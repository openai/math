import OAI.Hierarchy.TaggedWideWindowProgramLayout
import OAI.Hierarchy.TaggedWideFrozenSeries

namespace OAI
/-! # Reading the public instruction tables for the actual per-type windows -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAMFrozenWindow ProtocolRAMPackedRanked ProtocolRAMSupergroupDirectory
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged
open scoped BigOperators Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
  (cap : ℕ) (dated : WideCPU.Dated (events v.mesh).length) (bits romStart : ℕ)
local notation "l" => v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart
local notation "g" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "base" => v.wideGroupROM x dated bits romStart
local notation "first" => v.wideFormatROM x dated bits romStart
local notation "S" => v.wideFormatEnd x m ell cap dated bits romStart

/-- The two packed-group banks, the original geometric layer table and the
thirteen lookup columns plus arithmetic bias/origin of every purchased type. -/
def wideWindowWords {W : ℕ} (mem : Memory W) : Memory W :=
  let grp:=ProtocolRAMSupergroupDirectory.mount base 1 (Equiv.refl (Fin g))
    (packedDirectory g (WideMemory.H x.h v.W k v.wideJobs)) mem
  let pre:=PruneFlag.layerAdvice (v.widePruneLayout x) (l).layers grp
  fun a=>
    if hit:∃i:Fin (m+1),((l).windows i).rom≤a ∧ a<((l).windows i).adviceEnd then
      let i:=Classical.choose hit
      ((l).windows i).mount ((l).windowBase i) pre a
    else pre a

local notation "dest" => v.wideWindowWords x m ell short u δ ξ cap dated bits romStart

private theorem window_unique {i j : Fin (m+1)} {a : ℕ}
    (hi : ((l).windows i).rom≤a ∧ a<((l).windows i).adviceEnd)
    (hj : ((l).windows j).rom≤a ∧ a<((l).windows j).adviceEnd) : i=j := by
  rcases lt_trichotomy i j with lt|same|gt
  · exact False.elim ((not_lt_of_ge (v.wideWindow_disjoint x m ell short u δ ξ cap first lt)) (hj.1.trans_lt hi.2))
  · exact same
  · exact False.elim ((not_lt_of_ge (v.wideWindow_disjoint x m ell short u δ ξ cap first gt)) (hi.1.trans_lt hj.2))

theorem wideWindowWords_read {W : ℕ} (mem : Memory W) (i : Fin (m+1)) {a : ℕ}
    (hi : ((l).windows i).rom≤a ∧ a<((l).windows i).adviceEnd) :
    let grp:=ProtocolRAMSupergroupDirectory.mount base 1 (Equiv.refl (Fin g))
      (packedDirectory g (WideMemory.H x.h v.W k v.wideJobs)) mem
    let pre:=PruneFlag.layerAdvice (v.widePruneLayout x) (l).layers grp
    dest mem a=((l).windows i).mount ((l).windowBase i) pre a := by
  have hit : ∃j:Fin (m+1),((l).windows j).rom≤a ∧ a<((l).windows j).adviceEnd:=⟨i,hi⟩
  simp only [wideWindowWords,dite_eq_left hit,window_unique v x m ell short u δ ξ cap dated bits romStart
    (Classical.choose_spec hit) hi]

theorem wideWindowWords_outside_types {W : ℕ} (mem : Memory W) (a : ℕ) (small : a<first) :
    let grp:=ProtocolRAMSupergroupDirectory.mount base 1 (Equiv.refl (Fin g))
      (packedDirectory g (WideMemory.H x.h v.W k v.wideJobs)) mem
    dest mem a=PruneFlag.layerAdvice (v.widePruneLayout x) (l).layers grp a := by
  have no : ¬∃j:Fin (m+1),((l).windows j).rom≤a ∧ a<((l).windows j).adviceEnd := by
    rintro ⟨j,low,_⟩
    change first+j.val*v.wideWindowStride x ell cap≤a at low
    omega
  exact dite_eq_right no

theorem wideWindowWords_layer {W : ℕ} (mem : Memory W) (j : Fin (siteLast x.h (2^v.W) k+1))
    (fits : (l).layers.size≤2^W) :
    (l).layers.read (dest mem) (j.val:Word W)=(PruneFlag.layerCode (v.widePruneLayout x) j.val:Word W) := by
  have inside : j.val<(l).layers.size:=j.isLt.trans_le (group_capacity _)
  have wide:=inside.trans_le fits
  have small : (l).layers.base+j.val<first:=by
    change _<(l).layers.base+(l).layers.size
    omega
  change dest mem ((l).layers.base+(j.val:Word W).val%(l).layers.size)=_
  rw [Fin.val_cast_of_lt wide,Nat.mod_eq_of_lt inside,v.wideWindowWords_outside_types x m ell short u δ ξ cap dated bits romStart mem _ small]
  have inPage : (l).layers.base≤(l).layers.base+j.val ∧ (l).layers.base+j.val<(l).layers.base+(l).layers.size:=by omega
  simp [PruneFlag.layerAdvice,ThreeFlat.RAM.fillSegment,inPage]

theorem wideWindowWords_before {W : ℕ} (mem : Memory W) (a : ℕ) (small : a<base) :
    dest mem a=mem a := by
  have beforeLayer : a < (l).layers.base := by
    change a < base+2*span g
    exact small.trans_le (Nat.le_add_right _ _)
  have beforeTypes : a < first := by
    change a < (l).layers.base+(l).layers.size
    exact beforeLayer.trans_le (Nat.le_add_right _ _)
  rw [v.wideWindowWords_outside_types x m ell short u δ ξ cap dated bits romStart mem a beforeTypes]
  have outside : ¬ ((l).layers.base ≤ a ∧ a < (l).layers.base+(l).layers.size) :=
    fun h => (not_le.mpr beforeLayer) h.1
  simpa only [PruneFlag.layerAdvice, ThreeFlat.RAM.fillSegment,
    ite_eq_right outside] using ProtocolRAMSupergroupDirectory.frame base 1 (Equiv.refl (Fin g))
      (packedDirectory g (WideMemory.H x.h v.W k v.wideJobs)) mem a (Or.inl small)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
