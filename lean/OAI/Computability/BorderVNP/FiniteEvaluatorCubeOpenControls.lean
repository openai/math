import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenLayouts
import OAI.Computability.BorderVNP.PackedRoutingHeaders

/-! # Reading the two marked sort banks and the signed controls after host scatter

Only the physical endpoint cells are written by the host copy. The compact
bundle producer then writes the allocated range and row tables. Consequently
the geometry's stable-sort certificate and the signed controls supply the
actual subroutine inputs at both boundaries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open CellPacketGeometry RoutingISA.CellPacket

/-- Reading the same two physical banks preserves the complete stable bundle
certificate, including the exact range and source words for each global cell. -/
theorem SectionSpec.transfer {C N b dest : ℕ} {owner : Fin N → Fin C} {header : Fin N → BundleHeader}
    {rect : C+6*N+C ≤ 2^b} {m m' : ℕ → ℕ} (h : SectionSpec rect owner header m dest)
    (keep : ∀ a, dest ≤ a → a < dest+2^b+2^b → m' a=m a) : SectionSpec rect owner header m' dest := by
  have rank (i : Fin (2^b)) : m' (dest+(2^b+i.val)) = m (dest+(2^b+i.val)) := by
    have hi := i.isLt
    exact keep _ (by omega) (by omega)
  refine ⟨fun i => (rank i).trans_lt (h.rankBound i),fun c => ?_,fun c => ?_⟩
  · simpa only [rank] using h.markerOrder c
  · obtain ⟨len,words⟩ := h.cell c
    simp only [sectionRange] at len words
    simp only [sectionRange,rank]
    refine ⟨len,fun i => ?_⟩
    have hi := i.isLt
    have ordered := h.markerOrder c
    have stop := h.rankBound (Markers.stop rect c)
    change m' (dest+m (dest+(2^b+(Markers.start rect c).val))+1+i.val) = _
    rw [keep _ (by omega) (by omega)]
    exact words i

end Packing.BottomReports.BundleSort

namespace RoutingISA.SignedTaskArena

open Packing BottomReports BorderVNP.Cube FiniteEvaluator

variable (t : Layout) {team frame offsets control live ports bundles b w : ℕ}

/-- The ten ordinary frame locations consumed by the two physical producers. -/
structure Layout.OpenFields (t : Layout) (team frame offsets control live ports bundles : ℕ) (m : ℕ → ℕ) : Prop where
  teamWord : m frame=team
  cells : m (frame+15)=t.cube.cells
  bundlesWord : m (frame+66)=bundles
  banks : m (frame+72)=t.cube.hostDirectory
  offsetsWord : m (frame+87)=offsets
  cables : m (frame+7)=t.cube.cables
  liveWord : m (frame+65)=live
  portsWord : m (frame+1)*m (frame+67)=ports
  controlWord : m (frame+92)=control

/-- The routing header gives the cable, offset and live pointers. The remaining
operands are the processor team, cell and bundle counts, physical bank and
secondary-control pointers from the signed frame. -/
theorem Layout.OpenFields.of_header {origin : ℕ} {m : ℕ → ℕ}
    (hdr : RoutingOutputs.Header frame origin t.cube.cables t.cube.cells bundles m)
    (teamWord : m frame=team) (cells : m (frame+15)=t.cube.cells) (bundle : m (frame+66)=bundles)
    (bank : m (frame+72)=t.cube.hostDirectory) (portsWord : m (frame+1)*m (frame+67)=ports)
    (ctrl : m (frame+92)=control) :
    t.OpenFields team frame (RoutingOutputs.bases origin t.cube.cables t.cube.cells bundles).ends control
      (RoutingOutputs.bases origin t.cube.cables t.cube.cells bundles).livePairs ports bundles m :=
  ⟨teamWord,cells,bundle,bank,hdr.ends,hdr.edges,hdr.livePairs,portsWord,ctrl⟩

/-- The raw frame remains sufficient on any later image preserving its actually
addressed words. In particular the private count at index 46 is unrestricted. -/
theorem Layout.OpenFields.transfer {m m' : ℕ → ℕ} (h : t.OpenFields team frame offsets control live ports bundles m)
    (keep : ∀ i ∈ [0,1,7,15,65,66,67,72,87,92], m' (frame+i)=m (frame+i)) :
    t.OpenFields team frame offsets control live ports bundles m' := by
  have first := keep 0 (by decide)
  simp only [Nat.add_zero] at first
  exact ⟨first.trans h.teamWord,(keep 15 (by decide)).trans h.cells,(keep 66 (by decide)).trans h.bundlesWord,
    (keep 72 (by decide)).trans h.banks,(keep 87 (by decide)).trans h.offsetsWord,
    (keep 7 (by decide)).trans h.cables,(keep 65 (by decide)).trans h.liveWord,
    by rw [keep 1 (by decide),keep 67 (by decide),h.portsWord],(keep 92 (by decide)).trans h.controlWord⟩

/-- The four directory words and eight row-control operands are the actual
published signed vector, for every team and every number of retained bundles. -/
theorem Layout.OpenFields.inputs {m : ℕ → ℕ} (f : t.OpenFields team frame offsets control live ports bundles m)
    (ctl : ∀ i : Fin 37, m (control+i.val)=t.controls i.val) :
    (t.bundleLayout frame control bundles).loaded frame m ∧ (t.controlRows team frame offsets control live ports).Fields m := by
  exact ⟨⟨rfl,f.cells,f.bundlesWord,f.controlWord,ctl 18,ctl 19,ctl 20,ctl 21⟩,
    ⟨⟨f.teamWord,f.cells,f.banks,f.offsetsWord,f.cables,f.liveWord,f.portsWord,f.controlWord⟩,
      ⟨ctl 11,ctl 12,ctl 13,ctl 14,ctl 15,ctl 16,ctl 17,ctl 18⟩⟩⟩

variable (owner : Fin bundles → Fin t.cube.cells) (header : Fin bundles → BundleHeader)

local notation "H" => t.openInputs team frame offsets control live ports bundles b owner header

/-- Geometry and signed frame at the entry of the suffix imply all memory
preconditions of both directory writers on their actual intermediate images. -/
theorem Layout.open_inputs_read {m : ℕ → ℕ} (f : t.OpenFields team frame offsets control live ports bundles m)
    (ctl : ∀ i : Fin 37, m (control+i.val)=t.controls i.val)
    (rect : t.cube.cells+6*bundles+t.cube.cells ≤ 2^b)
    (bank : t.p.bundleInverse=t.p.bundlePayload+2^b)
    (sort : BundleSort.SectionSpec rect owner header m t.p.bundlePayload)
    (primary : frame+112 ≤ t.cube.cellBank) (directory : control+37 ≤ t.cube.cellBank)
    (sorted : t.p.bundleInverse+2^b ≤ t.cube.cellBank)
    (hostDest : let h := HostScatter.Layout.fromFrame frame m
      ∀ i < h.count, ∀ side, h.Owned m i side → t.cube.cellBank ≤ h.dest m i side) :
    (H).bundles.loaded frame (OpenSuffix.hostImage frame m) ∧
      (H).bundles.Sections (H).groups (H).sortWidth (OpenSuffix.hostImage frame m) ∧
      BundleDirectory.«prefix» (H).groups (H).bundles.cells=(H).bundles.bundles ∧
      (H).control.Fields ((H).bundleImage frame m) := by
  have host (a : ℕ) (lo : a<t.cube.cellBank) : OpenSuffix.hostImage frame m a=m a :=
    HostScatter.Layout.prefix_outside _ _ _ _ (fun i hi side own => .inl (lo.trans_le (hostDest i hi side own)))
  have retained := sort.transfer (m':=OpenSuffix.hostImage frame m) (fun a _ hi => host a (by omega))
  have loaded := (f.transfer t (fun i hi => host _ (by simp at hi; omega))).inputs t
    (fun i => (host _ (by have := i.isLt; omega)).trans (ctl i))
  have deck := t.constants_le_before
  have cell := t.cube.separated.2.2.2.2.2
  have base : t.cube.stop ≤ CubeConstants.arenaEnd t.cube.stop t.id := by
    unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  have clear := OpenSuffix.afterDeck_of_allocation (H) t.before le_rfl rfl rfl rfl rfl
  have after (a : ℕ) (lo : a<t.cube.cellBank) : (H).bundleImage frame m a=m a :=
    ((H).bundles.image_outside _ _ _ _ (.inl (lo.trans_le (cell.trans (base.trans (deck.trans clear.ranges)))))
      (.inl (lo.trans_le (cell.trans (base.trans (deck.trans clear.bundles)))))).trans (host a lo)
  have fields := (f.transfer t (fun i hi => after _ (by simp at hi; omega))).inputs t
    (fun i => (after _ (by have := i.isLt; omega)).trans (ctl i))
  exact ⟨loaded.1,(H).bundles.sections_of_sort owner header rect _ bank retained,
    BundleDirectory.prefix_groups owner header,fields.2⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
