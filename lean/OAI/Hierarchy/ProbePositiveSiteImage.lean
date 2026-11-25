import OAI.Hierarchy.ProbePositiveSiteROM

namespace OAI
/-! # Common immutable input image and charged footprint of the socket decoder -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets.SiteROM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open ProtocolRAM TaggedShorterSupergroups
open scoped Fin.CommRing Classical
variable {w h W k attempts H K : ℕ}

def image (start : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (mem : Memory w) :=
  let base := start+2*ProtocolRAMSupergroupDirectory.span K
  ProtocolRAMSupergroupDirectory.mount start 1 groups dir (mount dir base mem)

def endAddress (start G H K : ℕ) := start+2*ProtocolRAMSupergroupDirectory.span K+footprint G H

theorem image_site (start : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (mem : Memory w) :
    Resident dir (start+2*ProtocolRAMSupergroupDirectory.span K) (image start groups dir mem) := by
  apply (resident dir _ mem).frame
  intro x hx _
  exact ProtocolRAMSupergroupDirectory.frame start 1 groups dir _ _ (Or.inr hx)

theorem image_directory (start : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (mem : Memory w) (fit : K≤2^w)
    (g : AllGroups h (2^W)) :
    let r := ((groups.symm g).val:Word w)
    (ProtocolRAMSupergroupDirectory.groupBank start K).read (image start groups dir mem) r=
      ((dir.group g).val:Word w) ∧
    (ProtocolRAMSupergroupDirectory.offsetBank start K).read (image start groups dir mem) r=
      (dir.base g:Word w) := by
  simpa only [image,Nat.mul_one] using ProtocolRAMSupergroupDirectory.resident start 1 groups dir
    (mount dir (start+2*ProtocolRAMSupergroupDirectory.span K) mem) fit g

/-- Outside the contiguous public header both mounted tables preserve every
input cell, including the variable permutation and future marked candidates. -/
theorem image_frame (start : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (mem : Memory w) (x : ℕ)
    (away : x<start ∨ endAddress start dir.groups H K≤x) : image start groups dir mem x=mem x := by
  unfold image
  have old : x<start ∨ start+2*ProtocolRAMSupergroupDirectory.span K≤x := by
    unfold endAddress at away
    omega
  rw [ProtocolRAMSupergroupDirectory.frame _ _ _ _ _ _ old]
  have outside : ¬(start+2*ProtocolRAMSupergroupDirectory.span K≤x ∧
      x<start+2*ProtocolRAMSupergroupDirectory.span K+footprint dir.groups H) := by
    unfold endAddress at away;omega
  simp only [mount,fillSegment,ite_eq_right outside]

/-- The actual dense public site-table budget uses the packing theorem's
charged product of groups and height. It never scans one group per input row. -/
theorem storage (start : ℕ) {G H K budget : ℕ} (positive : 0<H) (packing : G*H≤budget) :
    endAddress start G H K ≤ start+4*(K+1)+2*budget := by
  have g : G≤G*H := by simpa using Nat.mul_le_mul_left G positive
  have old := ProtocolRAMSupergroupDirectory.space K
  unfold endAddress footprint
  omega

end Hierarchy.ProbeStage.ReportSockets.SiteROM
end

end OAI
