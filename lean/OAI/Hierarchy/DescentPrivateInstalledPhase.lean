import OAI.Hierarchy.DescentPrivateNativePhase
import OAI.Hierarchy.DescentFallbackPeriodTariff

namespace OAI
/-! # The installed fallback window as one native chronological phase -/
namespace Hierarchy.DescentFallbackPeriod
open DescentPacking.PackedMatch.Local.Gather
open DescentPackedFallbackTree.Image DescentSixParty.Chronology DescentSIMDLookup DescentPackedZip DescentSharedBookScan
open DescentFallbackRankRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {D L cap n r : ℕ}

def installedPhase (chart : Chart) (tabs : Fin (inputCount D L cap n r)→Tables)
    (reads : Fin (inputCount D L cap n r)→Expr) (menu : Banks)
    (w H G M Ht target mid out : ℕ) : NativePhase w :=
  let phase (slots rows : ℕ) (paid act : Expr) : NativePhase w :=
    { program := (scan w target slots paid).seq
        ((scan w mid rows act).seq (scan w out rows (DescentSIMDLookup.lookup menu)))
      ticks := (4+slots*(2*paid.work+4))+((4+rows*(2*act.work+4))+(4+44*rows))
      image := fun m => image out rows (DescentSIMDLookup.lookup menu)
        (image mid rows act (image target slots paid m))
      cheap := cheap_seq (scan_cheap w target slots paid)
        (cheap_seq (scan_cheap w mid rows act) (scan_cheap w out rows (DescentSIMDLookup.lookup menu))) }
  phase (H*DescentSharedBookScan.width r (2^n) D) (H*chunks G M)
    (record chart H D (2^Ht) (Ht+2)) (assembly tabs reads)

/-- The three loops traverse only their fixed public extents. All word contents,
including malformed row keys and arbitrary dictionary entries, follow the same clock. -/
theorem installedPhase_any (chart : Chart) (tabs : Fin (inputCount D L cap n r)→Tables)
    (reads : Fin (inputCount D L cap n r)→Expr) (menu : Banks)
    (w H G M Ht target mid out : ℕ)
    (sharedFits : (record chart H D (2^Ht) (Ht+2)).Fits w target)
    (sharedRoom : target+H*DescentSharedBookScan.width r (2^n) D<2^w)
    (gatherFits : (assembly tabs reads).Fits w mid) (gatherRoom : mid+H*chunks G M<2^w)
    (menuFits : (DescentSIMDLookup.lookup menu).Fits w out) (outRoom : out+H*chunks G M<2^w)
    (m : Memory w) : (installedPhase chart tabs reads menu w H G M Ht target mid out).Runs m := by
  let field:=record chart H D (2^Ht) (Ht+2)
  let slots:=H*DescentSharedBookScan.width r (2^n) D
  let rows:=H*chunks G M
  let first:=image target slots field m
  let act:=assembly tabs reads
  let second:=image mid rows act first
  have one:=@ProtocolRAM.scan_exec w target slots field m sharedFits sharedRoom
  have two:=@ProtocolRAM.scan_exec w mid rows act first gatherFits gatherRoom
  have three : (scan w out rows (DescentSIMDLookup.lookup menu)).Exec second
      (image out rows (DescentSIMDLookup.lookup menu) second) (4+44*rows) := by
    rw [Nat.mul_comm 44 rows]
    exact @ProtocolRAM.scan_exec w out rows (DescentSIMDLookup.lookup menu) second menuFits outRoom
  intro P R K
  exact one.then (two.then three)

theorem phase_keeps (chart : Chart) (tabs : Fin (inputCount D L cap n r)→Tables)
    (reads : Fin (inputCount D L cap n r)→Expr) (menu : Banks)
    (w H G M Ht target mid out : ℕ) (mem : Memory w) (addr : ℕ)
    (low : addr< min target (min mid out)) :
    (installedPhase chart tabs reads menu w H G M Ht target mid out).image mem addr=mem addr := by
  have ht:addr<target:=(lt_min_iff.mp low).1
  have hm:addr< mid:=(lt_min_iff.mp (lt_min_iff.mp low).2).1
  have ho:addr<out:=(lt_min_iff.mp (lt_min_iff.mp low).2).2
  dsimp only [installedPhase,imageBank]
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ho)).trans
    ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hm)).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ht)))

end
end Hierarchy.DescentFallbackPeriod

end OAI
