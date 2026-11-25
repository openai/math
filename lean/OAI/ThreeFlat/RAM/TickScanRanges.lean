import OAI.ThreeFlat.RAM.TickPhysicalABI

namespace OAI
/-! # Space for the mounted native group-scan streams -/

namespace ThreeFlat.RAM.TickActiveROM

structure ScanRanges (B : Layout) (n w : ℕ) : Prop where
  auxChunk : B.auxRequest+8*B.bits ≤ B.chunkRequest
  chunkTable : B.chunkRequest+8*B.bits ≤ B.intervalTable
  tableCount : B.intervalTable+4*n ≤ B.intervalCount
  countMap : B.intervalCount < B.intervalMap
  mapFit : B.intervalMap+B.bits < 2^w

open Diagonal.TickWorkspace

theorem ScanRanges.mounted (u a teams cap q nt ns np n w : ℕ)
    (requests : 8*a ≤ stride u) (rows : 4*n ≤ stride u) (fit : base u 8 ≤ 2^w) :
    ScanRanges (TickPhysicalABI.mounted u a teams cap q nt ns np) n w := by
  have pos : 0 < stride u := by simp [stride]
  simp only [TickPhysicalABI.mounted,TickPhysicalABI.layout]
  constructor <;> simp only [base] at * <;> omega


end ThreeFlat.RAM.TickActiveROM

end OAI
