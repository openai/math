import OAI.Computability.BorderVNP.CubeScatterPaddingPublished
import OAI.Computability.BorderVNP.RoutingISACubeArena

/-! # Padding guard allocations in the complete cube routing arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA CubeArena VPVNP.BurstRAM Tally

/-- The five pointers used by the padding verifier in the shared cube arena. -/
def arenaPointers (L : CubeArena.Layout) : Pointers :=
  ⟨L.powerBase,L.ownerBase,L.widthBase,L.pairDirectory,L.singleBank⟩

private theorem public_bounds (L : CubeArena.Layout) :
    L.widthBase+L.alphabet^2 ≤ L.stop ∧ L.powerBase+(L.n+1) ≤ L.stop ∧
    L.ownerBase+L.header.d ≤ L.stop ∧ L.pairDirectory+3*L.alphabet^2 ≤ L.stop ∧
    L.vertexBase ≤ L.stop := by
  have e : L.records ≤ L.stop := by
    unfold CubeArena.Layout.stop CubeArena.Layout.cellBank CubeArena.Layout.pairBase TableLayout.reserveEnd
    omega
  unfold CubeArena.Layout.records CubeArena.Layout.hostDirectory CubeArena.Layout.pairDirectory
    CubeArena.Layout.ownerBase CubeArena.Layout.teamTotals CubeArena.Layout.groupWeights
    CubeArena.Layout.powerBase CubeArena.Layout.ordinalBase at *
  have hv : L.vertexBase ≤ L.widthBase := by
    unfold CubeArena.Layout.widthBase CubeArena.Layout.dataMean CubeArena.Layout.cableMean
      CubeArena.Layout.demands CubeArena.Layout.nodes CubeArena.Layout.heads CubeArena.Layout.publicBase
    omega
  omega

/-- One bound on the actual arena's high-water address gives all physical array and
arithmetic extents for the native padding verifier. -/
theorem physicalRoom_of_arena {w : ℕ} (L : CubeArena.Layout) (frame team : ℕ)
    (axis : Fin (L.n+1)) (hd : 0 < L.header.d) (fit : L.stop < 2^w) :
    PhysicalRoom ((arenaPointers L).layout frame team L.header.packetBase axis L.header.d L.header.blocks L.b L.h L.K L.s)
      w L.n L.header.d L.header.blocks L.b L.h L.K L.s := by
  obtain ⟨widths,_,owners,triples,vertices⟩ := public_bounds L
  have hZ : 0 < L.alphabet := pow_pos hd _
  have pos : 0 < L.alphabet^2 := pow_pos hZ _
  have stride := Nat.le_mul_of_pos_left (L.header.blocks*(L.h*L.b)) pos
  have singles : L.singleBank+L.alphabet^2*(L.header.blocks*(L.h*L.b)) ≤ L.stop := vertices
  have packet : L.packetEnd ≤ L.stop :=
    (show L.packetEnd ≤ L.singleBank from by unfold CubeArena.Layout.singleBank; omega).trans
      (L.separated.2.1.trans vertices)
  have widthEnd := widths.trans_lt fit
  constructor
  · change L.header.d^(L.n+1)*L.header.d^(L.n+1) < 2^w
    change L.alphabet*L.alphabet < _
    rw [← pow_two]
    omega
  · omega
  · exact owners.trans fit.le
  · simpa only [arenaPointers,Pointers.layout,Layout.count,← pow_two,CubeArena.Layout.alphabet] using widths.trans fit.le
  · simpa only [arenaPointers,Pointers.layout,Layout.count,← pow_two,CubeArena.Layout.alphabet] using triples.trans fit.le
  · simpa only [arenaPointers,Pointers.layout,← pow_two,CubeArena.Layout.alphabet] using singles.trans fit.le
  · exact packet.trans fit.le

/-- The installed secondary header and a fitted cube arena also bound the selected
power-table address and the outer-loop count. -/
theorem bootstrapRoom_of_arena {w : ℕ} (L : CubeArena.Layout) (B : Bootstrap w) (pub : Arg → Word w)
    (axis : Fin (L.n+1)) (hd : 0 < L.header.d) (fit : L.stop < 2^w)
    (header : L.header = B.stat L.header.d L.n L.header.blocks L.b L.h L.s)
    (installed : L.header.Fits w L.n (selectorWidth L.n L.K L.h) (readings pub 0))
    (profile : B.profile < 2^w) (bc : L.h*L.b < 2^w) :
    B.Room (arenaPointers L) pub L.header.d L.n L.header.blocks L.b L.h L.K L.s := by
  have room := physicalRoom_of_arena L 0 0 axis hd fit
  exact ⟨header ▸ installed,profile,bc,(public_bounds L).2.1.trans fit.le,room.pairs⟩

end Cube.Padding

end BorderVNP
end Computability
end OAI
