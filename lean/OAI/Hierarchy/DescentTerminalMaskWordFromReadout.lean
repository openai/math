import OAI.Hierarchy.DescentTerminalFullAddress
import OAI.Hierarchy.DescentTerminalTrailingCensus

namespace OAI
/-! # The last readout word bounds its preceding mask allocation -/

namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentTerminalLast DescentTerminalRowArena DescentTerminalVertexFields

noncomputable section

/-- The original terminal layout places the scalar counter, row arena and key
readout successively after the mask allocation. -/
theorem mask_room_from_trailing {blocks w : ℕ} (V : Home.Format) (cfg : Shape) (I : Input)
    (channels : MaskAllocation.Channels blocks) (start rows keys : ℕ)
    (word : trailingStop (trailingCut (last V cfg I channels start) cfg.terminal.rows)
      rows cfg.terminal.pool keys + 1 < 2^w) : start < 2^w := by
  let base := afterMeter V cfg channels start
  have first : start ≤ base := by
    change start ≤ start + _ + _ + cfg.sites + cfg.sites + 3
    omega
  have toArena : base ≤ (rowArena cfg I base).finish := (rowArena cfg I base).start_le 22
  obtain ⟨a,b,c,d,e⟩ := stages cfg I base
  have toLast : start ≤ last V cfg I channels start :=
    first.trans (toArena.trans (a.trans (b.trans (c.trans (d.trans e)))))
  unfold trailingStop trailingCut at word
  omega

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
