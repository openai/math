import OAI.Computability.BorderVNP.CubeScatterCheckedPayload
import OAI.Computability.BorderVNP.CubeTeamRawDeclaration

/-! # Recovering the common payload from raw received prefixes and native returns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {a q blocks K h b s : ℕ}
variable {f : ReturnedDelivery G pin ext L D pp lp owner origin stride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {decl : LengthDeclaration a q} {group : Fin q → Fin (R+1)} {anchor : Fin (R+1)}

/-- The actual lower-owner visits identify all selector words. Their declaration checkers and
native column/minimum instructions then force a unique interpretation of the raw deliveries,
including all rows with two groups on one team. No selector tuple is an input. -/
theorem SharedWriters.decode_raw_scheduled (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
    (scans : RawScans group pub mac decl (fun sym => (f.receivedRows g group sym).take
      (rowSelectorBits a q blocks K h decl.1 (Sym2.mk sym.val.1 sym.val.2))) blocks b h K s) (labels : q^(a+1) ≤ 2^w)
    (packets : Cube.Physical.Owned.packetTrials a q blocks*(h*s) < 2^w) (cap : declarationCap a q blocks b h s < 2^w)
    (dyn : HeaderDecode.Layout) {p : Arg → Word w} {mc : TeamOpcode.Macros w 8}
    {reg : Bank w} {m : Memory w} {es u mu fs t' mt}
    (decode : Runs p mc HeaderDecode.program reg m es u mu) (minimum : Runs p mc CubeLengths.minimum u mu fs t' mt)
    (fits : HeaderDecode.Fits dyn w) (atFrame : HeaderDecode.AtFrame dyn (readings p) (readings m))
    (primary : readings p 0+63 < 2^w) (header : dyn.header+12 < 2^w) (totalsRoom : dyn.totals+dyn.a ≤ 2^w)
    (separate : dyn.dense+dyn.entries ≤ dyn.totals ∨ dyn.totals+dyn.a ≤ dyn.dense)
    (sumRoom : dyn.d*dyn.d*dyn.cap < 2^w) (radix : dyn.d = q) (axes : dyn.a = a+1) :
    let l := CubeLengths.layout (readings p) (readings mu)
    CubeLengths.Fits w (readings p) (readings mu) → l.claimed = dyn.dense → l.totals = dyn.totals →
      l.coordinates = dyn.a → l.chosen = decl.1.val → CubeLengths.StoredRows (readings mu) l.claimed decl.2 →
      (∃! x : DeclaredShared blocks b h K s decl, sharedWords decl x = f.receivedRows g group) ∧
        ∀ j : Fin (a+1), readings mu (l.totals+j.val) = ∑ row, decl.2 row j := by
  obtain ⟨select,⟨words,⟨checked⟩⟩,_⟩ := scans.recover
  exact writer.decode_scheduled frame select words checked labels packets cap dyn decode minimum fits atFrame
    primary header totalsRoom separate sumRoom radix axes

end TeamContraction

end BorderVNP
end Computability
end OAI
