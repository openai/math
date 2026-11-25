import OAI.Computability.BorderVNP.CubeTeamDeclarationEntries
import OAI.Computability.BorderVNP.CubeTeamScheduledMinimum
import OAI.Computability.BorderVNP.CubeScatterTransmissionPayload

/-! # Decoding the routed shared payload from actual public and owned-row checks -/

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

/-- The physical prefix readback identifies one selector tuple for all teams. Their actual
row and public-minimum returns force its declaration, pin every auxiliary total and make
these very received RAM words decode to a unique common payload. -/
theorem SharedWriters.decode_checked (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (select : Packet a q blocks → Selector a K h)
    (readback : ∀ p : Symbols q, (f.receivedRows g group p).take
      (rowSelectorBits a q blocks K h decl.1 (Sym2.mk p.val.1 p.val.2)) = commonSelectors select decl.1 p)
    {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
    (scans : CheckedScans group pub mac decl select b s)
    (labels : q^(a+1) ≤ 2^w) (packets : Cube.Physical.Owned.packetTrials a q blocks*(h*s) < 2^w)
    (cap : declarationCap a q blocks b h s < 2^w)
    {p : Arg → Word w} {mc : TeamOpcode.Macros w 8} {reg : Bank w} {m : Memory w} {es t' mt}
    (minRun : Runs p mc CubeLengths.publicMinimum reg m es t' mt)
    (fit : CubeLengths.Fits w (readings p) (readings m))
    (shape : (CubeLengths.layout (readings p) (readings m)).entries = q*q*(a+1))
    (dim : (CubeLengths.layout (readings p) (readings m)).coordinates = a+1)
    (index : (CubeLengths.layout (readings p) (readings m)).chosen = decl.1.val)
    (table : CubeLengths.StoredRows (readings m) (CubeLengths.layout (readings p) (readings m)).claimed decl.2) :
    (∃! x : DeclaredShared blocks b h K s decl, sharedWords decl x = f.receivedRows g group) ∧
      ∀ j : Fin (a+1), readings m ((CubeLengths.layout (readings p) (readings m)).totals+j.val) = ∑ row, decl.2 row j := by
  obtain ⟨passing,totals⟩ := scans.passes labels packets cap minRun fit shape dim index table
  refine ⟨writer.decode_received frame ?_ ?_,totals⟩
  · intro sym
    rw [readback,commonSelectors_decode]
    rfl
  · intro other prefixes
    exact (commonSelectors_injective decl.1 (fun sym => (prefixes sym).symm.trans (readback sym))) ▸ passing

/-- Payload recovery using the two adjacent programs in the actual signed scheduling table.
The header decoder's stores provide the totals before the native minimum test. -/
theorem SharedWriters.decode_scheduled (writer : SharedWriters f g src)
    (frame : SymbolFrame g (src anchor) blocks K h decl group)
    (select : Packet a q blocks → Selector a K h)
    (readback : ∀ sym : Symbols q, (f.receivedRows g group sym).take
      (rowSelectorBits a q blocks K h decl.1 (Sym2.mk sym.val.1 sym.val.2)) = commonSelectors select decl.1 sym)
    {pub : Fin (R+1) → Arg → Word w} {mac : Fin (R+1) → TeamOpcode.Macros w 8}
    (scans : CheckedScans group pub mac decl select b s) (labels : q^(a+1) ≤ 2^w)
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
  intro l fit dense target dim index table
  obtain ⟨least,totals⟩ := scheduledMinimum_return decl dyn decode minimum fits atFrame primary header
    totalsRoom separate sumRoom radix axes fit dense target dim index table
  have pass := (rows_and_minimum_iff group b s select decl).mp
    ⟨fun _ _ _ => scans.row_counts labels packets cap _,least⟩
  refine ⟨writer.decode_received frame ?_ ?_,totals⟩
  · intro sym
    rw [readback,commonSelectors_decode]
    rfl
  · intro other prefixes
    exact (commonSelectors_injective decl.1 (fun sym => (prefixes sym).symm.trans (readback sym))) ▸ pass

end TeamContraction

end BorderVNP
end Computability
end OAI
