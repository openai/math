import OAI.Computability.BorderVNP.FiniteEvaluatorCubeTriple
import OAI.Computability.BorderVNP.CubeISAOwnedStrictSideInverse

/-! # Inverting an arbitrary successful native triple-directory role

The actual private choices determine a scattered assignment with the same
routed exterior. The selector is read back from those scattered words and the
actual checker certifies its coordinate row. No passing global declaration is
required to invert a single role.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Physical.Owned BorderVNP.Cube.Tally
open BorderVNP.Cube.Scatter BorderVNP.Cube.TeamRows VPVNP.BurstRAM
open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages
open scoped Classical

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)
variable {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {src : Set ℕ} {r t : Bank w} {m mt : Memory w}

/-- Any normal return of the complete strict role, including the declaration
verifier, determines an actual physical private assignment, its memory image
and the verified declaration row for its original packet selector. -/
theorem strict_return_sound (ready : SideReady D A pub src r m) (actual claimed : ℕ) (rows : Sym2 (Fin d) → Fin (n+1) → ℕ)
    (input : CheckImage (layout D A.power A.header) src n actual claimed rows m)
    (space : LocalRow.Space (layout D A.power A.header) w n b h K s (readings pub 0) actual claimed)
    (labelsFit : d^(n+1) ≤ 2^w) (packetFit : packetTrials n d blocks*(h*s) < 2^w)
    (capFit : declarationCap n d blocks b h s < 2^w)
    (directorySep : ∀ a ∈ src, a < A.out ∨ A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ a)
    (checkSep : ∀ a ∈ src, LocalRow.Protected n h actual (LocalRow.head (layout D A.power A.header) n b h K s) a)
    {es} (run : Runs pub mac (strictRole n b h K s) r m es t mt) :
    ∃ x z, D.KeepsExterior x z ∧ SideReady (D.withWords x z) A pub src r m ∧
      StrictReturn (D.withWords x z) A src actual r m t mt ∧
      ∀ j, subtotals itemRow (crossCount b s D.select) D.axis (Sym2.mk D.pair.val.1 D.pair.val.2) j =
        rows (Sym2.mk D.pair.val.1 D.pair.val.2) j := by
  obtain ⟨_,u,mu,_,_,scatter,checked⟩ := RoutingISA.CellDispatch.seq_split run
  obtain ⟨x,z,ext,_,_,_,side⟩ := strictSide_recover D A pub mac src r m ready scatter
  let E := D.withWords x z
  have prepared : SideReady E A pub src r m := {ready with crosses := crossing_exterior D A x z ext ▸ ready.crosses}
  let L := layout D A.power A.header
  have keep (a : ℕ) (ha : a ∈ src) : mu a=m a := by
    rcases directorySep a ha with lo | hi
    · exact side.source a ha lo
    · exact side.above a ha hi
  have im := input.transfer keep
  have loaded := ready.protect.loaded ready.loaded keep
  have kept (j : Reg) (hj : Control j) (hne : j ≠ 7) : readings u j=readings r j :=
    congrArg Fin.val (side.keep j hj hne)
  have stored (p : {p : Packet n d blocks // p.1.1 D.axis = D.pair}) :
      SelectorRead.Stored (readings mu) (L.bank+packetIndex p.val*bankWidth n b h K s) (D.select p.val) := by
    simpa only [L,layout,OwnedVertex.bankAt,E,PacketRowData.withWords,ready.stride] using stored_after_strictSide prepared side p.val p.property
  have result := ((LocalRow.strictChecked_run pub mac u mu L D.axis D.pair b h K s actual claimed D.select rows
    loaded im.actualAt im.claimedAt im.table space rfl labelsFit packetFit capFit stored
    ((kept 0 (by decide) (by decide)).trans ready.entry.zero) ((kept 1 (by decide) (by decide)).trans ready.entry.one)
    ((kept 4 (by decide) (by decide)).trans ready.entry.axis) ((kept 14 (by decide) (by decide)).trans ready.entry.left)
    ((kept 15 (by decide) (by decide)).trans ready.entry.right)).sound checked)
  refine ⟨x,z,ext,prepared,?_,result.1⟩
  exact ⟨⟨result.2.cursor.trans (kept 22 (by decide) (by decide)),result.2.bound.trans (kept 23 (by decide) (by decide))⟩,
    result.2.vertex.trans side.output,fun a ha => (Fin.ext (result.2.outside a (checkSep a ha))).trans (keep a ha),
    u,mu,side,result.2⟩

/-- At every compact rank the public triple of any normal return names the
actual routed selector and owned vertex, even when private packet values vary. -/
theorem strict_sound (ready : SideReady D A pub src r m) (actual claimed : ℕ) (rows : Sym2 (Fin d) → Fin (n+1) → ℕ)
    (input : CheckImage (layout D A.power A.header) src n actual claimed rows m)
    (space : LocalRow.Space (layout D A.power A.header) w n b h K s (readings pub 0) actual claimed)
    (labelsFit : d^(n+1) ≤ 2^w) (packetFit : packetTrials n d blocks*(h*s) < 2^w)
    (capFit : declarationCap n d blocks b h s < 2^w)
    (directorySep : ∀ a ∈ src, a < A.out ∨ A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ a)
    (checkSep : ∀ a ∈ src, LocalRow.Protected n h actual (LocalRow.head (layout D A.power A.header) n b h K s) a)
    (subtotal : actual+(n+1) ≤ A.out) (scratch : LocalRow.head (layout D A.power A.header) n b h K s+8+h ≤ A.out)
    {es} (run : Runs pub mac (strictRole n b h K s) r m es t mt) :
    Stored (readings mt) A.out ((CubeVisits.row D.axis D.pair D.high blocks).map (visit D.base D.stride D.select D.demand D.supply)) := by
  obtain ⟨x,z,_,pre,ret,_⟩ := strict_return_sound D A ready actual claimed rows input space labelsFit packetFit capFit
    directorySep checkSep run
  have done := strict_stored (D.withWords x z) A pre ret subtotal scratch
  intro i
  let xs := CubeVisits.row D.axis D.pair D.high blocks
  let j : Fin (xs.map (visit D.base D.stride D.select x z)).length := ⟨i.val,by simpa only [List.length_map] using i.isLt⟩
  have hit := done j
  simp only [List.getElem_map] at hit ⊢
  exact hit

end FiniteEvaluator.CubeTriple

end BorderVNP
end Computability
end OAI
