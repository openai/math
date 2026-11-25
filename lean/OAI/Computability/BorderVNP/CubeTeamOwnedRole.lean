import OAI.Computability.BorderVNP.CubeTeamOwnedSelectorRows
import OAI.Computability.BorderVNP.CubeTeamOwnedGroups
import OAI.Computability.BorderVNP.CubeISALocalRowChecked

/-! # Executing and verifying one actual strict endpoint role -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages Physical Physical.Owned Tally Scatter VPVNP.BurstRAM

variable {w n d blocks b h K s : ℕ}

/-- Data recovered after the real scatter, vertex directory append and coordinate checks.
The intermediate memory witnesses the packet-bank writes used by the verifier. -/
structure StrictReturn (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h)
    (src : Set ℕ) (actual : ℕ) (r : Bank w) (m : Memory w) (t : Bank w) (mt : Memory w) : Prop where
  /-- Both reserved ordinal registers retain their incoming values. -/
  cursors : readings t 22 = readings r 22 ∧ readings t 23 = readings r 23
  /-- The physical append cursor records the complete half-cube directory. -/
  vertex : readings t 7 = A.out+(2*blocks*(d.choose 2)^n)*(3*2^n)
  /-- Every read-only source for this or a later endpoint retains its actual word. -/
  source : ∀ a ∈ src, mt a = m a
  /-- Intermediate bank, terminal checker state and all protected memory words. -/
  stages : ∃ u mu, SideResult D A src r m u mu ∧
    LocalRow.Return h actual (LocalRow.head (layout D A.power A.header) n b h K s)
      (readings u) (readings mu)
      (subtotals itemRow (crossCount b s D.select) D.axis (Sym2.mk D.pair.val.1 D.pair.val.2))
      (.ofWords t mt)

/-- The actual strict endpoint stage consumes its genuine local choice stream and
passes the real row test for an authentic declaration. The selectors used in the
test come from the packet bank written by this very execution. -/
theorem strictRole_run {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {src : Set ℕ}
    (D : PacketRowData n d blocks b h K s) (A : SideData n d blocks b h) (r : Bank w) (m : Memory w)
    (ready : SideReady D A pub src r m) (actual claimed : ℕ) (rows : Sym2 (Fin d) → Fin (n+1) → ℕ)
    (input : CheckImage (layout D A.power A.header) src n actual claimed rows m)
    (space : LocalRow.Space (layout D A.power A.header) w n b h K s (readings pub 0) actual claimed)
    (labelsFit : d^(n+1) ≤ 2^w) (packetFit : packetTrials n d blocks*(h*s) < 2^w)
    (capFit : declarationCap n d blocks b h s < 2^w)
    (auth : passesLengths b s D.select (D.axis,rows))
    (directorySep : ∀ a ∈ src, a < A.out ∨ A.out+(2*blocks*(d.choose 2)^n)*(3*2^n) ≤ a)
    (checkSep : ∀ a ∈ src, LocalRow.Protected n h actual
      (LocalRow.head (layout D A.power A.header) n b h K s) a) :
    TraceRun pub mac (strictRole n b h K s) r m (rowChoices packetTrialValid D.choices)
      (sideCost D A + LocalRow.strictTicks n b h K s blocks D.axis D.pair)
      (StrictReturn D A src actual r m) := by
  let L := layout D A.power A.header
  have tail (u : Bank w) (mu : Memory w) (side : SideResult D A src r m u mu) :
      TraceRun pub mac (LocalRow.strictChecked n b h K s) u mu [] (LocalRow.strictTicks n b h K s blocks D.axis D.pair)
        (StrictReturn D A src actual r m) := by
    have keep (a : ℕ) (ha : a ∈ src) : mu a = m a := by
      rcases directorySep a ha with below | above
      · exact side.source a ha below
      · exact side.above a ha above
    have im := input.transfer keep
    have loaded := ready.protect.loaded ready.loaded keep
    have old (j : Reg) (hj : Control j) (hne : j ≠ 7) : readings u j = readings r j :=
      congrArg Fin.val (side.keep j hj hne)
    have stored (p : {p : Packet n d blocks // p.1.1 D.axis = D.pair}) :
        SelectorRead.Stored (readings mu) (L.bank + packetIndex p.val*bankWidth n b h K s) (D.select p.val) := by
      simpa only [L,layout,OwnedVertex.bankAt,ready.stride] using
        stored_after_strictSide ready side p.val p.property
    have checked := LocalRow.strictChecked_run pub mac u mu L D.axis D.pair b h K s actual claimed
      D.select rows loaded im.actualAt im.claimedAt im.table space rfl labelsFit packetFit capFit stored
      ((old 0 (by decide) (by decide)).trans ready.entry.zero)
      ((old 1 (by decide) (by decide)).trans ready.entry.one)
      ((old 4 (by decide) (by decide)).trans ready.entry.axis)
      ((old 14 (by decide) (by decide)).trans ready.entry.left)
      ((old 15 (by decide) (by decide)).trans ready.entry.right)
    have valid := checked.complete (fun j => (auth.1 (Sym2.mk D.pair.val.1 D.pair.val.2) j).symm)
    apply (traceRun_unsigned valid (LocalRow.strictChecked_unsigned n b h K s)).mono le_rfl
    intro t mt verified
    refine ⟨⟨verified.cursor.trans (old 22 (by decide) (by decide)),
      verified.bound.trans (old 23 (by decide) (by decide))⟩,verified.vertex.trans side.output,?_,u,mu,side,verified⟩
    intro a ha
    exact (Fin.ext (verified.outside a (checkSep a ha))).trans (keep a ha)
  simpa only [strictRole,List.append_nil] using (strictSide_run D A pub mac src r m ready).seq tail

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
