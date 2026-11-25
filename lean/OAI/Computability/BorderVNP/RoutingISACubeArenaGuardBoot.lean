import OAI.Computability.BorderVNP.RoutingISACubeArenaGuardFrame
import OAI.Computability.BorderVNP.CubeTeamOwnedPublicPrefix
import OAI.Computability.BorderVNP.CubeRouteDataLayouts

/-! # Recovering the real padding frame from the native public group prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeArena

open BorderVNP.Cube BorderVNP.Cube.Padding BorderVNP.Cube.Tally VPVNP.BurstRAM
open LocalRow

/-- The actual public group return supplies the chosen axis, both secondary
bank scalars and the full powers table. Its protected boot words survive
the two subsequent directory writers. These are the pre-transmission inputs
to `Layout.padding_published`. -/
theorem Layout.published_before_writers {w : ℕ} (a : Layout) (pub : Arg → Word w) (f : BroadcastFrame)
    (B : Bootstrap w) (axis : Fin (a.n+1)) {raw : List Bool} {entry final : Memory w}
    {scheduled : ℕ → ℕ} (old : Fin 81 → Word w) (baseFields : B.old=a.extension old)
    (boot : BootPins pub f (B.extension a.header.d a.n a.header.blocks a.b a.h a.s) raw entry)
    (stat : B.stat a.header.d a.n a.header.blocks a.b a.h a.s = a.header)
    (room : a.stop < 2^w) (bankFit : bankWidth a.n a.b a.h a.K a.s < 2^w)
    (low : (pub 0).val+112 ≤ a.header.header)
    {owner : Fin a.header.d → ℕ} {rows : Sym2 (Fin a.header.d) → Fin (a.n+1) → ℕ}
    (scanned : a.ScannerWords (readings pub 0) f.team axis.val owner (readings pub) scheduled rows)
    (prefixWords : ∀ x < a.header.header, scheduled x = readings entry x)
    (controls : ℕ)
    (pair : PairDirectory.Image (a.pairWriter (pub 0).val)
      ((a.cellWriter (pub 0).val controls axis).written scheduled a.cells)
      (a.pairWriter (pub 0).val).count (readings final)) :
    Published (arenaPointers a) B pub final f.team axis a.header.d a.header.blocks a.b a.h a.K a.s := by
  obtain ⟨_,_,_,_,_,_,power,gw,gt,ot,op,ph,_⟩ := a.group_order
  have headerLow := a.writer_order.1
  have keep (x : ℕ) (hx : x < a.pairDirectory) : readings final x = scheduled x :=
    (pair.outside x (Or.inl hx)).trans ((a.cellWriter _ controls axis).written_outside scheduled a.cells x
      (Or.inl (hx.trans_le ph)))
  constructor
  · exact (keep (readings pub 0) (by change (pub 0).val < _; omega)).trans scanned.teamID
  · intro j _
    have under : (pub 0).val+31+j.val < a.header.header := by have := j.isLt; omega
    apply Fin.ext
    exact (keep _ (by omega)).trans ((prefixWords _ under).trans (congrArg Fin.val (boot.extension j)))
  · intro j v hv
    rw [baseFields]
    exact arena_literal a old room bankFit j v hv
  · rw [stat]
    exact (keep _ (by omega)).trans scanned.chosen
  · refine ⟨f.dst,readings entry,?_⟩
    intro j hj
    rw [stat]
    obtain ⟨seven,eight⟩ := secondary_banks a.header a.n (selectorWidth a.n a.K a.h) f.dst (readings entry)
    rcases List.mem_cons.mp hj with rfl | hj
    · exact (keep _ (by omega)).trans (scanned.setup.blocks.trans seven.symm)
    · have e : j=8 := List.mem_singleton.mp hj
      subst j
      exact (keep _ (by omega)).trans (scanned.setup.bank.trans eight.symm)
  · refine ⟨readings entry,?_⟩
    have val : axis.val ≤ a.n := by have := axis.isLt; omega
    exact (keep (a.powerBase+axis.val) (by omega)).trans
      ((scanned.setup.powers axis.val val).trans (installed_power (readings entry) axis).symm)

end RoutingISA.CubeArena

end BorderVNP
end Computability
end OAI
