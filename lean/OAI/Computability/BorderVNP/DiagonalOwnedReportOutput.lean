import OAI.Computability.BorderVNP.DiagonalIssuedPrefixReceipt

/-! # Native sparse source and its held placement on one returned report prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open CellDispatch SignedPrep TeamContraction VPVNP.BurstRAM BorderVNP.Cube ScheduleClock SignedTaskArena
open FragmentRows CellSparse CellSparse.Packet CellSparse.Packet.Source SparseExterior TypedTaskBuilder
open CompactMachine CellMacro.Generator

variable {T n w : ℕ} (a : SignedTaskArena.Layout)
    (id : TableEntry a.cube.n a.cube.b a.cube.h a.cube.K a.cube.s → ℕ)
    (U : Fin (T+1) → PinStart SparseExterior.driver n w) {u : Fin (T+1)} (p : (U u).Prefix id)
    {team offsets ctl live ports description : ℕ} {Site I : Type}

local notation3 (prettyPrint := false) "ram" => (visits id U p).reports.val.2.2
local notation3 (prettyPrint := false) "head" => readings (U u).pub 0
local notation3 (prettyPrint := false) "fragment" => FragmentRows.Layout.fromFrame head (readings ram)
local notation3 (prettyPrint := false) "scan" => a.controlRows team head offsets ctl live ports

/-- One native call source retains both the original owner directory and
the exact emitted sparse packet used to read every requested logical value. -/
abbrev OwnedPrefixOutput (who : Fin a.cube.cells → Fin (T+1))
    {fit : (fragment).Fits w (readings ram)} {cells : a.fragments.cells=(fragment).cells}
    (e : SparseEmission a fragment ram fit cells) {data : ℕ → ℕ → Bool}
    (rows : (i : Fin ((scan).toLayout.before (readings e.output) a.cube.cells)) →
      SparseCell a fragment ram data i.val)
    (index : I → ℕ) (want : I → CellInput)
    (saved : (patch : SparsePatch (w:=w) Site (scan) (readings e.output)) →
      SparseEmission.NativeInputAt id U p e patch rows description → Prop) : Prop :=
  ∃ native : SparseSource id U p,
    OwnerTable (U u).pub p.2.val.2.2 ⟨team,a.before.limit,a.cube.cells⟩ (PositiveTeam.ownerWord who) ∧
    (∀ i, native.logicalAt (index i)=want i) ∧
    Nonempty {witness : (patch : SparsePatch (w:=w) Site (scan) (readings e.output)) ×
      SparseEmission.NativeInputAt id U p e patch rows description //
      witness.2.native=native ∧ saved witness.1 witness.2}

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
