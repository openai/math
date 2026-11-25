import OAI.Hierarchy.DescentTerminalRoleTableMount
import OAI.Hierarchy.DescentTerminalSliceExecution
import OAI.Hierarchy.DescentTerminalSlicePanel

namespace OAI
/-! # Word width and coordinate transport for the six printed role banks -/
namespace Hierarchy.DescentTerminalRoleTables

/-- Each literal field table is contained in the mounted role ROM. -/
theorem field_word_room (widths : Fin 6 → ℕ) {base stop w : ℕ}
    (mounted : base + count widths ≤ stop) (limit : stop < 2^w) (field : Fin 6) :
    widths field ≤ w := by
  have summand : 2^(widths field) ≤ marks widths :=
    Finset.single_le_sum (f := fun j : Fin 6 => 2^(widths j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ field)
  have inTable : marks widths ≤ count widths := by unfold count; omega
  have price := (((summand.trans inTable).trans (Nat.le_add_left _ base)).trans mounted).trans_lt limit
  exact ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp price).le

end Hierarchy.DescentTerminalRoleTables

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentTerminalSliceRuns DescentTerminalPointerDigits
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
variable {F : Type} [Field F]

theorem role_memory_reindex {bm1 hm1 ng1 nn1 bm2 hm2 ng2 nn2 nslots d w : ℕ}
    (blocks : bm2=bm1) (hosts : hm1=hm2) (cohorts : ng1=ng2) (nodes : nn1=nn2)
    (field : ℕ) (layout : Fin (Columns nslots)→Fin bm1→Gather.Address)
    (seed opWidth arity cap piece drift : ℕ) (G : PoweredGadget F) (op : RotorSpec)
    (cfg : RawWidths) (m : Memory w) :
    DescentTerminalSliceShelf.memory field (fun j (x : Fin bm2)=>layout j (x.cast blocks))
      (writePanel («s»:=seed) («Z»:=opWidth) (M:=nslots) (N:=nn2) (groups:=ng2) (d:=d) G op arity cap piece drift cfg) hm2 m =
    DescentTerminalSliceShelf.memory field layout
      (writePanel («s»:=seed) («Z»:=opWidth) (M:=nslots) (N:=nn1) (groups:=ng1) (d:=d) G op arity cap piece drift cfg) hm1 m :=by
  cases blocks
  cases hosts
  cases cohorts
  cases nodes
  rfl

end Hierarchy.DescentSixParty.SeedNamed

end OAI
