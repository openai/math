import OAI.Hierarchy.DescentTerminalPreflightEarlier
import OAI.Hierarchy.DescentTerminalRouteColumnPrice
import OAI.Hierarchy.DescentTerminalScalarLUTPrice

namespace OAI
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalCompiledPrefix DescentTerminalRowArena
open DescentTerminalEmitter.Compact DescentTerminalPrimitiveArena DescentTerminalVertexFields
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (x : Spec) (begin_ rom q piece W K codes front : ℕ) (peer : Bank)
    (priorCables : Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
    (total modulo homes : Bank) (boundary : ℕ)
variable (cfg : DescentTerminalCompiledPrefix.Shape) (V : Home.Format)
    (other : AddressPlan.Input) (vertices A B : ℕ)
open DescentTerminalLocalPortBook
local notation "T" => AddressPlan.RouteSources.Tables.mk 4 vertices (vertices*A) A
  (Book.tokenBits (vertices*A)) W q K
local notation "mask_" => x.maskBase begin_
local notation "R_" => x.channels begin_
local notation "C_" => AddressPlan.meter V R_ mask_
local notation "base_" => AddressPlan.afterMeter V cfg R_ mask_
local notation "grain" => W*piece
local notation "raw" => cfg.terminal.plane.rawRows
local notation "candidate_" => DescentTerminalPaidBoot.candidate K W q piece codes raw front
local notation "id_" => front+DescentTerminalPaidBoot.total K W q piece codes raw
local notation "J_" => x.chipInput begin_ rom q grain peer priorCables total modulo homes boundary cfg other
local notation "row_" => AddressPlan.rowArena cfg J_ base_
local notation "cols_" => ScalarLiterals.columns q V.roles V.privateWords V.nodes V.addresses grain
                          vertices W B cfg.terminal.pool ((T).columns row_ (J_).sources)

local notation "I_" => x.reachedInput begin_ rom q piece W K codes front peer priorCables total modulo homes
  boundary cfg V other T vertices B

/-- Only the route tables and the four scalar tables purchase literal space in the original 43 columns. -/
theorem reached_need {h : ℕ} (rows : cfg.terminal.pool=K*W)
    (routed : Book.fixedWords vertices A W q≤2^(h/2))
    (keys : DescentTerminalSiteShelves.alphabet vertices W B≤2^(h/2))
    (headers : (DescentTerminalPrintedFields.capacity q V.roles V.privateWords V.nodes V.addresses grain vertices).total≤2^(h/2))
    (j : Fin 43) : need ((I_).sources j)≤2^(h/2)+4*cfg.terminal.pool :=by
  change need (cols_ j)≤_
  apply ScalarLiterals.priced <;> try assumption
  intro i
  rw [rows]
  apply AddressPlan.RouteSources.columns_priced vertices A W q K h row_ (J_).sources _ routed
  intro l
  change need (AddressPlan.HeaderColumns.columns _ _ (fun _=>Column.attained _) l)≤_
  unfold AddressPlan.HeaderColumns.columns
  split <;> exact Nat.zero_le _

/-- The same finite literal bound in terms of the node fields in the actual preflight page. -/
theorem reached_need_fields {h : ℕ} (rows : cfg.terminal.pool=K*W)
    (routed : Book.fixedWords vertices A W q≤2^(h/2)) (roles : 0<V.roles)
    (page : vertices*span q V.roles V.privateWords V.nodes V.addresses grain≤B)
    (small : 32*B≤h) (bins : 32*W≤h) (pack : 16*(q*grain)≤h) (large : 10≤h)
    (j : Fin 43) : need ((I_).sources j)≤2^(h/2)+4*cfg.terminal.pool :=by
  obtain ⟨keys,headers,_,_⟩:=shared_tables q V.roles V.privateWords V.nodes V.addresses grain vertices W B h
    roles page small bins pack large
  exact x.reached_need begin_ rom q piece W K codes front peer priorCables total modulo homes
    boundary cfg V other vertices A B rows routed keys headers j

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
