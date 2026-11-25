import OAI.Hierarchy.DescentTerminalRouteLiteralFrames
import OAI.Hierarchy.DescentTerminalRouteTablesRead
import OAI.Hierarchy.DescentTerminalScalarLiterals
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Fixed route-table readbacks after compact installation and scalar column substitution -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalEmitter.Compact
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {blocks v B bw:ℕ} (V:Home.Format) (S:Shape) (J:Input) (R:MaskAllocation.Channels blocks)
variable (start header q t H N A p verts W:ℕ) (qp:0<q)
variable (short:v*span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece≤B)
variable (T:RouteSources.Tables) (prior:Fin 43→ℕ→ℕ)
local notation "ba" => afterMeter V S R start
local notation "baseArena" => rowArena S J ba
local notation "bookCols" => T.columns baseArena J.sources
local notation "c" => ScalarLiterals.columns q t H N A p verts W B S.terminal.pool bookCols
local notation "I" => ({J with sources:=c}:Input)
local notation "fixed" => ScalarLiterals.data q t H N A p verts W B S.terminal.pool qp bookCols (T.value prior)
local notation "O" => registers V S R start header
local notation "C" => meter V R start
local notation "L" => layout S I ba O
local notation "loaded" => input V S I R start header short fixed
local notation "planStart" => fun m:Memory bw=>(baseArena).mount (loaded m)
local notation "position" => fun m:Memory bw=>Suffix.positioned S L (planStart m)
local notation "μ" => fun m:Memory bw=>Suffix.events S L (C).layout (planStart m)
local notation "formatted" => fun m:Memory bw=>DescentTerminalEmitter.formatted S.terminal (L).emit (μ m)
local notation "named" => fun m:Memory bw=>DescentTerminalEmitter.named S.terminal (L).emit (μ m)
local notation "sources" => inputs S I ba

theorem installed_route_tables (m:Memory bw) (early:Earlier S I ba (C).layout bw)
    (room:last V S I R start<2^bw) :
    T.Reads baseArena J.sources prior sources (position m) ∧
    T.Reads baseArena J.sources prior sources (formatted m) ∧
    T.Reads baseArena J.sources prior sources (named m) := by
  have stages_ (j:Fin 43) (lo:29≤j.val) (hi:j.val≤36) (u:Fin (need (bookCols j))) :
      (sources j).read (position m) (u.val:Word bw)=(T.value prior j u.val:Word bw) ∧
      (sources j).read (formatted m) (u.val:Word bw)=(T.value prior j u.val:Word bw) ∧
      (sources j).read (named m) (u.val:Word bw)=(T.value prior j u.val:Word bw) := by
    have other (k:Fin 43) (outside:k.val<29 ∨ 36<k.val) : j≠k := by
      rintro rfl;omega
    have bought:bookCols j=.literal (need (bookCols j)):=by
      fin_cases j <;> first | rfl | (exfalso; revert lo hi; decide)
    have same:c j=bookCols j:=by
      simp only [ScalarLiterals.columns,ite_eq_right (other 37 (by decide)),ite_eq_right (other 39 (by decide)),
        ite_eq_right (other 41 (by decide)),ite_eq_right (other 42 (by decide))]
    have original:sources j=view (pageEnd S I ba) c j:=by
      simp only [inputs,other 1 (by decide),other 13 (by decide),other 38 (by decide),
        other 10 (by decide),other 11 (by decide),other 22 (by decide),other 23 (by decide),
        other 40 (by decide),or_self,ite_false]
    let j':Fin (size (c j)):=⟨u.val,by
      rw [congrArg DescentTerminalEmitter.Compact.size (same.trans bought)]
      exact u.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)⟩
    have receipt:=literal_stages V S I R start header short fixed m early room j (same.trans bought) j'
    have atom:fixed j j'=T.value prior j u.val:=by
      simp only [ScalarLiterals.data,ite_eq_right (other 37 (by decide)),ite_eq_right (other 39 (by decide)),
        ite_eq_right (other 41 (by decide)),ite_eq_right (other 42 (by decide))];rfl
    rw [original,←atom]
    exact receipt
  exact ⟨fun j lo hi u=>(stages_ j lo hi u).1,fun j lo hi u=>(stages_ j lo hi u).2.1,
    fun j lo hi u=>(stages_ j lo hi u).2.2⟩

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
