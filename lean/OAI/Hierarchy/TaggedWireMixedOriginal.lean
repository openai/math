import OAI.Hierarchy.TaggedWireOriginalPublicRead
import OAI.Hierarchy.TaggedWireRoleRoomNative
import OAI.Hierarchy.TaggedWireSettledLayout

namespace OAI
/-! # Mixed original terminal operands from the real CT rows, public ROM and live paid rows -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom
open AdaptiveProbe WireTelescope ReportSockets ProtocolRAM Calendar TaggedShorterSupergroups
open ThreeFlat.RAM DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w h W k H attempts depth M R edges : ℕ} (S : PurchaseSampler)
    (order : Fin R≃Edges S h (2^W) k) (dir : Directory (reserved h W (copies k attempts)) H)
local notation "z" => shape (R:=R) S dir edges
local notation "N" => Fintype.card (Old h W k edges)

theorem resident_meta (start : ℕ) (m : Memory w) (resident : (tables S order dir edges).Resident start m)
    (room : N≤2^w) (field : Fin 7) (i : Fin N) :
    («meta» start N field).eval m (i.val:Word w)=(metadataTable S order attempts edges field i:Word w) := by
  apply RoleROM.read _ .row _ i room rfl
  intro j
  have cell:=resident.meta (finProdFinEquiv (field,j))
  change m (start+(finProdFinEquiv (field,j)).val)=
    (metadataTable S order attempts edges (finProdFinEquiv.symm (finProdFinEquiv (field,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (field,j))).2 : Word w) at cell
  rw [Equiv.symm_apply_apply] at cell
  have addr : start+field.val*N+j.val=start+(finProdFinEquiv (field,j)).val := by
    change start+field.val*N+j.val=start+(j.val+N*field.val)
    ac_rfl
  change m (start+field.val*N+j.val)=_
  rw [addr]
  exact cell

theorem mixed_original (π : Equiv.Perm (Fin (2^h))) (start : ℕ) (m : Memory w)
    (resident : (tables S order dir edges).Resident start m) (oldRoom : N≤2^w)
    (core : CatalogueRows.CoreSource) (ct : CoreCatalogue.Rows core order dir π M m)
    (wide : 4≤2^w) (sites : siteLast h (2^W) k+1≤2^w)
    («public» : Fintype.card (Public S h W k attempts)≤2^w)
    (rowRoom : 2^h≤2^w) (axisRoom : (siteLast h (2^W) k+1)*(2*k)≤2^w)
    (perm : ∀j:Fin (2^h),m j.val=((π j).val:Word w))
    (paid : Bool→Socket) (width fixed : Fin edges→ℕ) (stock : Goods h W k→ℕ) (reserved used : Catalysts h W k→ℕ)
    (enough : ∀j,fixed j≤width j) (pos : ∀j,0<width j→Bool→PaidPorts S h W k attempts)
    (sockets : ∀j hi side,Resolved S ((z).chart start) (paid side) m (j.val:Word w) (.inl (pos j hi side)))
    (i : Fin N) (on : 0<SettledMatrix.Layout.bits fixed stock reserved used i) (side : Bool) :
    Resolved S ((z).chart start) (originalInputs ((z).chart start) start N ((z).ext start) ((z).axis start) h W k core paid side)
      m (i.val:Word w) (publicRoleFor S π (activePaid S width pos) (SettledMatrix.Layout.numbered (r:=edges) i) side) := by
  refine original_public S ((z).chart start) order π m start ((z).ext start) ((z).axis start) core paid (activePaid S width pos) i side
    (fun j=>resident_meta S order dir start m resident oldRoom j i) sites wide rfl «public» resident.site resident.code
    ?_ perm rowRoom resident.exterior resident.signed axisRoom ?_
  · intro j old s
    have active:0<fixed j:=by simpa only [SettledMatrix.Layout.bits,Function.comp_apply,old,SettledMatrix.Layout.available,Sum.elim_inl] using on
    have yes:=active.trans_le (enough j)
    rw [activePaid_pos S width pos j yes s]
    exact sockets j yes s
  · intro p t l s
    let j:=altRow S order p t l s
    have seen:=alt_site S core order M dir π m ct p t l s .row (j.val:Word w) rfl
    simpa only [altSite,eval_atRow,Expr.eval,j] using seen

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram.RoleRoom

end
end OAI
