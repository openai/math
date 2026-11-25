import OAI.Hierarchy.ProbeFixedStripFunds
import OAI.Hierarchy.ProbeNativeBatchFunds

namespace OAI
/-! # A genuine affirmative menu lookup funds the native raw ballot before its mask is applied -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive.StripInput
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram StripDirectory
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing
variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N w q D z d : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H → ℝ} {cap : A → ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "req" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "demands" => (C × Fin k) ⊕ A
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap
variable {e : Role C H (A⊕B) k → Chord sites}
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}
variable (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput
    (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)
local notation "ports" => (Fintype.equivFin Roles).symm
local notation "old" => x.form.stockSource.old
local notation "channels" => (⟨x.addr,account id,x.active⟩ : Channels A Roles)
local notation "test" => tested {x.board.test with live:=x.active,rows:=x.raw.market.rows,population:=2^z}
  x.board.price (GlobalTests.offsets x.board.globalTests) old (channels).digit

omit [Nonempty (Fin k)] in
theorem affirmative_funded {J : Type*} [Fintype J] (widths : J → ℕ)
    (embed : menu.index→J) (sizes : ∀j,widths (embed j)=(menu.packet j).width)
    (ph : PhasePrice) (K : ℕ) (γ : ℝ) (lane : A→ℕ)
    (positive : 0<ph.a) (time : 0<ph.time) (bonus : ∀ l,0≤ph.bonus l) (Mpos : 0≤ph.M)
    (width : 0<ph.bits) (kpos : 0<K) (large : 2*(K*commonWidth widths)≤ph.bits)
    (margin : 0≤γ) (below : γ≤ menu.margin) (arity : (Fintype.card demands:ℝ)/K≤ph.time*ph.a*γ)
    (copies : x.board.copies=ph.bits/(K*commonWidth widths))
    (state : Memory w) (r : Word w) (grid : A→ℝ)
    (legal : quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid)∈prices)
    (failed : ε≤Probe.discrepancy F e req (quote M len (LocalCommodity.extraPrice (B:=B) grid)))
    (lookup : let i:=menu.select ⟨_,legal,failed⟩
      x.ballot.packet.eval state r=(((Fintype.equivFin menu.index i).val+1:ℕ):Word w))
    (priceOK : ∀a,grid a≤ph.quote (lane a) ((old).read state ((x.addr a).eval state r)).val) :
    x.ballot.packet.eval state r≠0 ∧
      ∀t,((x.ballot.need t).eval state r).val ≤ ((x.ballot.stock t).eval state r).val := by
  let paint:=quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid)
  let i:=menu.select ⟨paint,legal,failed⟩
  let K₀:=ph.bits/(K*commonWidth widths)
  let build (m : ℕ):=StripDirectory.batch (q:=q) menu test x.board.terms x.board.menu x.board.enabled x.board.selectors old .row m
    x.board.maxWidth ports x.slots
  have cap:=x.codeFit
  have inc:=(Fintype.equivFin menu.index i).isLt
  have number : (Fintype.equivFin menu.index i).val+1<2^w:=by omega
  have read : (x.ballot.packet.eval state r).val=(Fintype.equivFin menu.index i).val+1 :=
    (congrArg Fin.val lookup).trans (Fin.val_cast_of_lt number)
  have real : (build K₀).packet.eval state r=x.ballot.packet.eval state r:=rfl
  let laneAt (h : Fin (Fintype.card Roles)) := ((account id (ports h) : Option A).map lane).getD 0
  have fits : K₀*x.board.maxWidth<2^w := by
    change ph.bits/(K*commonWidth widths)*x.board.maxWidth<2^w
    rw [←copies]
    exact x.wide
  have ok := batch_funded (q:=q) menu test x.board.terms x.board.menu x.board.enabled x.board.selectors old .row
    x.board.maxWidth ports x.slots state r paint legal failed widths embed sizes ph laneAt K (Fintype.card demands) positive
    time (fun h=>bonus (laneAt h)) Mpos width kpos large margin below le_rfl arity x.codeFit x.fieldFit fits
    ((congrArg Fin.val real).trans read)
    (fun h=>(cap_debit menu i (ports h)).trans (((PacketWidths.ofMenu menu).maximum_ge i).trans x.maximum))
  have lowered : ∀h addr,x.slots h=some addr → paint (ports h)≤ph.quote (laneAt h) ((old).read state (addr.eval state r)).val := by
    intro h addr hit
    change (account id (ports h)).map x.addr=some addr at hit
    obtain ⟨a,who,rfl⟩:=Option.map_eq_some_iff.mp hit
    have honest : ports h=Role.extra (.inl a) := by
      generalize ports h=z₀ at who ⊢
      cases z₀ with
      | extra u => cases u <;> simp_all [account]
      | catalyst | radius | cross | horizontal => simp [account] at who
    dsimp only [laneAt]
    rw [honest]
    exact priceOK a
  have credit := ok lowered
  have saved : ∀h,(((build x.board.copies).need h).eval state r).val≤(((build x.board.copies).stock h).eval state r).val := by
    rw [copies]
    exact credit
  refine ⟨?_,?_⟩
  · intro zero
    rw [zero] at read
    change 0=(Fintype.equivFin menu.index i).val+1 at read
    omega
  · change ∀h,(((PortPadding.batch D (build x.board.copies)).need h).eval state r).val≤
      (((PortPadding.batch D (build x.board.copies)).stock h).eval state r).val
    intro h
    by_cases inside : h.val<Fintype.card Roles
    · let j : Fin (Fintype.card Roles):=⟨h.val,inside⟩
      have eq : h=PortPadding.inject x.ports j:=Fin.ext rfl
      rw [eq,PortPadding.real_need (build x.board.copies) x.ports j]
      simpa only [PortPadding.batch,PortPadding.extend_real] using saved j
    · rw [PortPadding.tail_need _ state r h (Nat.le_of_not_gt inside) x.fieldFit]
      exact Nat.zero_le _

end Hierarchy.ProtocolRAM.CatalystArchive.StripInput
end

end OAI
