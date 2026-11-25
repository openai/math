import OAI.Hierarchy.TaggedWideCalendarPinGeometry
import OAI.Hierarchy.TaggedWireSiteBits
import OAI.Hierarchy.TaggedWideNamedWidths

namespace OAI
/-! # The intermediate local state mask on the real dated role directory -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.LedgerStep
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open Tagged WideStack WidePadding WideControlJoin WireTelescope WireTelescope.CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical

variable {K N : ℕ} {Bits : Fin K→Type} (chart : (Σs,Bits s) ↪ Fin K×Fin N)
    (atSite : ∀s (u : Bits s),(chart ⟨s,u⟩).1=s)

/-- Restrict the original chart to one physical site, dropping its fixed
site coordinate. This keeps the same per-role ordinal and bit position. -/
def siteChart (s : Fin K) : Bits s ↪ Fin N where
  toFun u:=(chart ⟨s,u⟩).2
  inj' a b eqn:=by
    have pair : chart ⟨s,a⟩=chart ⟨s,b⟩ :=
      Prod.ext ((atSite s a).trans (atSite s b).symm) eqn
    exact eq_of_heq (Sigma.ext_iff.mp (chart.injective pair)).2

theorem siteChart_range (s : Fin K) (i : Fin N) :
    i∈Set.range (siteChart chart atSite s) ↔ (s,i)∈Set.range chart := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨⟨s,a⟩,Prod.ext (atSite s a) rfl⟩
  · rintro ⟨⟨u,a⟩,hit⟩
    have siteEq : u=s:=(atSite u a).symm.trans (congrArg Prod.fst hit)
    subst u
    exact ⟨a,congrArg Prod.snd hit⟩

/-- Embed every real dated role, with its own capacity, into the fixed-size
local directory. Original role, ordinal and digit are all retained. -/
def rolesChart {R : Type} {sites deg cap : ℕ} (capacity : R→ℕ) (within : ∀r,capacity r≤cap)
    (socket : R↪Fin (sites*deg)) : ((r:R)×Fin (capacity r)) ↪ Fin sites×Fin (deg*cap) where
  toFun a:=let z:=(finProdFinEquiv : Fin sites×Fin deg≃_).symm (socket a.1)
           (z.1,finProdFinEquiv (z.2,a.2.castLE (within a.1)))
  inj' := by
    rintro ⟨r,i⟩ ⟨u,j⟩ same
    have siteEq:=congrArg Prod.fst same
    have digitEq:=finProdFinEquiv.injective (congrArg Prod.snd same)
    have rankEq:=congrArg Prod.fst digitEq
    have sameRole : r=u:=socket.injective (finProdFinEquiv.symm.injective (Prod.ext siteEq rankEq))
    subst u
    exact Sigma.ext rfl (heq_of_eq (Fin.ext (congrArg (fun z=>z.2.val) digitEq)))

/-- Project the verified global role-table occupancy into the exact site
mask. Vacant native role rows are handled by the native zero setting. -/
theorem rolesChart_occupied {R X : Type} {sites deg cap : ℕ} (capacity : R→ℕ) (within : ∀r,capacity r≤cap)
    (socket : R↪Fin (sites*deg)) (cells : X↪((r:R)×Fin (capacity r)))
    (quantity : Fin sites×Fin deg→ℕ)
    (live : ∀r,quantity (finProdFinEquiv.symm (socket r))≤capacity r)
    (vacant : ∀z,finProdFinEquiv z∉Set.range socket→quantity z=0)
    (occupied : ∀a:((r:R)×Fin (capacity r)),a∈Set.range cells ↔ a.2.val<quantity (finProdFinEquiv.symm (socket a.1)))
    (s : Fin sites) (i : Fin (deg*cap)) :
    (s,i)∈Set.range (cells.trans (rolesChart capacity within socket)) ↔
      (finProdFinEquiv.symm i).2.val<quantity (s,(finProdFinEquiv.symm i).1) := by
  obtain ⟨⟨q,bit⟩,rfl⟩ := (finProdFinEquiv : Fin deg×Fin cap≃_).surjective i
  simp only [Equiv.symm_apply_apply]
  constructor
  · rintro ⟨x,hit⟩
    rcases h:cells x with ⟨r,d⟩
    change (rolesChart capacity within socket) (cells x) = _ at hit
    rw [h] at hit
    change ((finProdFinEquiv.symm (socket r)).1,
      finProdFinEquiv ((finProdFinEquiv.symm (socket r)).2, d.castLE (within r))) =
      (s, finProdFinEquiv (q,bit)) at hit
    have atSite:=congrArg Prod.fst hit
    have atSlot:=finProdFinEquiv.injective (congrArg Prod.snd hit)
    have loc : finProdFinEquiv.symm (socket r)=(s,q):=Prod.ext atSite (congrArg Prod.fst atSlot)
    have low:=(occupied ⟨r,d⟩).mp ⟨x,h⟩
    have eqn : d.val=bit.val:=congrArg (fun z=>z.2.val) atSlot
    simpa only [loc,eqn] using low
  · intro positive
    have existsRole : finProdFinEquiv (s,q)∈Set.range socket := by
      by_contra missing
      have zero:=vacant (s,q) missing
      omega
    obtain ⟨r,eqn⟩:=existsRole
    have loc : finProdFinEquiv.symm (socket r)=(s,q) := by rw [eqn,Equiv.symm_apply_apply]
    have lo : bit.val<capacity r:=positive.trans_le (loc ▸ live r)
    let d : Fin (capacity r):=⟨bit.val,lo⟩
    obtain ⟨x,hx⟩:=(occupied ⟨r,d⟩).mpr (by simpa only [loc] using positive)
    refine ⟨x,?_⟩
    change rolesChart capacity within socket (cells x) = _
    rw [hx]
    change ((finProdFinEquiv.symm (socket r)).1,
      finProdFinEquiv ((finProdFinEquiv.symm (socket r)).2,d.castLE (within r))) = _
    rw [loc]
    rfl

variable {F Ex Sel D : Type} [Field F] [Fintype Ex] [Fintype Sel] [Fintype D] (G : Gate)
    {deg cap digits : ℕ} (capFits : cap≤2^digits) (address : Fin deg→ℕ)
local notation "V" => SitePins Ex Sel D G
local notation "mid" => Fin (deg*cap)
local notation "part" => (finProdFinEquiv : Fin deg×Fin cap≃mid)

/-- A valid middle word has no high digit in any local role. Width bits are
literal reads of the shared paid CPU's immediate post-attempt width table. -/
def midPorts : Ports ((V⊕mid)⊕Bool) (deg*cap) digits where
  col i:=((part).symm i).2.castLE capFits
  live _:=.inr true
  width i b:=Sum.map Sum.inl id (G.shelfBit (address ((part).symm i).1,b.val))
  payload i:=.inl (.inr i)

def midGuard : BitNetwork F (Fintype.card (V⊕mid)) :=
  WideHost.localFamily (fun _ : Unit=>(midPorts G capFits address).network (F:=F)) (fun _ p=>p)

theorem mid_cost :
    let net:=midGuard (F:=F) (Ex:=Ex) (Sel:=Sel) (D:=D) G capFits address
    net.cells+net.internal≤(deg*cap)*(200*digits+65) := by
  intro net
  rw [show net.cells+net.internal=_ from WideHost.localFamily_size ..]
  simpa using (midPorts (Ex:=Ex) (Sel:=Sel) (D:=D) G capFits address).cost (F:=F)

variable (out : Memory G.W) (ext : Ex→Bool) (sel : Sel→Bool) (data : D→Bool)
    (dense : ∀i : Fin G.u,(G.addr i).val=i.val) (inside : ∀q,address q<G.u)
local notation "v" => Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))

include dense inside in
theorem mid_value {A : Widths K} (s : Fin K)
    (layout : (Σp,SiteBit A p) ↪ Fin K×mid) (site : ∀t u,(layout ⟨t,u⟩).1=t)
    (strict : ∀q,(out (address q)).val<2^digits)
    (published : ∀i:mid,(s,i)∈Set.range layout ↔ ((part).symm i).2.val<(out (address ((part).symm i).1)).val)
    (z : mid→Bool) :
    TypedWiring.value (midGuard (F:=F) G capFits address) (Sum.elim v z)=
      if ∀i,z i=true→i∈Set.range (siteChart layout site s) then 1 else 0 := by
  let width:mid→Word digits:=fun i=>⟨(out (address ((part).symm i).1)).val,strict _⟩
  rw [midGuard,WideHost.localFamily_eval,Fintype.prod_unique]
  have read (i : mid) (b : Fin digits) :
      Sum.elim (Sum.elim v z) id ((midPorts G capFits address).width i b)=bits (width i) b := by
    let field:=G.shelfBit (E:=Ex) (Q:=Sel) (D:=D) (address ((part).symm i).1,b.val)
    have eqn:=G.shelfBit_read dense out ext sel data (address ((part).symm i).1) b.val (inside ((part).symm i).1)
    change Sum.elim (Sum.elim v z) id (Sum.map Sum.inl id field)=_
    have lift : Sum.elim (Sum.elim v z) id (Sum.map Sum.inl id field)=Sum.elim v id field := by cases field <;>rfl
    exact lift.trans eqn
  change TypedWiring.value ((midPorts (Ex:=Ex) (Sel:=Sel) (D:=D) G capFits address).network (F:=F)) (Sum.elim (Sum.elim v z) id) = _
  rw [Ports.eval _ _ width read]
  have hit (i : mid) : i∈Set.range (siteChart layout site s) ↔
      ((part).symm i).2.val<(out (address ((part).symm i).1)).val :=
    (siteChart_range layout site s i).trans (published i)
  change (if ∀i,z i=true→true=true ∧ ((part).symm i).2.val<(out (address ((part).symm i).1)).val then (1:F) else 0)=_
  simp only [true_and,hit]


end Hierarchy.ProbeStage.CoreBoard.LedgerStep

end
end OAI
