import OAI.Hierarchy.DescentOrdinaryPaletteGather

namespace OAI
/-! The old primitive, newborn, and origin repitches coexist with the real halo and literal gather tables. -/
namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSixParty.Chronology
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {w : ℕ} (L : Layout) (base : ℕ) (B : L.Inputs)
local notation "H" => L.hosts
local notation "O" => L.oldGroups
local notation "M" => L.oldWork
local notation "P" => L.ports
local notation "u" => L.birthStart base
local notation "v" => L.originStart base
local notation "h₀" => L.portStart base
local notation "j₀" => L.bookStart base
local notation "s₀" => L.spreadStart base
local notation "dict" => L.references j₀
local notation "roster" => DescentScalarHaloPortROM.chart H O M P h₀ B.halo

theorem head_read (e : L.Early base B w) (cap : L.Capacity B) (S : L.Stock)
    (m : Memory w) (seen : L.Observed B S m) (space : s₀<2^w) :
    let out:=(L.head base B w).image m
    Source (L.pool base B) S.pool M out ∧
    ∀x,Reads (L.origins.bank v x) (S.origin x) L.workLanes out:=by
  intro o
  obtain ⟨bu,uv,vh,hj,js,_,_,_⟩:=L.cuts base
  have jroom:=js.trans_lt space
  have hroom:=hj.trans_lt jroom
  have vroom:=vh.trans_lt hroom
  have uroom:=uv.trans_lt vroom
  let m₁:=(L.prior.phase base B.previous w).image m
  let m₂:=(L.births.phase u B.newborn w).image m₁
  let m₃:=(L.origins.phase v B.origin w).image m₂
  let m₄:=(L.portPhase base w).image m₃
  have F₁:=L.prior.any base B.previous m e.old uroom
  have F₂:=L.births.any u B.newborn m₁ (fun x=>widen bu (e.births x)) vroom
  have F₃:=L.origins.any v B.origin m₂ (fun x=>widen (bu.trans uv) (e.origin x)) hroom
  have F₄:=DescentScalarHaloPortROM.mount H O M P h₀ B.halo m₃
    (show h₀+DescentScalarHaloPortROM.length H O M P<2^w from (Nat.le_add_right ..).trans_lt jroom)
  have F₅:=(dict).any m₄ space
  have from₄ (a : ℕ) (ha : a<j₀) : o a=m₄ a:=F₅.2.2.2 a (.inl ha)
  have from₃ (a : ℕ) (ha : a<h₀) : o a=m₃ a:=(from₄ a (ha.trans_le hj)).trans (F₄.2.2.1 a (.inl ha))
  have from₂ (a : ℕ) (ha : a<v) : o a=m₂ a:=(from₃ a (ha.trans_le vh)).trans (F₃.2 a (.inl ha))
  have from₁ (a : ℕ) (ha : a<u) : o a=m₁ a:=(from₂ a (ha.trans_le uv)).trans (F₂.2 a (.inl ha))
  have orig (a : ℕ) (ha : a<base) : o a=m a:=(from₁ a (ha.trans_le bu)).trans (F₁.2 a (.inl ha))
  have rd₁ (x) : Reads (L.prior.bank base x) (S.previous x) M o:=
    carry_reads (L.prior.placed base uroom x).1 (L.prior.placed base uroom x).2 from₁
      (L.prior.reads base B.previous m e.old uroom x _ cap.prior_live (cap.past x) (seen.past x))
  have mid₁ (a : ℕ) (ha : a<base) : m₁ a=m a:=F₁.2 a (.inl ha)
  have mid₂ (a : ℕ) (ha : a<base) : m₂ a=m a:=(F₂.2 a (.inl (ha.trans_le bu))).trans (mid₁ a ha)
  have rd₂ (x) : Reads (L.births.bank u x) (S.newborn x) M o:=
    carry_reads (L.births.placed u vroom x).1 (L.births.placed u vroom x).2 from₂
      (L.births.reads u B.newborn m₁ (fun x=>widen bu (e.births x)) vroom x _ cap.birth_live (cap.born x)
        (carry_reads (e.births x) (cap.born x) mid₁ (seen.born x)))
  have rd₃ (x) : Reads (L.origins.bank v x) (S.origin x) L.workLanes o:=
    carry_reads (L.origins.placed v hroom x).1 (L.origins.placed v hroom x).2 from₃
      (L.origins.reads v B.origin m₂ (fun x=>widen (bu.trans uv) (e.origin x)) hroom x _ cap.origin_live (cap.origin x)
        (carry_reads (e.origin x) (cap.origin x) mid₂ (seen.origin x)))
  have fits:=DescentScalarHaloPortROM.statics H O M P h₀ j₀ B.halo le_rfl jroom
  have shape:=F₄.2.1
  have wired : Mounted roster S.next o O M:=by
    refine ⟨fun z i=>(from₄ _ (before_bank (fits.1 i).1 (row H O M z) (fits.1 i).2)).trans (shape.ids i z),?_,
      fun h=>(from₄ _ (before_bank fits.2.1.1 h fits.2.1.2)).trans (shape.offsets h),
      fun z=>(from₄ _ (before_bank fits.2.2.1.1 (row H O M z) fits.2.2.1.2)).trans (shape.chunks z)⟩
    intro h i
    have at_:=before_bank e.halo (finProdFinEquiv (h,i)) e.slots
    have inside : (roster).roster.base + (h.val * P + i.val) < base := by
      change B.halo.base + (h.val * P + i.val) < base
      simpa only [finProdFinEquiv_apply_val, Nat.mul_comm P h.val, Nat.add_comm i.val (h.val * P)] using at_
    exact (orig _ inside).trans (seen.halo h i)
  exact ⟨L.field_sources base B o e S space wired rd₁ rd₂ ((dict).issued m₄),rd₃⟩


end
end Hierarchy.DescentOrdinaryPrimitiveCheckpoint.Layout

end OAI
