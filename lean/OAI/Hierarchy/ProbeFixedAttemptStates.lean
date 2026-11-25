import OAI.Hierarchy.ProbeFixedNativeBoards
import OAI.Hierarchy.ProbeFixedTerminalCash
import OAI.Hierarchy.ProbeFailedCoordinates
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime

namespace OAI
/-! # Word-address reads supplying the stock endpoints of each actual failed trial -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory
open scoped Classical Fin.CommRing
variable {r edges q₁ d₁ : ℕ} {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
  (bills : Event→WordRows)

def nativeAccount := v.account (v.privateArena P z width) (v.nativeFormats P z width) P.joint.initial width bills

theorem stock_pointer (a : Attempt) (i : Commodity (Fin (2^z)) (Stages z (2^v.W)) k) :
    (v.nativeAccount P z width bills).stockAt a i=
      (v.nativeFormats P z width a).stockSource.old.base+PurchaseInventory.slot i :=
  live F v.mesh (v.privateArena P z width) P.joint.initial (v.nativeBoards P z width) a i

theorem stock_goods (a : Attempt) :
    (v.nativeFormats P z width a).pricedArea.goods=PurchaseInventory.footprint z (Stages z (2^v.W)) k := by
  cases a <;> rfl

def nativeSlots (a : Attempt) :
    Commodity (Fin (2^z)) (Stages z (2^v.W)) k ≃ Fin (v.nativeFormats P z width a).pricedArea.goods :=
  (PurchaseInventory.slotEquiv z (Stages z (2^v.W)) k).trans (finCongr (v.stock_goods P z width a).symm)

theorem slot_index (a : Attempt) (i : Commodity (Fin (2^z)) (Stages z (2^v.W)) k) :
    (v.nativeSlots P z width a i).val=PurchaseInventory.slot i := rfl

theorem read_input (a : Attempt) (sink : Sink r edges) (idBase : ℕ) (role : Expr)
    (ids : Fin (max (Fintype.card (PayloadRole (Stages z (2^v.W)) k))
      (Fintype.card (PurchasedRole v.depth k)))→Expr) (C : Chart (wordBits z (2^v.W) copies) q₁ d₁)
    (m : Memory (wordBits z (2^v.W) copies)) :
    let f:=v.nativeFormats P z width a
    let g:=f.labelSource sink idBase role ids
    let s:=fresh f.pricedArea f.stockSource
    let old:=PurchaseStage.postOutput (C.layout a) (repair C a) (prepared C a m)
    let mi:=stageInput f.pricedArea f.stockSource g old
    let A:=v.nativeAccount P z width bills
    ready C (.attempt a) m → (∀i,protected C (A.stockAt a i) (.attempt a)) →
    f.pricedArea.goods≤2^wordBits z (2^v.W) copies → f.pricedArea.goods≤f.stockSource.old.size →
    f.stockSource.old.base+f.pricedArea.goods≤g.out →
    ∀ j : Fin s.goods,((A.bank.coordinates (v.nativeSlots P z width a)).stock (A.read a m) j)=
      (mi (s.plan.bank.base+j.val)).val := by
  intro f g s old mi A ok kept room span below j
  let e:=v.nativeSlots P z width a
  let i:=e.symm j
  have ix : PurchaseInventory.slot i=j.val:=by
    rw [←v.slot_index P z width a i]
    exact congrArg Fin.val (e.apply_symm_apply j)
  have actual : mi (f.pricedArea.start+j.val)=old (f.stockSource.old.base+j.val) :=
    (f.pricedArea.seed_read f.stockSource _ j room span).trans
      (ProtocolRAMGeneratedWrite.frame_image g.out f.pricedArea.occurrences ((g.geometry 5).atRow g.edge)
        old (f.stockSource.old.base+j.val) (.inl ((Nat.add_lt_add_left (show j.val < f.pricedArea.goods from j.isLt) _).trans_le below)))
  have keep:=postOutput_prior C a m (A.stockAt a i) ok (kept i)
  change (m (A.stockAt a i)).val=(mi (f.pricedArea.start+j.val)).val
  rw [←keep,v.stock_pointer P z width bills a i,ix]
  exact congrArg Fin.val actual.symm

theorem outer_output (r : ℕ) (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
    (m : Memory (wordBits z (2^v.W) copies)) (p h : ℕ) (hp : p<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) :
    let C:=v.nativeChart P z width r banks src tab dest owners
    let A:=v.nativeAccount P z width bills
    let u:=Attempt.outer p h
    let f:=v.nativeFormats P z width u
    let out:=after C (.attempt u) (trialState C m p h)
    ∀j : Fin f.pricedArea.goods,((A.bank.coordinates (v.nativeSlots P z width u)).stock (A.inner C m p h 0 0) j)=
      (out (f.pricedArea.output+j.val)).val := by
  intro C A u f out j
  let e:=v.nativeSlots P z width u
  let i:=e.symm j
  have ix : PurchaseInventory.slot i=j.val:=by
    rw [←v.slot_index P z width u i];exact congrArg Fin.val (e.apply_symm_apply j)
  have addr:=stockAt_entry v.mesh (v.privateArena P z width) (v.nativeFormats P z width) P.joint.initial p h i hp hh
  change (out (stockAt v.mesh (v.privateArena P z width) (v.nativeFormats P z width) P.joint.initial (.inner p h 0 0) i)).val=_
  rw [addr,ix]

theorem inner_output (r : ℕ) (banks : RouteSettlement.Banks) (src tab dest : ℕ) (owners : Bank)
    (m : Memory (wordBits z (2^v.W) copies)) (p h j b : ℕ)
    (hp : p<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) (hj : j<v.mesh.reserveSteps) (hb : b<v.mesh.innerFuel) :
    let C:=v.nativeChart P z width r banks src tab dest owners
    let A:=v.nativeAccount P z width bills
    let u:=Attempt.inner p h j b
    let f:=v.nativeFormats P z width u
    let out:=after C (.attempt u) (innerState C m p h j b)
    ∀i : Fin f.pricedArea.goods,((A.bank.coordinates (v.nativeSlots P z width u)).stock (A.inner C m p h j (b+1)) i)=
      (out (f.pricedArea.output+i.val)).val := by
  intro C A u f out x
  let e:=v.nativeSlots P z width u
  let i:=e.symm x
  have ix : PurchaseInventory.slot i=x.val:=by
    rw [←v.slot_index P z width u i];exact congrArg Fin.val (e.apply_symm_apply x)
  have addr:=stockAt_inner_after v.mesh (v.privateArena P z width) (v.nativeFormats P z width)
    P.joint.initial p h j b i hp hh hj hb
  change ((innerState C m p h j (b+1)) (stockAt v.mesh (v.privateArena P z width) (v.nativeFormats P z width)
    P.joint.initial (.inner p h j (b+1)) i)).val=_
  rw [inner_succ,addr,ix]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
