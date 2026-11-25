import OAI.Hierarchy.ProtocolRAMStripNativeCost

namespace OAI
/-! # Address safety of the complete native mixed-role edge reader -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage CoreBoard AdaptiveProbe BoughtSockets PurchaseFrozen
variable {z W k depth attempts w limit : ℕ} {S : PurchaseSampler} {C H A B : Type*}

theorem core_bank_fits (base : ℕ) (kind : CoreLookup.Channel S.degree (Stages z (2^W)) k)
    (room : limit<2^w) (high : base+CoreLookup.words S z (2^W) k≤limit) :
    (CoreLookup.bank (S:=S) (h:=z) (d:=2^W) base kind).Fits w limit := by
  let stride:=CoreLookup.stride z (2^W)
  let idx:=(Fintype.equivFin _) kind
  have upper:=Nat.mul_le_mul_right stride idx.isLt
  rw [Nat.succ_mul] at upper
  change base+Fintype.card (CoreLookup.Channel S.degree (Stages z (2^W)) k)*stride≤limit at high
  have stop : base+idx.val*stride+stride≤limit := by omega
  exact ⟨Nat.two_pow_pos _,by change stride<2^w;omega,stop⟩

private theorem StripPorts.primary_fits (p : StripPorts S z (2^W) k C H B) (b : Board)
    (room : limit<2^w) (high : p.directory+CoreLookup.words S z (2^W) k≤limit)
    (cells : ∀c,(p.column c).Fits w limit) (hor : ∀i l,(p.horizontal i l).Fits w limit)
    (probe : ∀i,(p.probe i).Fits w limit) (e : ColumnWires.Role C H (A⊕B) k) :
    (p.primary b e).Fits w limit := by
  have safe (x : Expr) (ok : x.Fits w limit) : (b.coreOnly x).Fits w limit := ⟨ok,trivial,ok,trivial⟩
  cases e with
  | catalyst c axis => exact safe _ ⟨core_bank_fits _ _ room high,cells c⟩
  | radius c axis side => exact safe _ ⟨core_bank_fits _ _ room high,cells c⟩
  | cross c axes s t => exact safe _ ⟨core_bank_fits _ _ room high,cells c⟩
  | horizontal i l => exact safe _ (hor i l)
  | extra i => rcases i with a|q
               · trivial
               · exact probe q

theorem payload_fits_local (b : Board) (v : Directory attempts) (S : PurchaseSampler) (directory col _depth K G H : ℕ)
    (room : limit<2^w) (core : directory+CoreLookup.words S z (2^W) k≤limit)
    (tab : col+ColumnROM.words z (2^W) k≤limit) (cover : ColumnROM.Cover z W v.remapBase v.sitesBase v.superBase K G H limit)
    (i : Fin (Fintype.card (StripDirectory.PayloadRole (Stages z (2^W)) k))) :
    (payloadEdge (payloadPorts S directory col v.remapBase v.sitesBase v.superBase K G H z W k attempts) b i).Fits w limit := by
  let p:=payloadPorts S directory col v.remapBase v.sitesBase v.superBase K G H z W k attempts
  have cells (c) : (p.column c).Fits w limit := ColumnROM.payload_fits_cols col v.remapBase v.sitesBase v.superBase K G H limit (payloadChoice z W c) room tab cover
  apply p.primary_fits b room core cells _ (fun u=>u.elim)
  intro h l
  change (payloadHorizontal S z (2^W) k directory p.column h l).Fits w limit
  unfold payloadHorizontal
  split
  · exact ⟨core_bank_fits _ _ room core,cells _⟩
  · exact ⟨core_bank_fits _ _ room core,trivial⟩

theorem payload_fits (b : Board) (v : Directory attempts) (S : PurchaseSampler) (directory col depth K G H : ℕ)
    (room : limit<2^w) (core : directory+CoreLookup.words S z (2^W) k≤limit)
    (tab : col+ColumnROM.words z (2^W) k≤limit) (cover : v.Cover S z W k depth K G H limit)
    (i : Fin (Fintype.card (StripDirectory.PayloadRole (Stages z (2^W)) k))) :
    (payloadEdge (payloadPorts S directory col v.remapBase v.sitesBase v.superBase K G H z W k attempts) b i).Fits w limit :=
  payload_fits_local b v S directory col depth K G H room core tab cover.columns i

theorem purchase_fits_local (b : Board) (v : Directory attempts) (sh : Shelf) (birth : ℕ) (S : PurchaseSampler)
    (directory col depth K G H : ℕ) (room : limit<2^w) (core : directory+CoreLookup.words S z (2^W) k≤limit)
    (tab : col+ColumnROM.words z (2^W) k≤limit) (cover : ColumnROM.Cover z W v.remapBase v.sitesBase v.superBase K G H limit)
    (keys : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).stop≤limit)
    (slab : ∀i : Key z (2^W) k,(sh.L S depth i).endAddress≤limit)
    (i : Fin (Fintype.card (StripDirectory.PurchasedRole depth k))) :
    (purchaseEdge (purchasePorts b v sh S directory col v.keysBase K G H z W k depth birth) b i).Fits w limit := by
  let p:=purchasePorts b v sh S directory col v.keysBase K G H z W k depth birth
  let head:=StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase
  have fitting (bank : Bank) (hu : bank.base+bank.size≤limit) : bank.Fits w limit :=
    ⟨Nat.two_pow_pos _,by omega,hu⟩
  have cells (c) : (p.column c).Fits w limit := by
    apply select_fits _ _ room keys
    intro i
    apply ColumnROM.stage_fits_cols col v.remapBase v.sitesBase v.superBase K G H limit _ _ _ room tab cover
    let L:=sh.L S depth i
    have ⟨_,_,_,_,_,so,g,pa,t⟩:=L.regions
    have stop : L.endAddress≤limit:=slab i
    exact ⟨fitting L.source (by omega),trivial,trivial⟩
  apply p.primary_fits b room core cells _ (fun _=>⟨trivial,trivial⟩)
  have position (j : Fin (depth+1)) : (rowKey sh S head z (2^W) k depth j).Fits w limit := by
    apply select_fits _ _ room keys
    intro i
    let L:=sh.L S depth i
    have ⟨_,_,_,_,_,s,g,p,t⟩:=L.regions
    have stop : L.endAddress≤limit:=slab i
    exact ⟨fitting L.source (by omega),trivial,trivial⟩
  have step (j : Fin depth) : (digitKey sh S head z (2^W) k depth j).Fits w limit := by
    apply select_fits _ _ room keys
    intro i
    let L:=sh.L S depth i
    have ⟨_,ids,mark,owner,scatter,s,g,p,t⟩:=L.regions
    have stop : L.endAddress≤limit:=slab i
    have endDigit:=Nat.mul_le_mul_right (PurchaseDirectory.span (2^z) S.degree depth) (Nat.add_le_add_right j.isLt 1)
    rw [Nat.succ_mul] at endDigit
    have directoryEnd : L.directory+(depth+1)*PurchaseDirectory.span (2^z) S.degree depth=L.signed.base:=ids
    refine ⟨fitting _ ?_,trivial⟩
    change L.directory+(j.val+1)*PurchaseDirectory.span (2^z) S.degree depth+PurchaseDirectory.span (2^z) S.degree depth≤limit
    omega
  intro i l
  change (chainHorizontal sh S z (2^W) k depth directory v.keysBase p.column i l).Fits w limit
  unfold chainHorizontal
  split
  · refine choose_fits_bound _ _ _ _ ?_ ?_
    · intro t
      exact ⟨core_bank_fits _ _ room core,position _⟩
    · exact select_fits head _ room keys (fun _=>trivial)
  · refine choose_fits_bound _ _ _ _ ?_ (step _)
    intro digit
    exact ⟨core_bank_fits _ _ room core,cells _⟩

theorem purchase_fits (b : Board) (v : Directory attempts) (a : Fin attempts) (S : PurchaseSampler)
    (directory col depth K G H : ℕ) (room : limit<2^w) (core : directory+CoreLookup.words S z (2^W) k≤limit)
    (tab : col+ColumnROM.words z (2^W) k≤limit) (cover : v.Cover S z W k depth K G H limit)
    (i : Fin (Fintype.card (StripDirectory.PurchasedRole depth k))) :
    (purchaseEdge (purchasePorts b v (v.shelf a) S directory col v.keysBase K G H z W k depth a.val) b i).Fits w limit :=
  purchase_fits_local b v (v.shelf a) a.val S directory col depth K G H room core tab cover.columns cover.keys (cover.source a) i

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
