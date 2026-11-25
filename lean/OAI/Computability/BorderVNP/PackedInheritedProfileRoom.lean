import OAI.Computability.BorderVNP.PackedInheritedVirtualRead
import OAI.Computability.BorderVNP.PackedBankPacketLocality

/-! # Address bounds for the intrinsic profile birth packets

All occupied source ports are canonical virtual-cell incidence words, and the
site slab begins at zero. Terminal hook comparisons use one contiguous wire
and one clipped interval of the original terminal row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedProfile

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell Inherited BankSite BankJoint BankCircuit BankPacket CellSparse CellAddresses
open scoped Classical

private theorem end_room {D ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (v : N.Site) (aux : N.Site → ℕ) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (noloop : ∀ z : Incident N v, N.src z.val ≠ N.dst z.val) (z : N.Edge) (src : Bool)
    (hv : incidentSite N z src = v) (k : Fin (N.width z)) :
    cableBase N id aux edgeID portID z src+k.val < aux v + incoming N v := by
  subst v
  let u := incidentWire N z src
  change wireBase N id (incidentSite N z src) edgeID portID aux ⟨incidentSite N z src,rfl⟩ u + k.val < _
  rw [singleton_wire N _ aux edgeID portID noloop u,Nat.add_assoc]
  exact Nat.add_lt_add_left ((wireOrdinal N edgeID portID _ u k).symm.trans_lt
    (sourceOrder N edgeID portID _ (.inl ⟨u,k⟩)).isLt) _

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable (a : S)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "j₀" => blocks p.layout bin perm m a
local notation3 "v₀" => seedSite e p bin perm positive first q a
local notation3 "work₀" => workAt e p bin perm positive first q
local notation3 "raw₀" => raw e p bin perm positive first q a siteID edgeID portID
local notation3 "orig₀" => originSite e p bin perm positive first q a siteID edgeID portID
local notation3 "tape₀" => terminalWords e raw₀

omit [Fintype P] in
/-- The work prefix begins at zero for every true profile origin or terminal. -/
theorem profile_start (r : Unit ⊕ (Fin D × Bool)) :
    let v := v₀ (profileNode e r)
    siteBase G₀ id v siteID work₀ ⟨v,rfl⟩ = 0 :=
  singleton_start G₀ _ work₀ siteID (profile_empty e p bin perm positive first q a r)

/-- The origin spoke lies in the complete intrinsic bank at the origin. -/
theorem origin_room (t : Fin D × Bool) (i : Fin j₀) (k : Fin (Nat.clog 2 e.count)) :
    (physicalPort m (originWords e raw₀) (.inl t)).atBit i k < (orig₀).size := by
  let v := v₀ (.inl ())
  let z : (G₀).Edge := .inr (.inr ⟨a,.inl t⟩)
  change (⟨cableBase G₀ id work₀ edgeID portID z true,Nat.clog 2 e.count,1⟩ : Port).atBit i k < _
  rw [lane_add]
  exact end_room G₀ v work₀ edgeID portID (profile_noLoop e p bin perm positive first q a (.inl ())) z true
    rfl (finProdFinEquiv (i,k))

variable (binName : S → ℕ)
local notation3 "term₀" => terminalSite e p bin perm positive first q a siteID edgeID portID binName

/-- The terminal's canonical selector lies in the intrinsic bank. -/
theorem terminal_spoke_room (t : Fin D × Bool) (i : Fin j₀) (k : Fin (Nat.clog 2 e.count)) :
    (physicalPort m (tape₀ t) (.inr (.inl ()))).atBit i k < (term₀ t).size := by
  let v := v₀ (.inr (.inl t))
  let z : (G₀).Edge := .inr (.inr ⟨a,.inl t⟩)
  change (⟨cableBase G₀ id work₀ edgeID portID z false,Nat.clog 2 e.count,1⟩ : Port).atBit i k < _
  rw [lane_add]
  exact end_room G₀ v work₀ edgeID portID (profile_noLoop e p bin perm positive first q a (.inr t)) z false
    rfl (finProdFinEquiv (i,k))

/-- Every compact feeder bit of this terminal lies in its intrinsic bank. -/
theorem terminal_feeder_room (t : Fin D × Bool) (f : Fin e.count) (i : Fin ((q a).val f)) (k : Fin m) :
    (physicalPort m (tape₀ t) (.inr (.inr (.inr f)))).atBit i k < (term₀ t).size := by
  let v := v₀ (.inr (.inl t))
  let z : (G₀).Edge := .inr (.inr ⟨a,.inr (.inl (f,t))⟩)
  change (⟨cableBase G₀ id work₀ edgeID portID z true,m,1⟩ : Port).atBit i k < _
  rw [lane_add]
  exact end_room G₀ v work₀ edgeID portID (profile_noLoop e p bin perm positive first q a (.inr t)) z true
    rfl (finProdFinEquiv (i,k))

/-- At one terminal's selected old cable the clipped input comparisons access
only the finite original staging row and the true cable in the incoming array. -/
theorem hook_local (t : Fin D × Bool) (z : {z : p.layout.Edge // bin z = some (perm t.1 a)})
    (f g : ℕ → Bool) (same : ∀ i < (term₀ t).size, f i = g i) :
    let src := decide (positive z.val = t.2)
    let r := terminalHook e p bin perm positive first q a id work₀ siteID edgeID portID binName t.1 z src
    r.Valid [] f ↔ r.Valid [] g := by
  intro src r
  let v := v₀ (.inr (.inl t))
  let u := seedHook e p bin perm a t.1 z src
  let desc := descriptor p.layout bin perm m binName z (some (t.1,true))
  let L := terminalLayout j₀ m (q a).val
  let original := L.port (.inr (.inl ()))
  let dest := incidentSite G₀ u false
  let off := siteBase G₀ id dest siteID work₀ ⟨dest,rfl⟩
  let wire := cableBase G₀ id work₀ edgeID portID u false
  have hside : (if src then positive z.val else !(positive z.val)) = t.2 := by
    have pick (b s : Bool) : (if decide (b = s) then b else !b) = s := by cases b <;> cases s <;> decide
    exact pick _ _
  have hd : dest = v := (hook_fields e p bin perm positive first q binName a t.1 z src).2.1.trans <|
    congrArg (fun side => v₀ (.inr (.inl (t.1,side)))) hside
  have hzero : off = 0 := by
    have h := congrArg (fun w => siteBase G₀ id w siteID work₀ ⟨w,rfl⟩) hd
    exact h.trans (profile_start e p bin perm positive first q a siteID (.inr t))
  change (∀ copy < 1, ∀ k < desc.span,
    f ((desc.terminalPort ⟨off+original.base,0,1⟩).atBit copy k) = f ((⟨wire,0,1⟩ : Port).atBit copy k)) ↔
    ∀ copy < 1, ∀ k < desc.span,
    g ((desc.terminalPort ⟨off+original.base,0,1⟩).atBit copy k) = g ((⟨wire,0,1⟩ : Port).atBit copy k)
  apply forall_congr'; intro i
  apply imp_congr_right; intro hi
  obtain rfl : i = 0 := by omega
  apply forall_congr'; intro k
  apply imp_congr_right; intro hk
  let idx : Fin ((layout p.layout bin perm m).width (z.val,some (t.1,true))) :=
    ⟨k,hk.trans_eq (descriptor_width p.layout bin perm m binName z _).symm⟩
  let B := bundle p.layout bin perm m positive a
  let ord := B.order t.1 ⟨prefixEdge p.layout bin perm m a t.1 z,idx⟩
  have ord_eq := terminalPort_atBit p.layout bin perm m binName positive a t.1 z original 0 idx
  have stage_eq : (desc.terminalPort ⟨off+original.base,0,1⟩).atBit 0 k = original.atBit 0 ord := by
    rw [hzero,zero_add]
    simpa only [original,BankLayout.port,CutDescriptor.terminalPort,CutDescriptor.slice,Port.atBit,zero_mul,add_zero] using (show (desc.terminalPort original).atBit 0 k = original.atBit 0 ord from ord_eq)
  rw [stage_eq]
  have left := inputBit_lt m j₀ (q a).val ord
  have right := end_room G₀ v work₀ edgeID portID (profile_noLoop e p bin perm positive first q a (.inr t))
    u false hd (⟨k,hk.trans_eq (hook_fields e p bin perm positive first q binName a t.1 z src).2.2.symm⟩)
  have hs := same (original.atBit 0 ord) (left.trans_le (Nat.le_add_right (term₀ t).work _))
  have hw := same (wire+k) right
  simpa only [Port.atBit,zero_mul,add_zero,mul_one] using (congrArg₂ Eq hs hw).to_iff

end Packing.InheritedProfile

end BorderVNP
end Computability
end OAI
