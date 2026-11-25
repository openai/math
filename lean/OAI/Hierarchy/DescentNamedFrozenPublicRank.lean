import OAI.Computability.BorderVNP.FragmentBucketPrefixSteps
import OAI.Hierarchy.DescentNamedPublicGroupRank
import OAI.Hierarchy.DescentNamedFrozenRoster
import OAI.Hierarchy.DescentTerminalFrozenRelative

namespace OAI
/-! # Book's public name uses the pre-existing frozen home rank and the native live cell -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))



open DescentTerminalGraphPositions DescentTerminalCableOrder
open ThreeFlat.Routing
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "homeRow" => publicHost X G S b hp base width
local notation "pins" => NativeBranch.rawPin S (X:=X) (radix:=radix) base width
local notation "M" => publicLayout X G S b hp base width
local notation "rows" => (pins).symm.trans (chart (j:=j) (r:=rest) M)
local notation "Pin" => Σ _:Fin S.copies,Fin E


open Computability.VPVNP.BurstRAM PrivateRAM DescentGL DescentColonies PinCohorts DescentTerminalPacketHomeRAM Computability.BorderVNP.FragmentBucket
local notation "track" => publicSpine X G S b hp base width
local notation "trace" => pinSpine X G S b hp base
local notation "size_" => E*2^b.path.frozen
local notation "block_" => 2^(retained-j)
local notation "where_" => cohort X G S b hp base
local notation "whose" => cohortHome X G S b hp base

private theorem logical_row (room : j ≤ retained) (z : Pin) :
    frozenIndex X G S b hp base width room (rows z).1=where_ z := by
  let u:=(pins).symm z
  have opened : castBits width.symm ((address _).symm u.1)=active b.origin.source base radix z := by
    apply (address _).injective
    apply Fin.ext
    rw [address_cast,Equiv.apply_symm_apply]
    exact (pinInput X G S b base z).symm
  let start:=((address _).symm u.1)
  let id₀:=fun _ : Fin E=>LinearEquiv.refl (ZMod 2) (Bits (j+(j+rest)))
  have selected:=chart_previous track id₀ room (fun _=>rfl) u
  apply congrArg (fun v : Fin E × Fin (2^b.path.frozen)=>finProdFinEquiv v)
  change previous room _ (chart (rotor track id₀) u).1=
    (z.2,address b.path.frozen ((trace).cut (active b.origin.source base radix z)).2)
  rw [selected]
  apply Prod.ext
  · rfl
  · change address b.path.frozen ((trace).cut (castBits width.symm start)).2=_
    rw [show castBits width.symm start=active b.origin.source base radix z from opened]

private theorem low_label (room : j≤retained) (z : Pin) :
    (rows z).1.val%block_*2^j+(rows z).2.val=
      (address retained (active b.target base radix z)).val := by
  let u:=(pins).symm z
  let input:=(address (j+(j+rest))).symm u.1
  let y:=frozenFirst track input
  let hi:=rowOrd j rest (coords j rest y).2
  let low:=chunkOrd j (coords j rest y).1
  let full:=address (j+(j+rest)) y
  let a:=(address retained ((track).cut input).1).val
  have form : full.val=hi.val*2^j+low.val:=coordinate_row j rest y
  have whole : full.val=(address b.path.frozen ((track).cut input).2).val*2^retained+a := by
    let split:=(splitRows b.path.frozen retained).symm (((track).cut input).2,((track).cut input).1)
    change (address _ (castBits _ split)).val=_
    rw [address_cast]
    simpa only [split,LinearEquiv.apply_symm_apply] using split_value b.path.frozen retained split
  have slab : 2^(j+rest)=block_*2^b.path.frozen := by
    have total:=(track).width
    rw [←pow_add]; congr 1;omega
  have power : 2^retained=block_*2^j := by rw [←pow_add,Nat.sub_add_cancel room]
  have bottom:=low.isLt
  have arithmetic : (hi.val%block_)*2^j+low.val=a := by
    have subtract:hi.val=(hi.val/block_)*block_+hi.val%block_:=(Nat.div_add_mod' ..).symm
    have small : (hi.val%block_)*2^j+low.val<2^retained := by
      have h:=Nat.mod_lt hi.val (Nat.two_pow_pos (retained-j))
      have lim:=Nat.mul_le_mul_right (2^j) (Nat.succ_le_of_lt h)
      rw [Nat.succ_mul] at lim
      rw [power];omega
    have sum_:full.val=(hi.val/block_)*2^retained+((hi.val%block_)*2^j+low.val) := by
      calc
        full.val=(((hi.val/block_)*block_+hi.val%block_)*2^j+low.val) := by rw [←subtract,form]
        _ = _ := by rw [power];ring
    have first:=congrArg (· % 2^retained) sum_
    have last:=congrArg (· % 2^retained) whole
    have aSmall : a<2^retained:=(address retained _).isLt
    simpa only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt aSmall] using first.symm.trans last
  change (hi.val+2^(j+rest)*u.2.val)%block_*2^j+low.val=_
  rw [show 2^(j+rest)*u.2.val = (block_*2^b.path.frozen)*u.2.val from congrArg (· * u.2.val) slab,
    Nat.mul_assoc,Nat.add_mul_mod_self_left,arithmetic]
  have live:=congrArg (fun x=>(address retained x).val) ((track).active_eq u)
  simpa only [u,Equiv.apply_symm_apply] using live

theorem frozen_public_rank (room : j≤retained) (whole : p∣s)
    (i : Fin (S.hostSize S.length)) (g : Order.Group O i) (external : g.val=none)
    (nm : Order.At O i g) (z : Pin) (chunk : Fin (poolBatchCount (s*1) p)) (label : nm.val=.inr ⟨z,chunk⟩) :
    (Order.inGroup O i g nm).val =
      (prior whose (where_ z).val i*2^retained+
        (address retained (active b.target base radix z)).val)*(s/p)+chunk.val := by
  have equiv : E*2^(j+rest)=size_*block_ := by
    rw [Nat.mul_assoc,←pow_add]
    have total:=(track).width
    congr 2; omega
  let group:=frozenIndex X G S b hp base width room
  have top:= (track).width
  have lr (u:Fin (E*2^(j+rest))) : (group u).val=u.val/block_ :=
    (frozenIndex_val X G S b hp base width room u).trans
      (calendar_quotient E j rest retained room (by omega) u)
  have homes (a:Fin (E*2^(j+rest))) : homeRow a=whose (group a) :=
    (publicHost_frozen X G S b hp base width room a).trans (frozenHome_direct X G S b hp base width (group a))
  have used : Order.Used O i (.inr ⟨z,chunk⟩) := label ▸ nm.2.1
  have target := (Order.used_port O i z chunk).mp used
  have which : homeRow (rows z).1=i := by
    have h:=public_host_read X G S b hp base width room ((pins).symm z)
    simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using h.symm.trans target
  have rank:=contiguous_prior equiv whose homeRow group lr homes (rows z).1
  rw [which] at rank
  rw [public_group_rank X G S b hp base width room whole i g external nm z chunk label,rank,
    show group (rows z).1=where_ z from logical_row X G S b hp base width room z]
  let n := prior whose (where_ z).val i
  have join_ : (n*block_+(rows z).1.val%block_)*2^j+(rows z).2.val=
      n*2^retained+(address retained (active b.target base radix z)).val := by
    calc
      _ = n*(block_*2^j)+((rows z).1.val%block_*2^j+(rows z).2.val) := by ring
      _ = _ := by rw [low_label X G S b hp base width room z,←pow_add,Nat.sub_add_cancel room]
  exact congrArg (fun a=>a*(s/p)+chunk.val) join_


/-- Book field six reads only the local port ordinal, the physical resident cell, and the within-pin grain. -/
theorem resident_public_name (room : j≤retained) (whole : p∣s) (v:(net).Site) (pin : Attached net v)
    (g : Order.Group O (b.target.home v)) (external : g.val=none) (nm : Order.At O (b.target.home v) g)
    (chunk : Fin (poolBatchCount (s*1) p)) (label : nm.val=.inr ⟨pin.val,chunk⟩) :
    (Order.inGroup O (b.target.home v) g nm).val=
      (densePin X G S b hp base v pin*2^retained+(address retained (activeAt X G S b base v)).val)*(s/p)+chunk.val := by
  have live : active b.target base radix pin.val=activeAt X G S b base v := by
    change activeAt X G S b base ((net).attach pin.val)=_
    rw [pin.property]
  have rank : densePin X G S b hp base v pin = prior whose (where_ pin.val).val (b.target.home v) := rfl
  rw [rank]
  simpa only [live] using frozen_public_rank X G S b hp base width room whole (b.target.home v) g external nm
    pin.val chunk label

/-- The pre-Book frozen shelf supplies the very same local ordinal as the row generator. -/
theorem resident_public_word {wb : ℕ} (room : j≤retained) (whole : p∣s)
    (L : ProtocolRAMEndpointSort.Layout) (m : Memory wb)
    (fit : L.Fits wb size_ (S.hostSize S.length)) (height : S.hostSize S.length<2^wb)
    (loaded : ∀a:Fin size_,m (L.src+a.val)=((frozenHome X G S b hp base width a).val:Computability.VPVNP.BurstRAM.Word wb))
    (v:(net).Site) (pin : Attached net v) (g : Order.Group O (b.target.home v)) (external:g.val=none)
    (nm : Order.At O (b.target.home v) g) (chunk : Fin (poolBatchCount (s*1) p)) (label : nm.val=.inr ⟨pin.val,chunk⟩) :
    let mm := DescentTerminalPacketSlotRAM.after L size_ (S.hostSize S.length) (ProtocolRAMEndpointSort.image L whose m)
    let adr := DescentTerminalPacketSlotRAM.out L size_ (S.hostSize S.length)+(dest whose (where_ pin.val)).val
    (Order.inGroup O (b.target.home v) g nm).val=
      ((mm adr).val*2^retained+(address retained (activeAt X G S b base v)).val)*(s/p)+chunk.val := by
  intro mm adr
  have loc:=cohort_slot X G S b hp base width m L fit height loaded v pin
  change mm adr=(densePin X G S b hp base v pin:Computability.VPVNP.BurstRAM.Word wb) at loc
  have bound:=prior_le_rows whose (where_ pin.val).val (b.target.home v)
  have full:=fit.room
  have small : densePin X G S b hp base v pin < 2^wb := by
    change prior whose (where_ pin.val).val (b.target.home v)<2^wb
    have hi:=(where_ pin.val).isLt
    omega
  rw [loc,Fin.val_cast_of_lt small]
  exact resident_public_name X G S b hp base width room whole v pin g external nm chunk label

end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
