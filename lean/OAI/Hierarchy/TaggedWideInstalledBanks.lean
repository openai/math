import OAI.Hierarchy.TaggedWideLeafBanks
import OAI.Hierarchy.TaggedWidePurchaseTransport
import OAI.Hierarchy.TaggedWidePhysical

namespace OAI
/-! # Install the two purchased networks at their original numbered ports -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged Tagged.WideStack Tagged.WideStack.Leaf TaggedShorterBudget TaggedShorterPacking TaggedShorterSupergroups
open ThreeFlat Routing Spill TaggedShorterCompaction TaggedShorterNetwork
open ProtocolRAMReportedPorts Real Filter
open scoped Classical BigOperators Topology
set_option quotPrecheck false

variable {F : Type*} [Field F] {κ A δ ξ C : ℝ} {u : ℝ→ℝ}
  (W m k attempts ell short : ℕ) (hW : 0<W)
local notation "geometry" => typeMenu κ A W m k attempts ell hW (fun _=>short+ell)
local notation "menu" => (geometry).menu u δ ξ
local notation "roles" => copies k attempts
local notation "dir" x => stageDir (x).h W roles (2*roles) (show 2*roles≤2^(2*roles) from Nat.lt_two_pow_self.le)
local notation "ports" x => 2^(superAddress W (2*roles) (x).h)
local notation "slots" x => purchaseSlots (x).h W k attempts ell

/-- The fixed ordinal type of the supplied public purchase is transported only by
the actual cardinality of the native batch directory. -/
def installedPurchase (x : WideParent κ A) (i : Fin (m+1))
    (buy : Purchased F menu x i (slots x)
      (purchaseCandidates x.h W k attempts (slots x) ((menu).height i x) (purchaseModules W u δ ξ menu x i))
      (purchaseModules W u δ ξ menu x i) C)
    (groupsFit : GroupRoom W k attempts u δ ξ menu x)
    (metadata : 1+(menu).height i x+(menu).height i x≤(menu).payload i x)
    {rowsN : ℕ} (rows : Fin rowsN→ProtocolRAMEmit.Row)
    (unique : Function.Injective fun j=>(rows j).link)
    (volume : ((∑ g : Fin (dir x).groups,count rows x.w m i.val g.val : ℕ):ℝ)≤
      typeFraction u δ ξ (logb x.h x.w) (W,i.val)*(2:ℝ)^x.h)
    (port : Bool→Fin rowsN→Fin (ports x))
    (anchor : {j : Fin rowsN // 0<pieces rows x.w j}×Bool ↪ Fin (dir x).groups × Fin (ports x))
    (owner : ∀j b,(anchor (j,b)).1.val=(rows j.val).group)
    (pin : ∀j b,(anchor (j,b)).2=port b j.val)
    (room : ∀j,pieces rows x.w j≤2^ell) :
    Leaf.Installed F (dir x).groups (ports x) (2^ell) x.w m i.val rows := by
  let t:=(menu).height i x
  let half:=2^(t-1)
  let M:=purchaseModules W u δ ξ menu x i
  let fraction:=typeFraction u δ ξ (logb x.h x.w) (W,i.val)
  have width : (menu).payload i x=⌈dyadic i.val*x.w⌉₊:=rfl
  have halfPos : 0<half:=(groupsFit i).1
  have twice : 2*half=2^t:=(groupsFit i).2.1
  have padding:=(groupsFit i).2.2
  have denom : (2:ℝ)^t=(2*half:ℕ) := by exact_mod_cast twice.symm
  refine ⟨half,t,M,fraction,(2:ℝ)^x.h,unique,volume,?_,halfPos,twice.symm,?_,?_,?_,?_,port,?_,room⟩
  · simpa only [Nat.cast_mul,Nat.cast_ofNat] using padding
  · change ⌈6*fraction*(2:ℝ)^x.h/(2:ℝ)^t⌉₊=_
    rw [denom]
  · exact buy.near
  · exact buy.farAt (purchase_capacity (dir x).groups (slots x) half M).symm
  · exact width ▸ metadata
  · intro g b
    exact portDistinct_of_grouped rows x.w m i.val (port b) ((Function.Embedding.sectL _ b).trans anchor)
      (fun j=>owner j b) (fun j=>pin j b) g

/-- The settled public input words evaluate exactly the original paid cut after
identifying its candidate ordinals with the actual static group batches. -/
theorem installedPurchase_closed (x : WideParent κ A) (i : Fin (m+1))
    (buy : Purchased F menu x i (slots x)
      (purchaseCandidates x.h W k attempts (slots x) ((menu).height i x) (purchaseModules W u δ ξ menu x i))
      (purchaseModules W u δ ξ menu x i) C)
    (groupsFit : GroupRoom W k attempts u δ ξ menu x)
    (metadata : 1+(menu).height i x+(menu).height i x≤(menu).payload i x)
    {rowsN : ℕ} (rows : Fin rowsN→ProtocolRAMEmit.Row)
    (unique : Function.Injective fun j=>(rows j).link)
    (volume : ((∑ g : Fin (dir x).groups,count rows x.w m i.val g.val : ℕ):ℝ)≤
      typeFraction u δ ξ (logb x.h x.w) (W,i.val)*(2:ℝ)^x.h)
    (port : Bool→Fin rowsN→Fin (ports x))
    (anchor : {j : Fin rowsN // 0<pieces rows x.w j}×Bool ↪ Fin (dir x).groups × Fin (ports x))
    (owner : ∀j b,(anchor (j,b)).1.val=(rows j.val).group)
    (pin : ∀j b,(anchor (j,b)).2=port b j.val)
    (room : ∀j,pieces rows x.w j≤2^ell)
    {V : Type} [Fintype V]
    (read : Input (TaggedShorterGroups.capacity (Fin (dir x).groups) (slots x)
      (2^((menu).height i x-1)) (purchaseModules W u δ ξ menu x i))
      (slots x) ((menu).height i x+(menu).payload i x)→V) (values : V→Bool) :
    let half:=2^((menu).height i x-1)
    let modules:=purchaseModules W u δ ξ menu x i
    let candidateCount:=TaggedShorterGroups.capacity (Fin (dir x).groups) (slots x) half modules
    let same:= (purchase_capacity (dir x).groups (slots x) half modules).symm
    let mounted:=installedPurchase W m k attempts ell short hW x i buy groupsFit metadata rows unique volume
      port anchor owner pin room
    (buy.cut (Purchased.readAt same read)).closed values =
      (CutFormat.mk candidateCount (slots x) modules ((menu).height i x) ((menu).payload i x)
        mounted.near mounted.far read).closed values :=
  buy.cut_cast_closed _ read values

theorem purchase_metadata (positive : 0<κ) (large : 1<A) :
    ∀ᶠ x in WideParent.large κ A,∀i : Fin (m+1),
      1+(menu).height i x+(menu).height i x≤(menu).payload i x :=
  (geometry).metadata u positive large

end Hierarchy.ProbeStage.ReportSockets

end

end OAI
