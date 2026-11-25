import OAI.Hierarchy.ProbeFixedEarnedStamp

namespace OAI
/-! # The classifier and the physical second radius of a chosen ballot role -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit PortPadding
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "D" => max n₀ n₁
local notation "bs" => v.nativeBoards P z width
local notation "s" => v.located (v.seed P z width) P width
local notation "b" => P.catalogue
local notation "H" => StripChart.header F bs
local notation "occ" => v.roleOccurrence P z width

def earnedClass (a : Attempt) : Expr :=
  chooseField D 0 (catalystFlag (z:=z) («W»:=v.W) (k:=k) (depth:=v.depth) a) (H a).fieldTerm

def earnedMate (a : Attempt) : Expr :=
  P.catalogue.checkedEdge (chooseField D 0 (fun i=>((radiusMate s v.mesh b P.routes a i).atRow (H a).ballTerm)) (H a).fieldTerm)

theorem earned_terms (a : Attempt) :
    (v.nativeTrees P z width a).catalystMate=some (v.earnedClass P z width a,v.earnedMate P z width a) := by
  cases a <;> rfl

private theorem classified (a : Attempt) (m : Memory W) (row : Fin (H a).rows) (f : Fin D)
    (header : (H a).Loaded m) (size : D≤2^W) :
    (v.earnedClass P z width a).eval m ((occ a row f).val:Word W)=
      (catalystFlag (z:=z) («W»:=v.W) (k:=k) (depth:=v.depth) a f).eval m ((occ a row f).val:Word W) := by
  have field : (H a).fieldTerm.eval m ((occ a row f).val : Word W) = (f.val : Word W) :=
    (StripDirectory.header_pair (H a) m header row f).2
  have hit := (congrArg Fin.val field).trans (Fin.val_cast_of_lt (f.isLt.trans_le size))
  exact eval_chooseField D 0 (catalystFlag (z:=z) («W»:=v.W) (k:=k) (depth:=v.depth) a)
    (H a).fieldTerm m ((occ a row f).val : Word W) f
    (by simpa only [Nat.zero_add] using size) (by simpa only [Nat.zero_add] using hit)

private theorem mate_selected (a : Attempt) (m : Memory W) (row : Fin (H a).rows) (f : Fin D)
    (header : (H a).Loaded m) (size : D≤2^W) (room : P.catalogue.rows<2^W)
    (core : P.catalogue.CoreOrPad ((radiusMate s v.mesh b P.routes a f).eval m (row.val:Word W))) :
    (v.earnedMate P z width a).eval m ((occ a row f).val:Word W)=
      (radiusMate s v.mesh b P.routes a f).eval m (row.val:Word W) := by
  let i := occ a row f
  let sel := chooseField D 0 (fun j=>((radiusMate s v.mesh b P.routes a j).atRow (H a).ballTerm)) (H a).fieldTerm
  have read := StripDirectory.header_pair (H a) m header row f
  have ball : (H a).ballTerm.eval m (i.val : Word W) = (row.val : Word W) := read.1
  have which : ((H a).fieldTerm.eval m (i.val:Word W)).val=f.val :=
    (congrArg Fin.val read.2).trans (Fin.val_cast_of_lt (f.isLt.trans_le size))
  have value : sel.eval m (i.val:Word W)=(radiusMate s v.mesh b P.routes a f).eval m (row.val:Word W) := by
    unfold sel
    rw [eval_chooseField _ _ _ _ _ _ f (by simpa only [Nat.zero_add] using size)
      (by simpa only [Nat.zero_add] using which), eval_atRow]
    exact congrArg ((radiusMate s v.mesh b P.routes a f).eval m) ball
  change (P.catalogue.checkedEdge sel).eval m (i.val:Word W)=_
  exact (P.catalogue.checked_core_value sel m _ room (by rw [value];exact core)).trans value

theorem payload_mate_at (phase trial : ℕ) (m : Memory W) (row : Fin (H (Attempt.outer phase trial)).rows)
    (role : PayloadRole N k) (header : (H (Attempt.outer phase trial)).Loaded m)
    (size : D≤2^W) (room : P.catalogue.rows<2^W) :
    let a := Attempt.outer phase trial
    let f := inject (Nat.le_max_left n₀ n₁) (Fintype.equivFin _ role)
    let o := occ a row f
    (v.earnedClass P z width a).eval m (o.val:Word W)=(catalystBit role:Word W) ∧
      (v.earnedMate P z width a).eval m (o.val:Word W)=((v.payloadPricePorts P z width).mate b role).eval m (row.val:Word W) := by
  intro a f o
  have dec : radiusMate s v.mesh b P.routes a f=(v.payloadPricePorts P z width).mate b role := by
    simp only [a, f, radiusMate, PortPadding.extend_real, Equiv.symm_apply_apply, payloadPricePorts]
  constructor
  · rw [v.classified P z width a m row f header size]
    simp only [a, f, catalystFlag, extend_real, Equiv.symm_apply_apply, Expr.eval]
  · have core : P.catalogue.CoreOrPad (((v.payloadPricePorts P z width).mate b role).eval m (row.val : Word W)) := by
      cases role with
      | catalyst => exact P.catalogue.coreOnly_cases _ m _ room
      | radius | cross | horizontal | extra => exact Or.inr (Fin.val_cast_of_lt room)
    exact (v.mate_selected P z width a m row f header size room (by simpa only [dec] using core)).trans
      (congrArg (fun e : Expr => e.eval m (row.val : Word W)) dec)

theorem purchased_mate_at (phase trial tick inner : ℕ) (m : Memory W) (row : Fin (H (Attempt.inner phase trial tick inner)).rows)
    (role : PurchasedRole v.depth k) (header : (H (Attempt.inner phase trial tick inner)).Loaded m)
    (size : D≤2^W) (room : P.catalogue.rows<2^W) :
    let a := Attempt.inner phase trial tick inner
    let f := inject (Nat.le_max_right n₀ n₁) (Fintype.equivFin _ role)
    let o := occ a row f
    (v.earnedClass P z width a).eval m (o.val:Word W)=(catalystBit role:Word W) ∧
      (v.earnedMate P z width a).eval m (o.val:Word W)=((v.purchasedPricePorts P z width phase trial).mate b role).eval m (row.val:Word W) := by
  intro a f o
  have dec : radiusMate s v.mesh b P.routes a f=(v.purchasedPricePorts P z width phase trial).mate b role := by
    simp only [a, f, radiusMate, PortPadding.extend_real, Equiv.symm_apply_apply, purchasedPricePorts]
  constructor
  · rw [v.classified P z width a m row f header size]
    simp only [a, f, catalystFlag, extend_real, Equiv.symm_apply_apply, Expr.eval]
  · have core : P.catalogue.CoreOrPad (((v.purchasedPricePorts P z width phase trial).mate b role).eval m (row.val : Word W)) := by
      cases role with
      | catalyst => exact P.catalogue.coreOnly_cases _ m _ room
      | radius | cross | horizontal | extra => exact Or.inr (Fin.val_cast_of_lt room)
    exact (v.mate_selected P z width a m row f header size room (by simpa only [dec] using core)).trans
      (congrArg (fun e : Expr => e.eval m (row.val : Word W)) dec)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
