import OAI.Hierarchy.DescentAlignedTrunkRefs
import OAI.Hierarchy.DescentTrunkBitHistory
import OAI.Hierarchy.DescentBundleHistory

namespace OAI
/-! # Retaining whole payload references through the ordered physical reset -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory DescentOrderedWords DescentResetAttachments DescentNamedContact DescentRouterBank Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {A B : Type} {w : A→ℕ} {v : B→ℕ} {p : ℕ}

/-- A genuine full-payload image is enough for all p bit operands at once. -/
def alignedMap (f : BitRef w→BitRef v)
    (lift : ∀a (b : Aligned p (w a)),∃ c : B, ∃ s : Aligned p (v c),∀d,f ⟨a,b.bit d⟩=⟨c,s.bit d⟩) :
    BlockMap p w v f where
  map t :=
    let e := lift t.port ⟨t.block,t.fits⟩
    let s := e.choose_spec.choose
    ⟨e.choose,s.row,s.fits⟩
  read t d := ((lift t.port ⟨t.block,t.fits⟩).choose_spec.choose_spec d).symm

variable {n r : ℕ} {P H Q X Y : Type} [Fintype H] [Fintype Q] {bits : P→ℕ}
variable (N : Network n P bits) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network r (Bool×Q) (publicWidth group N.width)) {L : ℕ} (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e)
local notation "M" => DescentResetTrunks.network N home group R
variable (old : SiteBits (U:=X) N) (bank : SiteBits (U:=Y) R)

def oldBlockMap (u : N.Site) := alignedMap (trunkOldBit N home group R key u)
  (trunkOldBit_aligned N home group R key whole u)

def bankBlockMap (hp : 0<p) (u : R.Site) := alignedMap (trunkBankBit N home group R key u)
  (trunkBankBit_aligned N home group R key whole hp u)

def oldGatherShape (s : ∀v,Shape p (old v)) (h : H) (u : Fibre home h) :
    Shape p (oldGather N home group R key old h u) := by
  rcases u with ⟨u,rfl⟩
  exact (s u).reroute (oldBlockMap N home group R key whole u)

def bankPullbackShape (hp : 0<p) (s : ∀v,Shape p (bank v)) (v : R.Site) :
    Shape p (bankPullback N home group R key bank v) :=
  (s v).reroute (bankBlockMap N home group R key whole hp v)

private theorem finPair {a b : ℕ} (i : Fin a) (j : Fin b) :
    (finProdFinEquiv (i,j)).val=i.val*b+j.val := by change j.val+b*i.val=i.val*b+j.val;ring

/-- Each relay source and its matching trunk position are one complete initial
edge word. The dense lane in the latter starts at its ordered prefix. -/
def relayShape (hp : 0<p) (h : H) : Shape p (relay N home group R key h) where
  hiddenMultiple x := nomatch x
  groups e _ := N.width e.val/p
  size_eq e _ := (Nat.div_mul_cancel (whole e.val)).symm
  chunk e s j :=
    let inOld : Aligned p (N.width e.val) := ⟨j.val,
      (Nat.mul_le_mul_right p j.isLt).trans_eq (Nat.div_mul_cancel (whole e.val))⟩
    let width (i : Fibre (DescentResetTrunks.moved N home) h) := N.width i.val
    let order := DescentOrderedReset.fibreKey key (DescentResetTrunks.moved N home) h
    let packed := inside order width (fun q=>whole q.val) e inOld
    Slice.whole hp (.inl (if s.val=0 then
      ⟨.inl ⟨.inr (.inl h),Or.inr rfl⟩,packed.row,packed.fits⟩
      else ⟨.inl ⟨.inl (true,e.val),Or.inl (congrArg (fun q=>Sum.inl (true,q)) e.property)⟩,j.val,inOld.fits⟩))
  read e s j d := by
    let rank := DescentOrderedReset.fibreKey key (DescentResetTrunks.moved N home) h
    let width (i : Fibre (DescentResetTrunks.moved N home) h) := N.width i.val
    let lane : Aligned p (N.width e.val) := ⟨j.val,
      (Nat.mul_le_mul_right p j.isLt).trans_eq (Nat.div_mul_cancel (whole e.val))⟩
    let index : Fin (N.width e.val) :=
      Fin.cast (Nat.div_mul_cancel (whole e.val)) (finProdFinEquiv (j,d))
    have digit : lane.bit d = index := Fin.ext (finPair j d).symm
    rw [decode_whole]
    by_cases hs : s.val=0
    · simp only [hs,ite_true,Sum.map_inl,relay]
      apply congrArg Sum.inl
      exact congrArg (Sigma.mk _) ((inside_read rank width (fun i=>whole i.val) e lane d).trans
        (congrArg (fun b : Fin (N.width e.val)=>address rank width ⟨e,b⟩) digit))
    · simp only [hs,ite_false,Sum.map_inl,relay]
      apply congrArg Sum.inl
      exact congrArg (Sigma.mk _) digit

end
end Hierarchy.DescentBundleHistory

end OAI
