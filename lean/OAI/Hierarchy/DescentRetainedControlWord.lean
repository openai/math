import OAI.Hierarchy.DescentRetainedHomeMask
import OAI.Hierarchy.DescentRotorWindowArchive
import OAI.Hierarchy.DescentResetPackedStencil

namespace OAI
/-! # A short retained routing register from the real earlier matrix window -/
namespace Hierarchy.DescentRetainedControl
open DescentSIMDLookup DescentRotorWindowArchive
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def keyBits (L : ℕ) :=Nat.clog 2 (L+1)
def bits (L : ℕ) :=keyBits L*L
def socket {L : ℕ} (d : Fin L) : Cell (keyBits L):=⟨d.val+1,
  (Nat.succ_le_of_lt d.isLt).trans_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self L) (Nat.le_pow_clog (by decide) _))⟩

def neighbors {L : ℕ} (prior : Fin L→Fin L→Bool) (d : Fin L) :=(Finset.univ.filter fun j=>prior j d).card
def vector {L : ℕ} (accept : Fin L→Bool) (prior : Fin L→Fin L→Bool) : Cell (bits L) :=
  encode (keyBits L) L fun j=>∑d : Fin L, if accept d=true ∧ neighbors prior d=j.val then socket d else 0

def source {L : ℕ} (z : Cell (bits L)) (j : Fin L) : Option (Fin L) :=
  let k:=((encode (keyBits L) L).symm z j).val
  if h:0<k ∧ k≤L then some ⟨k-1,by omega⟩ else none

theorem at_source {L : ℕ} (accept : Fin L→Bool) (prior : Fin L→Fin L→Bool) (order : Fin L≃Fin L)
    (ranks : ∀d,neighbors prior d=(order d).val) (d : Fin L) :
    source (vector accept prior) (order d)=if accept d then some d else none:=by
  have one : ∑j : Fin L,(if accept j=true ∧ neighbors prior j=(order d).val then socket j else 0)=
      if accept d then socket d else 0:=by
    rw [Finset.sum_eq_single d]
    · simp [ranks]
    · intro j _ hj
      have diff:(order j).val≠(order d).val:=fun h=>hj (order.injective (Fin.ext h))
      simp [ranks,diff]
    · simp
  simp only [source,vector,Equiv.symm_apply_apply,one]
  by_cases h : accept d = true <;> simp [socket,h,Nat.succ_le_of_lt d.isLt]

def take {L : ℕ} (width : ℕ) (z : Cell (bits L)) (value : Cell (width*L)) : Cell (width*L) :=
  encode width L fun j=>(source z j).elim 0 ((encode width L).symm value)

theorem take_zero {L : ℕ} (width : ℕ) (z : Cell (bits L)) : take width z 0=0:=by
  have zero : encode width L (fun _ => 0) = 0 := by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin L => (0 : Cell width))).val = 0
    simp
  have inv:(encode width L).symm 0=(fun _=>0):=(encode width L).symm_apply_eq.mpr zero.symm
  unfold take
  rw [inv,←zero]
  apply congrArg (encode width L)
  funext j
  cases source z j <;>rfl

variable {D L cap b : ℕ}
def filter {field : ℕ} (which : Option ℕ) (packet : Cell (field*count D L cap)) : Cell (bits L):=
  let a:=(encode field (count D L cap)).symm packet
  let accept:=fun j : Fin L=>which=some ((a (ix (.inl (.inl (.inl j))))).val/2)
  let prior:=fun i j : Fin L=>decide ((a (ix (.inr (.inl (i,j))))).val≠0)
  vector (fun j=>decide (accept j)) prior

/-- Removing the zero-row image allows a clipped last SIMD word. The matching
constant is restored by the receiving shape's short strip decoder. -/
def code {field : ℕ} (which : Option ℕ) (packet : Cell (field*count D L cap)) : Cell (bits L) :=
  filter (D:=D) (L:=L) (cap:=cap) which packet-filter (D:=D) (L:=L) (cap:=cap) which (0:Cell (field*count D L cap))
def restore (field : ℕ) (which : Option ℕ) (c : Cell (bits L)) : Cell (bits L):=
  c+filter (D:=D) (L:=L) (cap:=cap) which (0:Cell (field*count D L cap))

@[simp] theorem code_zero (field : ℕ) (which : Option ℕ) :
    code (D:=D) (L:=L) (cap:=cap) which (0:Cell (field*count D L cap))=0:=by simp [code]
@[simp] theorem restore_code (field : ℕ) (which : Option ℕ) (x : Cell (field*count D L cap)) :
    restore (D:=D) (L:=L) (cap:=cap) field which (code which x)=filter which x:=by simp [restore,code]
theorem from_packet (which : Option ℕ) (x : Fin (count D L cap)→Cell b) :
    filter (D:=D) (L:=L) (cap:=cap) which (encode b _ x)=
    vector (fun j=>decide (which=some ((x (ix (.inl (.inl (.inl j))))).val/2)))
      (fun i j=>decide ((x (ix (.inr (.inl (i,j))))).val≠0)):=by simp [filter]

theorem joined (v : DescentResetRetainedSetup.Layout) (accept : Fin v.donors→Bool)
    (prior : Fin v.donors→Fin v.donors→Bool) (order : Fin v.donors≃Fin v.donors)
    (ranks : ∀d,neighbors prior d=(order d).val) (rows : Fin v.channels→Cell v.stripWord) :
    encode v.stripWord v.channels (fun j=>take v.bits (vector accept prior) (rows j))=
      v.routedWord accept prior (encode v.stripWord v.channels rows):=by
  unfold DescentResetRetainedSetup.Layout.routedWord
  apply congrArg (encode v.stripWord v.channels)
  funext j
  unfold take
  apply congrArg (encode v.bits v.donors)
  funext p
  obtain ⟨d,rfl⟩:=order.surjective p
  rw [at_source accept prior order ranks]
  let ix : Fin v.fields×Fin v.previousNodes:=finProdFinEquiv.symm j
  refine Eq.trans ?_ (v.routed_digit accept prior order ranks _ d ix.2 ix.1).symm
  have back : finProdFinEquiv (ix.1,ix.2)=j := finProdFinEquiv.apply_symm_apply j
  have digit : v.entry (encode v.stripWord v.channels rows) d ix.2 ix.1 =
      (encode v.bits v.donors).symm (rows j) d := by
    apply congrArg (fun x => (encode v.bits v.donors).symm x d)
    exact (congrFun ((encode v.stripWord v.channels).symm_apply_apply rows) _).trans (congrArg rows back)
  change (if accept d then some d else none).elim 0 ((encode v.bits v.donors).symm (rows j)) =
    if accept d then v.entry (encode v.stripWord v.channels rows) d ix.2 ix.1 else 0
  rw [digit]
  cases ok : accept d <;> rfl
end
end Hierarchy.DescentRetainedControl

end OAI
