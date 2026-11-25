import OAI.Hierarchy.DescentRetainedResetPinPointer
import OAI.Hierarchy.DescentResetDonorSlotSources

namespace OAI
/-! Private words and occupied operand slots in a primary and its original donors. -/
namespace Hierarchy.DescentRetainedPrivateSlotBook
open DescentKernelHistory DescentLocalPrivateNames DescentBundleHistory DescentNamedContact
open DescentSixParty DescentRouterBank DescentResetTrunks Computability.BorderVNP.Crossing
open DescentCompiler DescentPrimitivePalette DescentRetainedResetPinPointer
open scoped Classical
noncomputable section
set_option quotPrecheck false

/-- The primary has the disjoint union of its donors' argument slots and used
private words. The two identifications preserve the reference at every slot. -/
structure Donors {T U A I : Type} {P : I→Type} (r : Recipe T A) (src : ∀i,Recipe U (P i)) where
  slots : Slot r≃(Σi,Slot (src i))
  words : r.UsedWord≃(Σi,(src i).UsedWord)
  uses : ∀s w,read r s=some w ↔ ∃u,read (src (slots s).1) (slots s).2=some u ∧ words w=⟨(slots s).1,u⟩

namespace Donors
variable {T U V U₁ A B I : Type} {P Q : I→Type} {r : Recipe T A} {s : Recipe V B}
  {src : ∀i,Recipe U (P i)} {prior : ∀i,Recipe U₁ (Q i)}

def rebase (x : WordBook r s) (d : Donors s src) : Donors r src where
  slots:=x.slotsTo.trans d.slots
  words:=x.word.trans d.words
  uses q w:=(x.slots_read q w).trans (d.uses _ _)

def previous (d : Donors r src) (b : ∀i,WordBook (src i) (prior i)) : Donors r prior where
  slots:=d.slots.trans (Equiv.sigmaCongrRight (fun i=>(b i).slotsTo))
  words:=d.words.trans (Equiv.sigmaCongrRight (fun i=>(b i).word))
  uses q w:=by
    change read r q=some w ↔ ∃u,read (prior _) ((b _).slotsTo (d.slots q).2)=some u ∧
      (Equiv.sigmaCongrRight (fun i=>(b i).word)) (d.words w)=⟨(d.slots q).1,u⟩
    rw [d.uses]
    constructor
    · rintro ⟨u,hit,same⟩
      exact ⟨(b _).word u,((b _).slots_read _ _).1 hit,by rw [same];rfl⟩
    · rintro ⟨u,hit,same⟩
      let v:=((b (d.slots q).1).word).symm u
      have equal : (b _).word v=u := Equiv.apply_symm_apply _ _
      refine ⟨v,((b _).slots_read _ _).2 (equal.symm ▸ hit),?_⟩
      apply (Equiv.sigmaCongrRight (fun i=>(b i).word)).injective
      simpa only [Equiv.sigmaCongrRight_apply,equal] using same

/-- A genuine hidden word is named by its original donor and the minimum actual
rectangular address of its old argument. -/
def key {D K bits : ℕ} (d : Donors r src) (donor : I↪Fin D)
    (positions : ∀i,Slot (src i)↪Fin K) (fit : K≤2^bits) : r.UsedWord↪Fin D×DescentSIMDLookup.Cell bits where
  toFun w:=(donor (d.words w).1,((firstAlias _ (positions _) (d.words w).2).castLE fit))
  inj' :=by
    intro u v same
    change (donor (d.words u).1, (firstAlias _ (positions _) (d.words u).2).castLE fit) =
      (donor (d.words v).1, (firstAlias _ (positions _) (d.words v).2).castLE fit) at same
    apply d.words.injective
    generalize d.words u=x at same ⊢
    generalize d.words v=y at same ⊢
    obtain ⟨i,a⟩:=x
    obtain ⟨j,b⟩:=y
    obtain rfl : i=j:=donor.injective (congrArg Prod.fst same)
    have ab : a=b:=(firstAlias _ (positions i)).injective (Fin.ext (congrArg (fun p : Fin D×Fin (2^bits)=>p.2.val) same))
    cases ab
    rfl

theorem source {D K bits : ℕ} (d : Donors r src) (donor : I↪Fin D)
    (positions : ∀i,Slot (src i)↪Fin K) (fit : K≤2^bits) (q : Slot r) (w : r.UsedWord)
    (hit : read r q=some w) :
    ∃u,read (src (d.slots q).1) (d.slots q).2=some u ∧
      d.key donor positions fit w=(donor (d.slots q).1,(firstAlias _ (positions _) u).castLE fit):=by
  obtain ⟨u,seen,which⟩:=(d.uses q w).1 hit
  refine ⟨u,seen,?_⟩
  exact congrArg (fun z : Σi,(src i).UsedWord => (donor z.1,(firstAlias _ (positions z.1) z.2).castLE fit)) which

theorem key_slot {D K bits:ℕ} (d : Donors r src) (donor : I↪Fin D)
    (positions : ∀i,Slot (src i)↪Fin K) (fit : K≤2^bits) (q : Slot r) :
    (read r q).map (d.key donor positions fit)=
      (read (src (d.slots q).1) (d.slots q).2).map
        (fun u=>(donor (d.slots q).1,Fin.ofNat (2^bits) (firstAlias _ (positions _) u).val)):=by
  cases seen:read r q with
  | some w=>
    obtain ⟨u,previous,which⟩:=d.source donor positions fit q w seen
    rw [previous]
    simp only [Option.map_some, Option.some.injEq, which]
    apply congrArg (Prod.mk _)
    apply Fin.ext
    exact (Nat.mod_eq_of_lt ((firstAlias _ (positions _) u).isLt.trans_le fit)).symm
  | none=>
    cases was:read (src (d.slots q).1) (d.slots q).2 with
    | none=>rfl
    | some u=>
      let w:=d.words.symm ⟨(d.slots q).1,u⟩
      have hit:read r q=some w:=(d.uses q w).2 ⟨u,was,d.words.apply_symm_apply _⟩
      rw [seen] at hit
      contradiction
end Donors

section Gather
variable {p n d L : ℕ} {P H Q X : Type} [Fintype H] [Fintype Q] {bs : P→ℕ}
variable (hp:0<p) (N:Network n P bs) (home:N.Site→H) (group:Bool→N.Edge→Q)
  (R:Network d (Bool×Q) (publicWidth group N.width)) (idx:N.Edge↪Fin L)
  (whole:∀e,p∣N.width e) (old:SiteBits (U:=X) N) (src:∀v,Shape p (old v)) (h:H)
local notation "result" => (inShape N home group R idx whole old src h).recipe hp

def gathered : Donors result (fun i:Fibre home h=>(src i.val).recipe hp) where
  slots:=retainedSlots hp N home group R idx whole old src h
  words:=resetDonor hp N home group R idx whole old src h
  uses q w:=by
    obtain ⟨⟨i,node⟩,j⟩:=q
    let u:=DescentResetLocalNodes.gathered N home group R idx old h i node
    let k:=Fin.cast (retained_argument_count hp N home group R idx whole old src h i node) j
    change read result ⟨⟨i,node⟩,j⟩=some w ↔ ∃v,read ((src i.val).recipe hp) ⟨u,k⟩=some v ∧ _
    have eqv := retained_slot_private hp N home group R idx whole old src h i node k w
    constructor
    · intro seen
      obtain ⟨v,hit,same⟩ := eqv.mp ((read_some result ⟨i,node⟩ j w).mp seen)
      exact ⟨v,(read_some _ u k v).mpr hit,same⟩
    · rintro ⟨v,seen,same⟩
      exact (read_some result ⟨i,node⟩ j w).mpr (eqv.mpr ⟨v,(read_some _ u k v).mp seen,same⟩)
end Gather

end
end Hierarchy.DescentRetainedPrivateSlotBook

end OAI
