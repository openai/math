import OAI.Hierarchy.DescentPreparedPrivateRoots
import OAI.Hierarchy.DescentDatedResetWindows

namespace OAI
/-! # The scalar and lookup pages physically mounted ahead of the independent root scans -/
namespace Hierarchy.DescentDatedAddressBook
open DescentSixParty.Chronology DescentFallbackPeriod.Projected DescentSIMDLookup Filter
noncomputable section

def rootHeaderEnd (base r n D H G M shapes field lawWidth : ℕ) :=
  DescentSharedLeafLookup.Public.stop (DescentSharedBookScan.Public.stop base r (2^n) D H shapes) H G M field+
    Fintype.card (RootPage r (2^n))*lawWidth

theorem root_header_physical {n r D L cap field : ℕ} (b : RootBook n r D L cap field)
    (base H G M : ℕ) : b.stop base H G M=rootHeaderEnd base r n D H G M b.shapes field (b.width H G M) := rfl

theorem root_header_affine (base r n D H G M shapes field lawWidth : ℕ) :
    rootHeaderEnd base r n D H G M shapes field lawWidth=
    base+rootHeaderEnd 0 r n D H G M shapes field lawWidth := by
  simp [rootHeaderEnd,DescentSharedLeafLookup.Public.stop,DescentSharedBookScan.Public.stop,Nat.add_assoc]

theorem root_header_rate {ι : ℕ→Type*} {r n D H G M S F W : ∀h,ι h→ℕ}
    (radix : Bounded (fun h i=>2^(r h i))) (classes : Bounded (fun h i=>2^(n h i)))
    (degree : Bounded D) (hosts : Bounded H) (groups : Bounded G) (lanes : Bounded M)
    (shapes : Bounded S) (field : Bounded (fun h i=>2^(F h i))) (law : Bounded W) :
    Bounded (fun h i=>rootHeaderEnd 0 (r h i) (n h i) (D h i) (H h i) (G h i) (M h i) (S h i) (F h i) (W h i)) := by
  let c := fun j=>Bounded.const (ι:=ι) j
  have depth:=radix.of_le (y:=r) fun _ _=>Nat.lt_two_pow_self.le
  have pr:=((depth.add (c 1)).mul radix).mul (classes.add (c 1))
  have fieldCount:=pr.mul ((degree.add (c 1)).mul pr)
  have image:=((c 2).mul pr).mul shapes
  have maxr:=(hosts.mul fieldCount).max' ((depth.add (c 1)).max' (radix.max' ((classes.add (c 1)).max' image)))
  have scalar:=(c DescentSharedBookScan.Public.lanes).mul maxr.padded
  have batch : Bounded (fun h i=>chunks (G h i) (M h i)) :=
    (groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=hosts.mul batch
  have repeated:=(scalar.add ((c 2).mul rows.padded)).add (((lanes.add (c 1)).mul field).padded)
  have pages : Bounded (fun h i=>Fintype.card (RootPage (r h i) (2^(n h i)))) :=by
    let codes:=fun h (i:ι h)=>(DescentHostDirectory.codes (r h i)).card
    have count : Bounded codes := (radix.mul (c 2)).of_le fun h i=>by
      have room:=DescentHostDirectory.codes_card (r h i)
      rw [Nat.pow_succ] at room
      dsimp only [codes]
      omega
    have slots:=(c 2).mul ((count.mul ((c 2).add classes)).add (count.mul (classes.add (c 1))))
    simpa only [RootTemplates.page_count] using slots
  apply (repeated.add (pages.mul law)).of_le
  intro h i
  simp only [rootHeaderEnd,DescentSharedBookScan.Public.stop,DescentSharedBookScan.Public.bits,
    DescentSharedBookScan.Public.maxRows,DescentSharedBookScan.width,DescentFallbackShapeTable.rows,
    DescentFallbackShapeTable.imageSize,DescentSharedLeafLookup.Public.stop,DescentSharedLeafLookup.Public.stride,
    DescentSharedLeafLookup.Public.words,Nat.zero_add,Nat.le_refl]

/-- Uniform bounds on the native table arity and on its single packed key bound the actual
supremum over the complete finite family of good, exceptional and ghost root laws. -/
theorem root_law_width_rate {ι : ℕ→Type*} {n r D L cap field H G M : ∀h,ι h→ℕ}
    (books : ∀h (i:ι h),RootBook (n h i) (r h i) (D h i) (L h i) (cap h i) (field h i))
    (hosts : Bounded H) (groups : Bounded G) (lanes : Bounded M)
    (arity : ∃U:ℕ,∀ᶠ h:ℕ in atTop,∀i p,((books h i).table p).1≤2^(U*h))
    (key : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i p,let t:=(books h i).table p;
      (t.2.field*t.1+t.2.field)*M h i≤K*h)
    (shared : Bounded (fun h i=>(books h i).sharedWords (M h i))) :
    Bounded (fun h i=>(books h i).width (H h i) (G h i) (M h i)) := by
  apply Bounded.add (y:=fun h i=>(books h i).sharedWords (M h i)) (x:=fun h i=>(books h i).payloadWidth (H h i) (G h i) (M h i)) _ shared
  obtain ⟨U,hu⟩:=arity
  obtain ⟨K,hk⟩:=key
  have ap : Bounded (ι:=ι) (fun h _=>2^(U*h)):=⟨U,Filter.Eventually.of_forall (fun _ _=>le_rfl)⟩
  have kp : Bounded (ι:=ι) (fun h _=>2^(K*h)):=⟨K,Filter.Eventually.of_forall (fun _ _=>le_rfl)⟩
  have batch : Bounded (fun h i=>chunks (G h i) (M h i)) :=
    (groups.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  obtain ⟨C,hc⟩:=(Bounded.const 1).add (((ap.mul ((Bounded.const 2).mul kp)).add kp).add (hosts.mul batch).padded)
  refine ⟨C,?_⟩
  filter_upwards [hu,hk,hc] with h au ak bound
  intro i
  apply le_trans _ (bound i)
  apply Nat.add_le_add_left _ 1
  apply Finset.sup_le
  intro p _
  let t:=(books h i).table p
  have packed : (t.2.field*t.1+t.2.field)*M h i≤K*h:=ak i p
  have strip : t.2.field*t.1*M h i≤K*h :=
    (Nat.mul_le_mul_right (M h i) (Nat.le_add_right ..)).trans packed
  have P:=Nat.pow_le_pow_right (by decide : 0<2) packed
  have S:=Nat.pow_le_pow_right (by decide : 0<2) strip
  change t.2.stop 0 (H h i) (G h i) (M h i)≤_
  simp only [RootTable.stop,RootTable.split,RootTable.unit,Nat.zero_add]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul (au i p) (Nat.mul_le_mul_left 2 P)) S) _

end
end Hierarchy.DescentDatedAddressBook

end OAI
