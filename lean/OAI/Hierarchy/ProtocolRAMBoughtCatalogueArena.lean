import OAI.Hierarchy.ProtocolRAMBoughtCatalogueFits
import OAI.Hierarchy.ProtocolRAMCoreCatalogueBudget

namespace OAI
/-! # One high-water address for the real core and bought catalogue readers -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen ReportSockets CoreBoard Calendar CatalogueRows
open scoped Classical Fin.CommRing
variable {h W k attempts : ℕ}

def Directory.eventEnds (v : Directory attempts) (S : PurchaseSampler) (h d k depth : ℕ) (a : Fin attempts) :=
  let cap := ProtocolRAMPurchaseSampler.span (count h d k*paths h S.degree depth)
  max ((v.shelf a).firstBase+count h d k*blockSize h d S.degree depth)
    (max (v.flagBase a+cap) (v.menuBase a+cap))

def Directory.archivesEnd (v : Directory attempts) (S : PurchaseSampler) (h d k depth : ℕ) :=
  max (v.header h d k S.degree depth).stop
    (max (StripDirectory.stratumHeader h d k S.degree depth v.keysBase).stop
      (Finset.univ.sup (v.eventEnds S h d k depth)))

def Directory.withCore (v : Directory attempts) (h W K : ℕ) : Directory attempts :=
  { v with
    remapBase := CoreCatalogue.groupStart h W
    superBase := CoreCatalogue.superStart h W
    sitesBase := CoreCatalogue.siteBase h W K }

def Directory.jointTop (v : Directory attempts) (S : PurchaseSampler) (h W k depth K G H R : ℕ) :=
  max (CoreCatalogue.top h W K G H R) (v.archivesEnd S h (2^W) k depth)

def decoderFactor (S : PurchaseSampler) (d k attempts depth : ℕ) :=
  let keys := (2*rounds d+1)*(2*k)
  let cards := keys*S.degree^depth
  12*((attempts+1)*cards)+8+keys*factor d S.degree depth+2*(cards+1)

/-- The original event bases and the two immutable header bases can be
supplied by an existing calendar layout. Choosing the same upper bound for
all of them adds a fixed number of linear rows, independent of height. -/
theorem Directory.archives_linear (v : Directory attempts) (S : PurchaseSampler) (h d k depth B : ℕ)
    (origin : v.outerBase≤ B ∧ v.keysBase≤ B ∧ ∀a,(v.shelf a).firstBase≤ B ∧ v.flagBase a≤ B ∧ v.menuBase a≤ B) :
    v.archivesEnd S h d k depth≤ B+decoderFactor S d k attempts depth*2^h := by
  let n := 2^h
  let keys := (2*rounds d+1)*(2*k)
  let cards := keys*S.degree^depth
  have npos : 1≤ n := Nat.two_pow_pos _
  have countAt : count h d k=keys := count_eq h d k
  have size : count h d k*paths h S.degree depth=cards*n := by
    rw [countAt];dsimp only [paths,cards,n];ring
  have old := (v.header h d k S.degree depth).span
  change _ ≤ v.outerBase+12*(attempts*(count h d k*paths h S.degree depth))+8 at old
  rw [size] at old
  have small := (StripDirectory.stratumHeader h d k S.degree depth v.keysBase).span
  change _ ≤ v.keysBase+12*(count h d k*paths h S.degree depth)+8 at small
  rw [size] at small
  have bins := ProtocolRAMPurchaseSampler.span_le (count h d k*paths h S.degree depth)
  rw [size] at bins
  have volume : decoderFactor S d k attempts depth*n=
      12*((attempts*cards)*n)+12*(cards*n)+8*n+(keys*factor d S.degree depth)*n+2*(cards*n)+2*n := by
    dsimp only [decoderFactor,keys,cards];ring
  obtain ⟨outer,keyPos,archive⟩ := origin
  unfold archivesEnd
  change _≤ B+decoderFactor S d k attempts depth*n
  rw [volume]
  refine max_le ?_ (max_le ?_ (Finset.sup_le ?_))
  · rw [←Nat.mul_assoc attempts] at old; omega
  · omega
  · intro a _
    obtain ⟨first,flags,menus⟩ := archive a
    unfold eventEnds
    rw [size,countAt]
    change max ((v.shelf a).firstBase+keys*(factor d S.degree depth*n)) _ ≤ _
    rw [←Nat.mul_assoc keys]
    simp only [max_le_iff]
    omega

theorem Directory.joint_cover (v : Directory attempts) (S : PurchaseSampler) (h W k depth K G H R : ℕ) :
    (v.withCore h W K).Cover S h W k depth K G H (v.jointTop S h W k depth K G H R) := by
  let endAt := v.jointTop S h W k depth K G H R
  have base : CoreCatalogue.top h W K G H R≤ endAt := le_max_left ..
  have old : v.archivesEnd S h (2^W) k depth≤ endAt := le_max_right ..
  unfold CoreCatalogue.top at base
  unfold archivesEnd at old
  simp only [max_le_iff] at base old
  obtain ⟨_,_,os,ss⟩ := base
  obtain ⟨head,keys,events⟩ := old
  have part (a : Fin attempts) := (Finset.le_sup (f:=v.eventEnds S h (2^W) k depth) (Finset.mem_univ a)).trans events
  have site : CoreCatalogue.superStart h W+2*ProtocolRAMSupergroupDirectory.span K=CoreCatalogue.siteBase h W K := rfl
  have heap : Native.heapEnd h (2^W) Native.copies≤ CoreCatalogue.groupStart h W := le_max_left ..
  have first : CoreCatalogue.groupStart h W+ReportGroupROM.words h (2^W)=CoreCatalogue.superStart h W := rfl
  refine ⟨head,keys,by omega,by change CoreCatalogue.groupStart h W+_≤ endAt;omega,?_,by
    change CoreCatalogue.superStart h W+_≤ endAt;omega,os,ss,?_,?_⟩
  · intro a i
    have p := max_le_iff.mp (part a)
    exact ((v.shelf a).end_le S depth i (Nat.two_pow_pos _)).trans (((v.shelf a).final_after S depth i).trans p.1)
  · intro a
    exact (max_le_iff.mp (max_le_iff.mp (part a)).2).1
  · intro a
    exact (max_le_iff.mp (max_le_iff.mp (part a)).2).2

theorem Directory.joint_fits (v : Directory attempts) (S : PurchaseSampler) (h W k depth K G H R w out : ℕ)
    (low : v.jointTop S h W k depth K G H R≤ out) (room : out<2^w) :
    (CoreCatalogue.sourceAt h W k attempts R K G H (CoreCatalogue.pointBits h W)).All (Expr.Fits w out) ∧
      ((v.withCore h W K).source S h W k depth K G H).All (Expr.Fits w out) := by
  have data := v.joint_cover S h W k depth K G H R
  constructor
  · exact (CoreCatalogue.top_fits _ _ _ _ _ _ _ _ _ out ((le_max_left ..).trans low) room).all
  · apply Directory.source_fits _ _ _ _ _ _ _ _ _ out room
    exact ⟨data.outer.trans low,data.keys.trans low,data.ct.trans low,data.names.trans low,
      fun a i=>(data.source a i).trans low,data.super.trans low,data.offsets.trans low,data.sites.trans low,
      fun a=>(data.flags a).trans low,fun a=>(data.menus a).trans low⟩

/-- The calendar supplies its existing high-water bound for event archives.
The public packed directory and core image have their own proven linear bound,
so both sets of instructions fit simultaneously in the subdivision's actual
word width for all sufficiently large heights. -/
theorem eventually_joint_fits (S : PurchaseSampler) (W k attempts depth C : ℕ) (dirs : ℕ→Directory attempts)
    (archive : ∀ᶠ h : ℕ in Filter.atTop,(dirs h).archivesEnd S h (2^W) k depth≤ C*2^h) :
    ∀ᶠ h : ℕ in Filter.atTop,
      ∃ dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts))
        (2^superAddress W (2*ReportSockets.copies k attempts) h),
        let K:=Fintype.card (AllGroups h (2^W)); let R:=Fintype.card (Edges S h (2^W) k)
        let H:=2^superAddress W (2*ReportSockets.copies k attempts) h
        let out:=(dirs h).jointTop S h W k depth K dir.groups H R
        let w:=Native.wordBits h (2^W) Native.copies
        out<2^w ∧ (CoreCatalogue.sourceAt h W k attempts R K dir.groups H (CoreCatalogue.pointBits h W)).All (Expr.Fits w out) ∧
          (((dirs h).withCore h W K).source S h W k depth K dir.groups H).All (Expr.Fits w out) := by
  filter_upwards [archive,CoreCatalogue.eventually_fits S W k attempts,Native.eventually_append_room (2^W) Native.copies C] with h a fits room
  obtain ⟨dir,site⟩ := fits
  have endAt := max_lt site (a.trans_lt ((Nat.le_add_left _ _).trans_lt room))
  exact ⟨dir,endAt,(dirs h).joint_fits S h W k depth _ _ _ _ _ _ le_rfl endAt⟩

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
