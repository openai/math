import OAI.Hierarchy.ProtocolRAMCoreCatalogueSource

namespace OAI
/-! # Core catalogue from a raw permutation and the fixed directory words -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
variable {w h W k R K H attempts : ℕ} {S : PurchaseSampler}

def groupStart (h W : ℕ) := max (Native.heapEnd h (2^W) Native.copies) (2^h)
def superStart (h W : ℕ) := groupStart h W + ReportGroupROM.words h (2^W)
def siteBase (h W K : ℕ) := superStart h W + 2*ProtocolRAMSupergroupDirectory.span K
def headBase (h W K G H : ℕ) := SiteROM.endAddress (superStart h W) G H K

def initial (order : Fin R ≃ Edges S h (2^W) k) (M : ℕ) (groups : Fin K ≃ AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H)
    (raw : Memory (Native.wordBits h (2^W) Native.copies)) :=
  mountHeader order (headBase h W K dir.groups H) attempts (groupStart h W) M
    (SiteROM.image (superStart h W) groups dir
      (ReportGroupROM.load (groupStart h W) groups PurchaseCT.groupNumber raw))

def sourceAt (h W k attempts R K G H bits : ℕ) :=
  source (headBase h W K G H) R bits (siteBase h W K) (superStart h W) K G H k attempts

structure PublicTables (order : Fin R ≃ Edges S h (2^W) k) (M : ℕ) (groups : Fin K ≃ AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H) (m : Memory w) : Prop where
  header : Header order (headBase h W K dir.groups H) attempts (groupStart h W) M m
  names : ReportGroupROM.Resident (groupStart h W) groups PurchaseCT.groupNumber m
  sites : SiteROM.Resident dir (siteBase h W K) m
  tables : ∀g,let idx:=((groups.symm g).val:Word w)
    (ProtocolRAMSupergroupDirectory.groupBank (superStart h W) K).read m idx=((dir.group g).val:Word w) ∧
    (ProtocolRAMSupergroupDirectory.offsetBank (superStart h W) K).read m idx=(dir.base g:Word w)

theorem publicTables (order : Fin R ≃ Edges S h (2^W) k) (M : ℕ) (groups : Fin K ≃ AllGroups h (2^W))
    (dir : Directory (reserved h W (copies k attempts)) H)
    (raw finish : Memory (Native.wordBits h (2^W) Native.copies))
    (keep : ∀a,groupStart h W≤ a → a< headBase h W K dir.groups H+headerWords R → finish a=initial order M groups dir raw a)
    (kFit : K≤2^Native.wordBits h (2^W) Native.copies)
    (slotsFit : ReportGroupROM.stride h (2^W)≤2^Native.wordBits h (2^W) Native.copies) :
    PublicTables order M groups dir finish := by
  let w := Native.wordBits h (2^W) Native.copies
  let first := groupStart h W
  let split := superStart h W
  let loc := siteBase h W K
  let hdr := headBase h W K dir.groups H
  let remapped := ReportGroupROM.load first groups PurchaseCT.groupNumber raw
  let withSites := SiteROM.image split groups dir remapped
  let raw' := initial order M groups dir raw
  have hd : 1≤2^W := Nat.two_pow_pos _
  have afterHeap : Native.heapEnd h (2^W) Native.copies≤ first := le_max_left ..
  have nLow : 2^h≤ first := le_max_right ..
  have head : first≤ split := Nat.le_add_right ..
  have border : split≤ loc := Nat.le_add_right ..
  have tail : loc≤ hdr := Nat.le_add_right ..
  have header : Header order hdr attempts first M finish :=
    (mountHeader_read order hdr attempts first M withSites).frame (fun a low hi => keep a (by omega) hi)
  have beforeHeader (a : ℕ) (lo : first≤ a) (hi : a< hdr) : finish a=withSites a :=
    (keep a lo (hi.trans_le (Nat.le_add_right ..))).trans (mountHeader_outside order hdr attempts first M withSites a (.inl hi))
  have names : ReportGroupROM.Resident first groups PurchaseCT.groupNumber finish := by
    apply ReportGroupROM.of_frame (ReportGroupROM.resident first groups PurchaseCT.groupNumber raw hd slotsFit)
    intro a lo hi
    change a< split at hi
    exact (beforeHeader a lo (by omega)).trans (SiteROM.image_frame split groups dir remapped a (.inl hi))
  have sites : SiteROM.Resident dir loc finish := by
    apply (SiteROM.image_site split groups dir remapped).frame
    intro a lo hi
    exact beforeHeader a (by omega) hi
  have equalRead (b : Bank) (low : split≤ b.base) (high : b.base+b.size≤ hdr) (idx : Word w) :
      b.read finish idx=b.read withSites idx := by
    have digit := Nat.mod_lt idx.val (Nat.two_pow_pos b.bits)
    change idx.val % b.size < b.size at digit
    exact beforeHeader _ (by omega) (by omega)
  have super (g : AllGroups h (2^W)) :
      let idx := ((groups.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank split K).read finish idx=((dir.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank split K).read finish idx=(dir.base g:Word w) := by
    intro idx
    have total : split+2*ProtocolRAMSupergroupDirectory.span K≤ hdr := tail
    have left := equalRead (ProtocolRAMSupergroupDirectory.groupBank split K) (le_rfl) (by
      change split+ProtocolRAMSupergroupDirectory.span K≤ hdr; omega) idx
    have right := equalRead (ProtocolRAMSupergroupDirectory.offsetBank split K) (Nat.le_add_right ..) (by
      change split+ProtocolRAMSupergroupDirectory.span K+ProtocolRAMSupergroupDirectory.span K≤ hdr; omega) idx
    have lookup := SiteROM.image_directory split groups dir remapped kFit g
    exact ⟨left.trans lookup.1,right.trans lookup.2⟩
  exact ⟨header,names,sites,super⟩

/-- Readback in any memory containing the actual numbered CT data and the
unchanged format tables on their precise half-open interval. -/
theorem rows_of_retained (order : Fin R ≃ Edges S h (2^W) k) (bits M : ℕ)
    (groups : Fin K ≃ AllGroups h (2^W)) (dir : Directory (reserved h W (copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (raw finish : Memory (Native.wordBits h (2^W) Native.copies))
    (ct : Geometry π finish (2^W))
    (keep : ∀a,groupStart h W≤ a → a< headBase h W K dir.groups H+headerWords R → finish a=initial order M groups dir raw a)
    (rooms : let w := Native.wordBits h (2^W) Native.copies
      R≤2^w ∧ K≤2^w ∧ dir.groups≤2^w ∧ dir.groups*H≤2^w ∧
      ReportGroupROM.stride h (2^W)≤2^w ∧ superStart h W≤2^bits ∧ 2^bits≤2^w) :
    Rows (sourceAt h W k attempts R K dir.groups H bits) order dir π M finish := by
  obtain ⟨rFit,kFit,gFit,sitesFit,slotsFit,accessible,wide⟩ := rooms
  let w := Native.wordBits h (2^W) Native.copies
  have pubs := publicTables order M groups dir raw finish keep kFit slotsFit
  have nFit : 2^h≤2^w := (Native.height_extent h (2^W)).trans (Native.extent_word h (2^W) Native.copies).le
  have afterHeap : Native.heapEnd h (2^W) Native.copies≤ groupStart h W := le_max_left ..
  have head : groupStart h W≤ superStart h W := Nat.le_add_right ..
  have width : 0< w := by dsimp [w,Native.wordBits];omega
  exact source_read order _ bits _ _ _ M groups dir π finish pubs.header ct pubs.names pubs.sites pubs.tables
    width rFit nFit wide (afterHeap.trans (head.trans accessible)) accessible gFit sitesFit

/-- The only data in the initial tape depending on the input permutation are
its raw words. From the exact terminal memory of the native CT subdivision,
the fixed five serializer expressions decode every true core edge. -/
theorem raw_run (order : Fin R ≃ Edges S h (2^W) k) (bits M : ℕ)
    (groups : Fin K ≃ AllGroups h (2^W)) (dir : Directory (reserved h W (copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (raw : Memory (Native.wordBits h (2^W) Native.copies))
    (input : ∀ r : Fin (2^h), raw r.val=((π r).val:Word _))
    (rooms : let w := Native.wordBits h (2^W) Native.copies
      R≤2^w ∧ K≤2^w ∧ dir.groups≤2^w ∧ dir.groups*H≤2^w ∧
      ReportGroupROM.stride h (2^W)≤2^w ∧ superStart h W≤2^bits ∧ 2^bits≤2^w) :
    let raw' := initial order M groups dir raw
    let start := Native.inputTape h (2^W) _ raw'
    let finish := Native.images h (2^W) start (rounds (2^W))
    (Native.subdivisionProgram h (2^W)).Exec start finish (Native.subdivisionConstant (2^W)*2^h) ∧
      Rows (sourceAt h W k attempts R K dir.groups H bits) order dir π M finish := by
  obtain ⟨rFit,kFit,gFit,sitesFit,slotsFit,accessible,wide⟩ := rooms
  let w := Native.wordBits h (2^W) Native.copies
  let first := groupStart h W
  let split := superStart h W
  let loc := siteBase h W K
  let hdr := headBase h W K dir.groups H
  let remapped := ReportGroupROM.load first groups PurchaseCT.groupNumber raw
  let withSites := SiteROM.image split groups dir remapped
  let raw' := initial order M groups dir raw
  let start := Native.inputTape h (2^W) _ raw'
  let finish := Native.images h (2^W) start (rounds (2^W))
  have hd : 1≤2^W := Nat.two_pow_pos _
  have nFit : 2^h≤2^w := (Native.height_extent h (2^W)).trans (Native.extent_word h (2^W) Native.copies).le
  have afterHeap : Native.heapEnd h (2^W) Native.copies≤ first := le_max_left ..
  have nLow : 2^h≤ first := le_max_right ..
  have head : first≤ split := Nat.le_add_right ..
  have border : split≤ loc := Nat.le_add_right ..
  have tail : loc≤ hdr := Nat.le_add_right ..
  have input' (r : Fin (2^h)) : raw' r.val=((π r).val:Word w) := by
    have low := r.isLt.trans_le nLow
    change mountHeader order hdr attempts first M withSites r.val=_
    rw [mountHeader_outside _ _ _ _ _ _ _ (.inl (by omega))]
    change SiteROM.image split groups dir remapped r.val=_
    rw [SiteROM.image_frame _ _ _ _ _ (.inl (by omega))]
    exact (ReportGroupROM.frame first groups PurchaseCT.groupNumber raw _ (.inl low)).trans (input r)
  obtain ⟨ran,ct,retains⟩ := geometry_run hd π raw' input'
  have keep (a : ℕ) (lo : first≤ a) : finish a=raw' a := retains a (afterHeap.trans lo)
  exact ⟨ran,rows_of_retained order bits M groups dir π raw finish ct (fun a lo _ => keep a lo)
    ⟨rFit,kFit,gFit,sitesFit,slotsFit,accessible,wide⟩⟩

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
