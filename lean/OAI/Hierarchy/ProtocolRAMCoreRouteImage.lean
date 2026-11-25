import OAI.Hierarchy.ProtocolRAMCorePadded
import OAI.Hierarchy.ProtocolRAMCoreRouteHops
import OAI.Hierarchy.ProtocolRAMBoughtCataloguePaid

namespace OAI
/-! # Public edge-ordinal ROM on the very same core and acquired route tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets BoughtSockets CatalogueRows
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {z W k attempts R K H tables phases jobs : ℕ} {S : PurchaseSampler}

def directoryBase (S : PurchaseSampler) (z W k attempts depth K G H R : ℕ) :=
  Public.endAddress S (CoreCatalogue.top z W K G H R) z W k attempts depth

def stop (S : PurchaseSampler) (z W k attempts depth K G H R : ℕ) :=
  directoryBase S z W k attempts depth K G H R+CoreLookup.words S z (2^W) k

def source (S : PurchaseSampler) (z W k attempts depth K G H R : ℕ) : Source :=
  addresses (directoryBase S z W k attempts depth K G H R) (CoreCatalogue.top z W K G H R)
    (CoreCatalogue.groupStart z W) (CoreCatalogue.siteBase z W K) (CoreCatalogue.superStart z W) K G H

theorem columns_sites (z d k : ℕ) : Fintype.card (CoreBoard.Columns z d)≤ siteLast z d k+1 := by
  have iso := Fintype.card_congr (siteNumber z d k)
  simp only [Fintype.card_fin] at iso
  exact (Fintype.card_le_of_injective (fun c : CoreBoard.Columns z d=>((c,none) : Site z d k))
    (fun _ _ eq=>congrArg Prod.fst eq)).trans_eq iso

theorem column_count (z d k : ℕ) (hd : 1≤ d) : Fintype.card (CoreBoard.Columns z d)≤ siteFactor d k*2^z :=
  (columns_sites z d k).trans (site_count z d k hd)

def factor (S : PurchaseSampler) (d k : ℕ) :=
  Fintype.card (CoreLookup.Channel S.degree (18*(d-1)+1) k)*(2*(siteFactor d k+2))

theorem words_linear (S : PurchaseSampler) (z d k : ℕ) (hd : 1≤ d) :
    CoreLookup.words S z d k≤ factor S d k*2^z := by
  let n := 2^z
  have sites := column_count z d k hd
  have pos : 1≤ n := Nat.two_pow_pos _
  have cap : CoreLookup.positions z d≤ (siteFactor d k+1)*n := by
    unfold CoreLookup.positions
    rw [Nat.add_mul,Nat.one_mul]
    exact max_le (by change _≤ siteFactor d k*2^z+2^z;omega) (Nat.le_add_left ..)
  have rounded := ProtocolRAMPurchaseSampler.span_le (CoreLookup.positions z d)
  have stride : CoreLookup.stride z d≤ 2*(siteFactor d k+2)*n := by
    change ProtocolRAMPurchaseSampler.span _≤ _
    have eq : 2*(siteFactor d k+2)*n=2*((siteFactor d k+1)*n+n) := by ring
    rw [eq];omega
  unfold CoreLookup.words factor
  rw [show Stages z d=18*(d-1)+1 from CoreCatalogue.total_stages z d,Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ stride

theorem eventually_width (S : PurchaseSampler) (W k attempts depth : ℕ) :
    ∀ᶠ z : ℕ in Filter.atTop,
      ∀ dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts))
        (2^superAddress W (2*copies k attempts) z),
        let H := 2^superAddress W (2*copies k attempts) z
        dir.groups*H≤2*(((2*rounds (2^W)+1)*4^(rounds (2^W)+1)*2^z)*copies k attempts)+H →
        stop S z W k attempts depth (Fintype.card (AllGroups z (2^W))) dir.groups H
          (Fintype.card (Edges S z (2^W) k))<2^Native.wordBits z (2^W) Native.copies := by
  obtain ⟨A,core⟩ := CoreCatalogue.affordable_directory S W k attempts
  let B := 2*siteFactor (2^W) k+20+12*((attempts+1)*((2*rounds (2^W)+1)*(2*k)*S.degree^depth))
  let D := factor S (2^W) k
  filter_upwards [Native.eventually_append_room (2^W) Native.copies (A+B+D)] with z word
  intro dir H packed
  have base := core z dir packed
  have upper := Public.size S (CoreCatalogue.top z W (Fintype.card (AllGroups z (2^W))) dir.groups H
    (Fintype.card (Edges S z (2^W) k))) z W k attempts depth
  have wid := words_linear S z (2^W) k (Nat.two_pow_pos _)
  change _≤ _+B*2^z at upper
  change _≤ D*2^z at wid
  unfold stop directoryBase
  have ub := Nat.add_le_add (upper.trans (Nat.add_le_add_right base _)) wid
  apply ub.trans_lt
  rw [←Nat.add_mul,←Nat.add_mul]
  omega

theorem public_above {w : ℕ} (S : PurchaseSampler) (base z W k attempts depth : ℕ) (m : Memory w) (x : ℕ)
    (above : Public.endAddress S base z W k attempts depth≤ x) :
    Public.load S base z W k attempts depth m x=m x := by
  have ⟨keys,outer⟩ := Public.borders S base z W k attempts depth
  unfold Public.load
  rw [StockCommit.PortHeader.load_frame _ _ _ (.inr above),
    StockCommit.PortHeader.load_frame _ _ _ (.inr (outer.trans above)),
    ColumnROM.frame _ _ _ _ _ _ (.inr ((keys.trans outer).trans above))]

/-- The complete public prefix nested inside the port and economic directories. -/
def low (order : Fin R≃Edges S z (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (depth : ℕ) (rest : Boot.Tape z (2^W)) : Boot.Tape z (2^W) :=
  CoreCatalogue.initial order M groups packed
    (Public.load S (CoreCatalogue.top z W K packed.groups H R) z W k attempts depth
      (CoreLookup.mount (directoryBase S z W k attempts depth K packed.groups H R) order rest))

theorem low_above (order : Fin R≃Edges S z (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (depth : ℕ) (rest : Boot.Tape z (2^W)) (x : ℕ)
    (above : stop S z W k attempts depth K packed.groups H R≤ x) :
    low order M groups packed depth rest x=rest x := by
  let base := CoreCatalogue.top z W K packed.groups H R
  have ⟨keys,outer⟩ := Public.borders S base z W k attempts depth
  have dir : directoryBase S z W k attempts depth K packed.groups H R≤ x := (Nat.le_add_right ..).trans above
  have top : base≤ x := (Nat.le_add_right ..).trans (keys.trans (outer.trans dir))
  unfold low
  rw [Public.core_above order M groups packed _ x top,public_above S base z W k attempts depth _ x dir,
    CoreLookup.mount_outside _ order rest x (.inr above)]

structure Seen (order : Fin R≃Edges S z (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (v : Directory attempts) (depth : ℕ) (π : Equiv.Perm (Fin (2^z))) (m : Boot.Tape z (2^W)) : Prop where
  board : Public.Readback order M groups packed v depth π m
  padded : CoreLookup.Padded (directoryBase S z W k attempts depth K packed.groups H R) order m

theorem Seen.lookup {order : Fin R≃Edges S z (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups z (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^z))} {m : Boot.Tape z (2^W)}
    (seen : Seen order M groups packed v depth π m) :
    CoreLookup.Loaded (directoryBase S z W k attempts depth K packed.groups H R) order m :=
  seen.padded.loaded

theorem Seen.readable {order : Fin R≃Edges S z (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups z (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^z))} {m : Boot.Tape z (2^W)}
    (seen : Seen order M groups packed v depth π m)
    (space : directoryBase S z W k attempts depth K packed.groups H R≤2^Native.wordBits z (2^W) Native.copies) :
    Readable (source S z W k attempts depth K packed.groups H R) S z W k attempts order π m := by
  have ⟨first,last⟩ := Public.borders S (CoreCatalogue.top z W K packed.groups H R) z W k attempts depth
  have small := ProtocolRAMPurchaseSampler.lt_span (siteLast z (2^W) k+1)
  have bank : ProtocolRAMPurchaseSampler.span (siteLast z (2^W) k+1)≤ ColumnROM.words z (2^W) k := Nat.le_add_right ..
  have cols := columns_sites z (2^W) k
  change Public.endAddress S _ z W k attempts depth≤ _ at space
  exact ⟨⟨groups,packed,rfl,seen.board.columns⟩,seen.board.input,seen.lookup,
    (Native.height_extent z (2^W)).trans (Native.extent_word z (2^W) Native.copies).le,by omega⟩

set_option cleanup.letToHave false in
theorem start (order : Fin R≃Edges S z (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups z (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z W (copies k attempts)) H)
    (joint : JointHeader.Board) (ports : PortROM.Table tables) (N depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^z))) (stock : ℕ→ℕ) (rest : Boot.Tape z (2^W))
    (markets : Fin jobs→Market z (2^W) k) {size : ℕ} (layout : Boot.Layout markets size) (v : Directory attempts)
    (space : let last := stop S z W k attempts depth K packed.groups H R
      last≤ joint.initial ∧ last≤ ports.base ∧ last≤ size ∧ last<2^Native.wordBits z (2^W) Native.copies ∧
      ∀j,last≤ Boot.low (markets j)) :
    let dirBase := directoryBase S z W k attempts depth K packed.groups H R
    let words := Public.words order M groups packed joint ports N depth phase π stock (CoreLookup.mount dirBase order rest)
    let mid := Boot.booted markets size words
    (Native.subdivisionProgram z (2^W)).Exec (Boot.initial markets size words) mid (Native.subdivisionConstant (2^W)*2^z) ∧
      Boot.Receipt markets π (Computability.VPVNP.RAMMemory.initialMemory size words) mid ∧ Seen order M groups packed v depth π mid := by
  let base := CoreCatalogue.top z W K packed.groups H R
  let endAt := directoryBase S z W k attempts depth K packed.groups H R
  let last := stop S z W k attempts depth K packed.groups H R
  let withROM := CoreLookup.mount endAt order rest
  let archive := Public.load S base z W k attempts depth withROM
  have lower : endAt≤ last := Nat.le_add_right ..
  have ⟨first,second⟩ := Public.borders S base z W k attempts depth
  have cap : base≤ endAt := (Nat.le_add_right ..).trans (first.trans second)
  have header : CoreCatalogue.headBase z W K packed.groups H+CoreCatalogue.headerWords R≤ base :=
    (le_max_left ..).trans (le_max_right ..)
  have origin : CoreCatalogue.groupStart z W≤ base := by
    unfold CoreCatalogue.headBase SiteROM.endAddress CoreCatalogue.superStart at header
    omega
  obtain ⟨jointLo,portsLo,memLo,word,marketsLo⟩ := space
  obtain ⟨exec,receipt,read⟩ := Public.start order M groups packed joint ports N depth phase π stock withROM markets layout v
    ⟨lower.trans jointLo,lower.trans portsLo,lower.trans memLo,lower.trans_lt word,fun j=>lower.trans (marketsLo j)⟩
  refine ⟨exec,receipt,read,(CoreLookup.mount_padded endAt order rest).frame ?_⟩
  intro a lo hi
  have high := origin.trans (cap.trans lo)
  have got := receipt.kept a ((le_max_left ..).trans high) (fun j used=>Nat.not_lt_of_ge used.1 (hi.trans_le (marketsLo j)))
  rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le memLo)] at got
  exact got.trans ((CoreCatalogue.master_retains order M groups packed joint ports N phase π stock archive a
    ((le_max_right ..).trans high) (hi.trans_le jointLo) (hi.trans_le portsLo)).trans
    ((Public.core_above order M groups packed archive a (cap.trans lo)).trans (public_above S base z W k attempts depth withROM a lo)))

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
