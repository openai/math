import OAI.Hierarchy.ProtocolRAMBoughtCatalogueArena
import OAI.Hierarchy.ProtocolRAMColumnDirectory

namespace OAI
/-! # The column ID and two bought ordinal directories on one public tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.Public
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen ReportSockets CoreBoard Calendar
open scoped Classical Fin.CommRing
variable {w h W k attempts R K G H : ℕ}

def keyHead (S : PurchaseSampler) (base h W k depth : ℕ) : StockCommit.PortHeader :=
  StripDirectory.stratumHeader h (2^W) k S.degree depth (base+ColumnROM.words h (2^W) k)

def outerHead (S : PurchaseSampler) (base h W k attempts depth : ℕ) : StockCommit.PortHeader :=
  ⟨(keyHead S base h W k depth).stop,attempts,count h (2^W) k*paths h S.degree depth⟩

def endAddress (S : PurchaseSampler) (base h W k attempts depth : ℕ) :=
  (outerHead S base h W k attempts depth).stop

def load (S : PurchaseSampler) (base h W k attempts depth : ℕ) (m : Memory w) : Memory w :=
  (outerHead S base h W k attempts depth).load
    ((keyHead S base h W k depth).load (ColumnROM.load base h (2^W) k m))

def join (v : Directory attempts) (S : PurchaseSampler) (h W k depth K G H R : ℕ) : Directory attempts :=
  let base := CoreCatalogue.top h W K G H R
  { v.withCore h W K with
    keysBase := (keyHead S base h W k depth).start
    outerBase := (outerHead S base h W k attempts depth).start }

theorem stop_after (j : StockCommit.PortHeader) : j.start≤ j.stop := by
  dsimp [StockCommit.PortHeader.stop,StockCommit.PortHeader.parity,StockCommit.PortHeader.owner]
  omega

theorem borders (S : PurchaseSampler) (base h W k attempts depth : ℕ) :
    base+ColumnROM.words h (2^W) k≤ (keyHead S base h W k depth).stop ∧
      (keyHead S base h W k depth).stop≤ endAddress S base h W k attempts depth :=
  ⟨stop_after (keyHead ..),stop_after (outerHead ..)⟩

structure Resident (S : PurchaseSampler) (base h W k attempts depth : ℕ) (m : Memory w) : Prop where
  columns : ColumnROM.Resident base h (2^W) k m
  keys : (keyHead S base h W k depth).Loaded m
  outer : (outerHead S base h W k attempts depth).Loaded m

theorem resident (S : PurchaseSampler) (base h W k attempts depth : ℕ) (m : Memory w)
    (nFits : 2^h≤2^w) (wide : 0< w) (room : endAddress S base h W k attempts depth<2^w) :
    Resident S base h W k attempts depth (load S base h W k attempts depth m) := by
  let key := keyHead S base h W k depth
  let head := outerHead S base h W k attempts depth
  let col := ColumnROM.load base h (2^W) k m
  have ⟨a,b⟩ := borders S base h W k attempts depth
  have kFit : key.stop<2^w := b.trans_lt room
  have siteFit := ProtocolRAMPurchaseSampler.lt_span (siteLast h (2^W) k+1)
  have siteLo : ProtocolRAMPurchaseSampler.span (siteLast h (2^W) k+1)≤ ColumnROM.words h (2^W) k :=
    Nat.le_add_right ..
  refine ⟨?_,?_,head.load_ok _ wide room⟩
  · apply (ColumnROM.resident base h (2^W) k m (by omega) nFits).frame
    intro x lo hi
    exact (head.load_frame _ x (.inl (hi.trans_le a))).trans (key.load_frame col x (.inl hi))
  · apply (key.load_ok col wide kFit).frame
    intro x _ hi
    exact head.load_frame _ x (.inl hi)

theorem Resident.frame {S : PurchaseSampler} {base h W k attempts depth : ℕ} {m m' : Memory w}
    (origin : Resident S base h W k attempts depth m)
    (preserved : ∀x,base≤ x → x< endAddress S base h W k attempts depth → m' x=m x) :
    Resident S base h W k attempts depth m' := by
  have ⟨a,b⟩ := borders S base h W k attempts depth
  refine ⟨origin.columns.frame (fun x lo hi=>preserved x lo ((hi.trans_le a).trans_le b)),?_,?_⟩
  · apply origin.keys.frame
    intro x lo hi
    change base+_≤ x at lo
    exact preserved x (by omega) (hi.trans_le b)
  · apply origin.outer.frame
    intro x lo hi
    change (keyHead S base h W k depth).stop≤ x at lo
    exact preserved x (by omega) hi

theorem size (S : PurchaseSampler) (base h W k attempts depth : ℕ) :
    endAddress S base h W k attempts depth≤ base+
      (2*siteFactor (2^W) k+20+12*((attempts+1)*((2*rounds (2^W)+1)*(2*k)*S.degree^depth)))*2^h := by
  let key := keyHead S base h W k depth
  let outer := outerHead S base h W k attempts depth
  let n := 2^h
  let keys := (2*rounds (2^W)+1)*(2*k)
  let cards := keys*S.degree^depth
  have rows : count h (2^W) k*paths h S.degree depth=cards*n := by
    rw [count_eq];dsimp only [paths,n,cards,keys];ring
  have kb := key.span
  change key.stop≤ base+ColumnROM.words h (2^W) k+12*(count h (2^W) k*paths h S.degree depth)+8 at kb
  have ob := outer.span
  change outer.stop≤ key.stop+12*(attempts*(count h (2^W) k*paths h S.degree depth))+8 at ob
  rw [rows] at kb ob
  have col := ColumnROM.linear h (2^W) k (Nat.two_pow_pos _)
  have pos : 1≤ n := Nat.two_pow_pos _
  have volume : (2*siteFactor (2^W) k+20+12*((attempts+1)*cards))*n=
      (2*siteFactor (2^W) k+4)*n+16*n+12*(attempts*(cards*n))+12*(cards*n) := by ring
  change outer.stop≤ base+(2*siteFactor (2^W) k+20+12*((attempts+1)*cards))*n
  rw [volume]
  dsimp only [n] at kb ob pos ⊢
  omega


/-- Any directory selected by the actual stage-purchase bound can also
carry the quotient/remainder archives and global column decoder. The input
height threshold is independent of the chosen packed directory. -/
theorem eventually_width (S : PurchaseSampler) (W k attempts depth : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop,
      ∀ dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts))
        (2^superAddress W (2*copies k attempts) h),
        let H := 2^superAddress W (2*copies k attempts) h
        dir.groups*H≤2*(((2*rounds (2^W)+1)*4^(rounds (2^W)+1)*2^h)*copies k attempts)+H →
        endAddress S (CoreCatalogue.top h W (Fintype.card (AllGroups h (2^W))) dir.groups H
          (Fintype.card (Edges S h (2^W) k))) h W k attempts depth<2^Native.wordBits h (2^W) Native.copies := by
  obtain ⟨A,core⟩ := CoreCatalogue.affordable_directory S W k attempts
  let B := 2*siteFactor (2^W) k+20+12*((attempts+1)*((2*rounds (2^W)+1)*(2*k)*S.degree^depth))
  filter_upwards [Native.eventually_append_room (2^W) Native.copies (A+B)] with h room
  intro dir H packed
  have base := core h dir packed
  have high := size S (CoreCatalogue.top h W (Fintype.card (AllGroups h (2^W))) dir.groups H
    (Fintype.card (Edges S h (2^W) k))) h W k attempts depth
  have some := Nat.add_le_add_right base (B*2^h)
  exact high.trans_lt (some.trans_lt (by rw [←Nat.add_mul];omega))

end Hierarchy.ProtocolRAM.BoughtSockets.Public
end

end OAI
