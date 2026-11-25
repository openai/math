import OAI.Hierarchy.ProtocolRAMCalendarMenuROM

namespace OAI
/-! # Mounting the two actual priced packet catalogues in the shared boot image -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripDirectory
open scoped Classical Fin.CommRing
namespace MenuROM
variable {z d k N phases shapes jobs U V X Y w : ℕ}

theorem Pages.Resident.move {p : Pages phases U V} {m after : Memory w} (old : p.Resident m)
    (order : p.Ordered) (equal : ∀x,p.base≤x→x<p.stop→after x=m x) : p.Resident after := by
  have left : p.left.base≤p.left.stop := Nat.le_add_right ..
  have right : p.right.base≤p.right.stop := Nat.le_add_right ..
  have la : p.leftAlphabet.base≤p.leftAlphabet.stop := Nat.le_add_right ..
  have ra : p.rightAlphabet.base≤p.rightAlphabet.stop := Nat.le_add_right ..
  obtain ⟨o₁,o₂,o₃⟩ := order
  exact ⟨old.left.frame fun x lo hi=>equal x lo (by unfold Pages.stop;omega),
    old.right.frame fun x lo hi=>equal x (by unfold Pages.base;omega) (by unfold Pages.stop;omega),
    old.leftAlphabet.frame fun x lo hi=>equal x (by unfold Pages.base;omega) (by unfold Pages.stop;omega),
    old.rightAlphabet.frame fun x lo hi=>equal x (by unfold Pages.base;omega) hi⟩

theorem Pages.master (p : Pages phases U V) (ord : p.Ordered)
    (b : JointHeader.Board) (phase : Fin phases→PhasePrice) (π : Equiv.Perm (Fin (2^z)))
    (stock : ℕ→ℕ) (rest : Boot.Tape z d) (port : PortROM.Table shapes) (scalar : ScalarROM.Table phases)
    (old : DiscrepancyROM.Table phases X) (newer : DiscrepancyROM.Table phases Y)
    (v : Fin jobs→Market z d k) {size : ℕ} (layout : Boot.Layout v size) (hd : 1≤d)
    (first : 2^z≤b.initial) (scores : JointHeader.stop b z N k phases≤port.base)
    (heap : heapEnd z d copies≤port.base) (ports : port.stop≤ scalar.base) (lower : scalar.stop≤old.base)
    (disc : old.stop≤newer.base) (menus : newer.stop≤p.base)
    (before : ∀i,p.stop≤Boot.low (v i)) (room : p.stop≤ size)
    (pfit : p.left.entries≤2^wordBits z d copies) (rfit : p.right.entries≤2^wordBits z d copies)
    (afit : p.leftAlphabet.entries≤2^wordBits z d copies) (bfit : p.rightAlphabet.entries≤2^wordBits z d copies) :
    let extra := DiscrepancyROM.both old newer (p.words rest)
    let words := JointHeader.words b z d N k phase π stock (port.words (scalar.words extra))
    p.Resident (Boot.booted v size words) := by
  dsimp only
  let extra := DiscrepancyROM.both old newer (p.words rest)
  apply (p.resident rest ord pfit rfit afit bfit).move ord
  intro x lo hi
  have oo : old.base≤old.stop := Nat.le_add_right ..
  have nn : newer.base≤newer.stop := Nat.le_add_right ..
  have endN := menus.trans lo
  have endO := disc.trans (nn.trans endN)
  exact (JointHeader.tail_origin b phase π stock extra port scalar v layout hd first scores heap ports
      x (lower.trans (oo.trans endO)) (fun i=>hi.trans_le (before i)) (hi.trans_le room)).trans
    ((newer.outside _ (.inr endN)).trans (old.outside _ (.inr endO)))

end MenuROM
namespace StripChart
variable {z d k q depth phases : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "Q₁" => Fintype.card (PayloadStrip.Quotes N k)
local notation "Q₂" => Fintype.card (ChainStrip.Axes depth k)

variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (s : Boards z d k q depth) (t : TreeCosts)

def menuPages (base leftRadix rightRadix : ℕ) (phase : Fin phases→PhasePrice) : MenuROM.Pages phases Q₁ Q₂ :=
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,s.positive⟩⟩
  letI : Nonempty (PurchasedRole depth k) := ⟨.catalyst (ChainStrip.inlet depth 0) ⟨0,s.positive⟩⟩
  let a := payloadMenu F N k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    t.payload t.payload_nonneg s.minimum
  let b := purchasedMenu F depth k s.positive s.radius s.radius_nonneg s.tolerance s.tolerance_pos
    t.purchase t.purchase_nonneg s.minimum
  let left := MenuROM.menus a base leftRadix (fun u key=>
    PayloadStrip.prices N k s.radius (payloadGrid leftRadix (phase u).precision key))
  let right := MenuROM.menus b left.stop rightRadix (fun u key=>
    phaseGrid (depth:=depth) (k:=k) (phase u) s.radius rightRadix key)
  let first := MenuROM.alphabets a right.stop
  ⟨left,right,first,MenuROM.alphabets b first.stop⟩

theorem menu_ordered (base pl pr : ℕ) (phase : Fin phases→PhasePrice) :
    (menuPages F s t base pl pr phase).Ordered := ⟨le_rfl,le_rfl,le_rfl⟩

/-- Both the packet-code lookup and the histogram-alphabet load are placed
in the true initial read-only header outside all private selector spans. -/
def withMenuROM (base pl pr : ℕ) (phase : Fin phases→PhasePrice) (phaseAt : Attempt→Fin phases) :
    Boards z d k q depth :=
  let p := menuPages F s t base pl pr phase
  { s with
    tree := t.atAttempt
    tree_nonneg := t.nonneg
    outer := fun j a =>
      let b := s.outer j a
      { b with
        menu := p.left.bank (phaseAt (.outer j a))
        terms := p.leftAlphabet.bank 0
        test := { b.test with radix := pl } }
    inner := fun j a u h =>
      let b := s.inner j a u h
      { b with
        menu := p.right.bank (phaseAt (.inner j a u h))
        terms := p.rightAlphabet.bank 0
        test := { b.test with radix := pr } } }

theorem menu_stop (base pl pr : ℕ) (phase : Fin phases→PhasePrice) :
    let p := menuPages F s t base pl pr phase
    p.stop=base+phases*p.left.size+phases*p.right.size+p.leftAlphabet.size+p.rightAlphabet.size := by
  have consecutive {L R : ℕ} (p : MenuROM.Pages phases L R) (start : p.left.base=base)
      (right : p.right.base=p.left.stop) (first : p.leftAlphabet.base=p.right.stop)
      (last : p.rightAlphabet.base=p.leftAlphabet.stop) :
      p.stop=base+phases*p.left.size+phases*p.right.size+p.leftAlphabet.size+p.rightAlphabet.size := by
    change p.rightAlphabet.base+1*p.rightAlphabet.size=_
    rw [last,DiscrepancyROM.Table.stop,first,DiscrepancyROM.Table.stop,right,
      DiscrepancyROM.Table.stop,start,one_mul,one_mul]
  exact consecutive (menuPages F s t base pl pr phase) rfl rfl rfl rfl

end StripChart
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
