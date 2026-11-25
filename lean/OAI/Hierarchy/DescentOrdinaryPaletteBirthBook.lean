import OAI.Hierarchy.DescentOrdinaryPaletteBirth
import OAI.Hierarchy.DescentOrdinaryPaletteBirthSweep
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # Running the native birth-column publisher with the original global coefficient dictionary -/
namespace Hierarchy.DescentOrdinaryPaletteBirth
open DescentKernelHistory DescentSixParty DescentPrimitivePalette DescentCompiler
open DescentSIMDLookup DescentPackedColony DescentOrdinaryBorn DescentSixParty.Chronology
open DescentStaticWordColumn (names)
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (seed Z : ℕ) (op : RotorSpec) (B : Chart)
local notation "law_" => published G seed Z op B
def phase (old : Bank) (at_ w : ℕ) := Native.phase B law_ old at_ w
abbrev cpu := Native.cpu B
abbrev textCost := Native.textCost B

theorem any {w} (old : Bank) (at_ : ℕ) (m : Memory w) (early : old.Fits w at_) (room : roof B at_<2^w) :
    let stage:=phase G seed Z op B old at_ w
    stage.Runs m ∧ ∀a,a<at_ ∨ roof B at_≤a → stage.image m a=m a :=
  Native.any B law_ (blank G seed Z op B) old at_ m early room

theorem posted {w} (old : Bank) (at_ : ℕ) (m : Memory w) (early : old.Fits w at_)
    (v : Fin B.hosts→Fin B.groups→Cell B.chipBits) (oldRows : B.rows≤old.size)
    (read : Reads old v B.lanes m) (room : roof B at_<2^w) (i : Fin (fields B)) :
    Reads (bank B at_ i) (fun h g=>law_ i (v h g)) B.lanes ((phase G seed Z op B old at_ w).image m) :=
  Native.posted B law_ (blank G seed Z op B) old at_ m early v oldRows read room i

/-- In the admitted word width the entire packed value, including ragged tail lanes,
    is present at the physical output address as an ordinary natural number. -/
theorem posted_word {w} (old : Bank) (at_ : ℕ) (m : Memory w) (early : old.Fits w at_)
    (v : Fin B.hosts→Fin B.groups→Cell B.chipBits) (oldRows : B.rows≤old.size)
    (read : Reads old v B.lanes m) (room : roof B at_<2^w) (bitsFit : printedBits G seed Z op*B.lanes≤w)
    (i : Fin (fields B)) (a : Row B.hosts B.groups B.lanes) :
    (((phase G seed Z op B old at_ w).image m) ((bank B at_ i).base+(row B.hosts B.groups B.lanes a).val)).val=
      (data (fun h g=>law_ i (v h g)) a).val :=by
  let word_:=data (fun h g=>law_ i (v h g)) a
  have bounded : word_.val<2^w:=word_.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) bitsFit)
  exact (congrArg Fin.val (posted G seed Z op B old at_ m early v oldRows read room i a)).trans
    (Fin.val_cast_of_lt bounded)

theorem placed {w} (at_ : ℕ) (room : roof B at_<2^w) (i : Fin (fields B)) :
    (bank B at_ i).Fits w (roof B at_) ∧ B.rows≤(bank B at_ i).size :=
  Native.placed B at_ room i

theorem price (old : Bank) (at_ w : ℕ) :
    (phase G seed Z op B old at_ w).ticks≤cpu B ∧ names (phase G seed Z op B old at_ w).program≤textCost B :=
  Native.price B law_ old at_ w

/-- Changing the dated coefficient exponent changes only the contents stored
in the ROM. The command, table extent, and output banks have the same budget. -/
theorem scale_price (z : ℕ) (old : Bank) (at_ w : ℕ) :
    let dated:={B with scale:=z}
    let issue:=phase G seed Z op dated old at_ w
    roof dated at_=roof B at_ ∧ (∀i : Fin (fields B),bank dated at_ i=bank B at_ i) ∧
      issue.ticks≤cpu B ∧ names issue.program≤textCost B :=
  ⟨rfl,fun _=>rfl,price G seed Z op {B with scale:=z} old at_ w⟩

theorem scale_invoice (z : ℕ) (old : Bank) (at_ w : ℕ) :
    (phase G seed Z op {B with scale:=z} old at_ w).wordInvoice≤(cpu B+7*textCost B)*w:=by
  obtain ⟨_,_,ticks,hardware⟩:=scale_price G seed Z op B z old at_ w
  exact Nat.mul_le_mul_right _ (Nat.add_le_add ticks (Nat.mul_le_mul_left 7 hardware))

/-- The admitted packed word contains the coefficient at the supplied date
exponent, with the same host lanes and printed bit width. -/
theorem posted_scale_word {w} (z : ℕ) (old : Bank) (at_ : ℕ) (m : Memory w) (early : old.Fits w at_)
    (v : Fin B.hosts→Fin B.groups→Cell B.chipBits) (oldRows : B.rows≤old.size)
    (read : Reads old v B.lanes m) (room : roof B at_<2^w) (bitsFit : printedBits G seed Z op*B.lanes≤w)
    (i : Fin (fields B)) (a : Row B.hosts B.groups B.lanes) :
    let dated:={B with scale:=z}
    (((phase G seed Z op dated old at_ w).image m) ((bank B at_ i).base+(row B.hosts B.groups B.lanes a).val)).val=
      (data (fun h g=>published G seed Z op dated i (v h g)) a).val :=
  posted_word G seed Z op {B with scale:=z} old at_ m early v oldRows read room bitsFit i a

end
end Hierarchy.DescentOrdinaryPaletteBirth

end OAI
