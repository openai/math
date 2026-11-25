import OAI.Hierarchy.DescentDatedResetWindows
import OAI.Hierarchy.DescentPackedCanvasExtent

namespace OAI
/-! # The real pre-estimator census, immutable flow book and measured source pitch -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup
open DescentPackedWalsh DescentPackedFlowPublication DescentPackedRectangle DescentDatedAddressBook ProtocolRAM Filter
noncomputable section
variable {ι : ℕ→Type*}

theorem aperture_rate (H D u l b short M k pay : ∀h,ι h→ℕ)
    (hosts : Bounded H) (ports : Bounded D) (radix : Bounded (fun h i=>2^(k h i)))
    (axes : Bounded (fun h i=>2^(u h i+l h i)))
    (payload : ∃C : ℕ,∀ᶠ h:ℕ in atTop,∀i,pay h i≤C*h)
    (pair : ∀ᶠ h:ℕ in atTop,∀i,(b h i+b h i)*2^(l h i)≤pay h i)
    (book : ∀ᶠ h:ℕ in atTop,∀i,Book.width (b h i) (2^(k h i)) (short h i)*M h i≤pay h i) :
    Bounded (fun h i=>aperture (H h i) (D h i) (u h i) (l h i) (b h i) (short h i) (M h i) (k h i)) := by
  obtain ⟨C,hw⟩:=payload
  have words:=Bounded.pow_of_linear (K:=C) hw
  have m : Bounded (fun h i=>u h i+l h i) :=axes.of_le fun _ _=>Nat.lt_two_pow_self.le
  have hi : Bounded (fun h i=>2^(u h i)) :=axes.of_le fun _ _=>Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have rows:=hosts.mul hi
  have page' : Bounded (fun h i=>page (H h i) (u h i)) := by
    simpa only [page,rowBits,←Nat.log2_eq_log_two] using (rows.add (Bounded.const 1)).logPage
  have small : Bounded (fun h i=>2^(smallKey (l h i) (b h i))) := by
    apply words.of_eventually_le
    exact pair.mono fun h q i=>Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right _ (Nat.le_add_right ..)).trans (q i))
  have inside : Bounded (fun h i=>2^((b h i+b h i)*2^(l h i))) :=
    words.of_eventually_le (pair.mono fun h q i=>Nat.pow_le_pow_right (by decide) (q i))
  have big : Bounded (fun h i=>2^(bigKey (l h i) (b h i))) := by
    simpa only [bigKey,Nat.pow_add,Nat.pow_one] using (Bounded.const 2).mul inside
  have pitch : Bounded (fun h i=>2^(Book.pitchBits (H h i) (u h i))) :=
    ((((Bounded.const 2).mul hosts).add (Bounded.const 1)).mul hi).of_le fun h i=>Book.pitch_upper _ _
  have gate : Bounded (fun h i=>2^(Book.width (b h i) (2^(k h i)) (short h i)*M h i)) :=
    words.of_eventually_le (book.mono fun h q i=>Nat.pow_le_pow_right (by decide) (q i))
  dsimp only [aperture,inputWords,span,DescentPackedRectangle.words,Book.gateWords,Book.indexWords]
  repeat' first | assumption | apply Bounded.add | apply Bounded.mul | apply Bounded.const

/-- Combine the source/earlier-register inventory with the true generated immutable canvas,
native chosen GL pass, retained selected rotation and repacking. All addresses use the same old floor. -/
theorem whole_repacked_rate {p : ∀h,ι h→Placement} (pay gain : ∀h,ι h→ℕ)
    (hbits : ∀h i,0<(p h i).geo.bits)
    (b : Placement.ScalarRoom p pay gain)
    (field groups re e : ∀h,ι h→ℕ)
    (groupsB : Bounded groups) (lanesB : Bounded (fun h i=>2^(e h i)))
    (dict : ∀ᶠ h:ℕ in atTop,∀i,re h i+field h i*(2^(re h i)*2^(e h i))≤pay h i/2)
    (start : ∀h,ι h→ℕ) (short M k : ∀h,ι h→ℕ)
    (pre : ∀h i,let g:=(p h i).geo;(p h i).endAddress-start h i≤
      aperture g.hosts g.ports g.high g.low g.bits (short h i) (M h i) (k h i))
    (radix : Bounded (fun h i=>2^(k h i))) (axes : Bounded (fun h i=>2^((p h i).geo.high+(p h i).geo.low)))
    (book : ∀ᶠ h:ℕ in atTop,∀i,let g:=(p h i).geo;Book.width g.bits (2^(k h i)) (short h i)*M h i≤pay h i) :
    Bounded (fun h i=>(p h i).repackedEnd (pay h i) (gain h i) (hbits h i)
      (field h i) (groups h i) (2^(re h i)) (2^(e h i))-start h i) := by
  have src:=aperture_rate (fun h i=>(p h i).geo.hosts) (fun h i=>(p h i).geo.ports)
    (fun h i=>(p h i).geo.high) (fun h i=>(p h i).geo.low) (fun h i=>(p h i).geo.bits)
    short M k pay b.hosts b.ports radix axes b.payload (b.routeBits.mono fun h q i=>(q i).trans (Nat.div_le_self ..)) book
  have prefixB : Bounded (fun h i=>(p h i).endAddress-start h i) :=src.of_le pre
  have body:=Placement.repacked_span_rate p pay gain hbits b field groups re e groupsB lanesB dict
  apply (prefixB.add body).of_le
  intro h i
  have : (p h i).middle≤(p h i).endAddress := by rw [(p h i).end_eq];exact Nat.le_add_right ..
  omega

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas.Setup

end OAI
