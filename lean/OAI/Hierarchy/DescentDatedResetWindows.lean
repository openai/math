import OAI.Hierarchy.DescentDatedResetRate
import OAI.Hierarchy.DescentResetRootAllocator

namespace OAI
/-! # Actual selected matrix, packed slice and every private root window of a reset -/
namespace Hierarchy
open DescentFallbackShapeTable DescentSixParty.Chronology DescentSharedBookScan DescentSIMDLookup
open DescentDatedAddressBook Filter
noncomputable section
namespace DescentSixParty.PackedFlow.Canvas.Placement
variable {ι : ℕ→Type*} (p : ∀h,ι h→Placement) (pay gain : ∀h,ι h→ℕ)
variable (positive : ∀h i,0<(p h i).geo.bits)

/-- Fee support for the two actually loaded chosen-matrix pages and all repack scans.
The signed control and selected scalar stay strictly before the new source directory. -/
theorem repacked_span_rate (b : ScalarRoom p pay gain)
    (field groups re e : ∀h,ι h→ℕ)
    (bg : Bounded groups) (lanes : Bounded (fun h i=>2^(e h i)))
    (dictionary : ∀ᶠ h:ℕ in atTop,∀i,re h i+field h i*(2^(re h i)*2^(e h i))≤pay h i/2) :
    Bounded (fun h i=>(p h i).repackedEnd (pay h i) (gain h i) (positive h i)
      (field h i) (groups h i) (2^(re h i)) (2^(e h i))-(p h i).middle) := by
  let d:=fun h i=>(p h i).geo.high+(p h i).geo.low
  obtain ⟨C,hw⟩:=b.payload
  have sheets:=Bounded.pow_of_linear (K:=C) hw
  have actual : Bounded (fun h i=>(2^(d h i))^(d h i)) := by
    apply sheets.of_eventually_le
    filter_upwards [b.square] with h square
    intro i
    rw [←Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) ((square i).trans (Nat.div_le_self ..))
  have axes : Bounded d := by
    apply sheets.of_eventually_le
    filter_upwards [b.square] with h square
    intro i
    have : d h i≤d h i*d h i := Nat.le_mul_self ..
    exact (this.trans ((square i).trans (Nat.div_le_self ..))).trans Nat.lt_two_pow_self.le
  have hosts : Bounded (fun h i=>(p h i).routedHosts) :=
    ((Bounded.const 1 |>.add b.ports).add axes).mul b.hosts
  have batches : Bounded (fun h i=>chunks (groups h i) (2^(e h i))) :=
    (bg.add lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have live:=hosts.mul batches
  have tab : Bounded (fun h i=>2^(re h i)*Subwords.stride (field h i) (2^(re h i)) (2^(e h i))) :=
    sheets.of_eventually_le (dictionary.mono fun h ok i=>
      (Subwords.dictionary_budget (field h i) (pay h i) (re h i) (e h i) (ok i)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.div_le_self ..)))
  have rem:=remix_span_rate p pay gain positive b
  have span:=(((rem.add actual).add actual).add (Bounded.const 1)).add
    ((Bounded.const 4).mul (((Bounded.const 1).add live).add tab))
  apply (span.add live).of_le
  intro h i
  dsimp only [d,repackedEnd,rotationEnd,Subwords.finish,Subwords.destination]
  omega

end DescentSixParty.PackedFlow.Canvas.Placement
namespace DescentSixParty.Chronology.RootTemplates

def privateEnd (start H G M r n D : ℕ) :=
  (arena start H G M r n D).first (Fintype.card (RootPage r (2^n)))

theorem privateEnd_add (start shift H G M r n D : ℕ) :
    privateEnd (shift+start) H G M r n D=shift+privateEnd start H G M r n D := by
  simp only [privateEnd,RootArena.first,RootArena.stride,Nat.add_assoc]

theorem private_span_rate {ι : ℕ→Type*} (H G M r n D : ∀h,ι h→ℕ)
    (bh : Bounded H) (bg : Bounded G) (bm : Bounded M)
    (br : Bounded (fun h i=>2^(r h i))) (bins : Bounded (fun h i=>2^(n h i))) (bd : Bounded D) :
    Bounded (fun h i=>privateEnd 0 (H h i) (G h i) (M h i) (r h i) (n h i) (D h i)) := by
  have r' : Bounded r :=br.of_le fun _ _=>Nat.lt_two_pow_self.le
  have cr : Bounded (fun h i=>(DescentHostDirectory.codes (r h i)).card) := by
    apply (br.mul (Bounded.const 2)).of_le
    intro h i
    have fact:=DescentHostDirectory.codes_card (r h i)
    rw [Nat.pow_succ] at fact
    omega
  have batches : Bounded (fun h i=>chunks (G h i) (M h i)) :=
    (bg.add bm).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=((r'.add (Bounded.const 1)).mul br).mul (bins.add (Bounded.const 1))
  have widths:=rows.mul ((bd.add (Bounded.const 1)).mul rows)
  have count_:= (Bounded.const 2).mul ((cr.mul ((Bounded.const 2).add bins)).add
    (cr.mul (bins.add (Bounded.const 1))))
  have all:=((bh.mul widths).padded.add ((Bounded.const 2).mul (bh.mul batches).padded)).mul count_
  simpa only [privateEnd,arena,RootArena.first,RootArena.stride,RootArena.span,Nat.zero_add,page_count,
    DescentSharedBookScan.width,DescentFallbackShapeTable.rows] using all

end DescentSixParty.Chronology.RootTemplates
end
end Hierarchy

end OAI
