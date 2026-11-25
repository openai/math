import OAI.Hierarchy.DescentSeedTokenPrice
import OAI.Hierarchy.DescentResetStemProjectRate

namespace OAI
/-! # Uniform physical address and tariff bounds for the entire seed token deck -/
namespace Hierarchy.DescentSeedTokenTransposition
open Filter DescentDatedAddressBook DescentSIMDLookup
variable {ι : ℕ→Type*}
private theorem chunks_bounded {g m : ∀h,ι h→ℕ} (groups : Bounded g) (pitch : Bounded m) :
    Bounded (fun h i=>chunks (g h i) (m h i)) :=
  (groups.add pitch).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))

theorem rate {O H G X a A M : ∀h,ι h→ℕ}
    (old : Bounded O) (actors : Bounded H) (groups : Bounded G) (blocks : Bounded X)
    (oldPitch : Bounded A) (newPitch : Bounded M) (live : ∀h i,0<X h i)
    (inBits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,a h i*A h i≤K*h)
    (outBits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(a h i*X h i)*M h i≤K*h) :
    Bounded (fun h i=>endAddress 0 (O h i) (H h i) (G h i) (X h i) (a h i) (A h i) (M h i)) ∧
      Bounded (fun h i=>tariff (O h i) (H h i) (G h i) (X h i) (a h i) (A h i) (M h i)) :=by
  have one:=Bounded.const (ι:=ι) 1
  have point:=DescentResetStemProject.rates one old groups blocks oldPitch newPitch inBits outBits
  obtain ⟨u,low⟩:=inBits
  obtain ⟨v,high⟩:=outBits
  have src:=Bounded.pow_of_linear low
  have dst:=Bounded.pow_of_linear high
  have leaf : Bounded (fun h i=>2^(a h i*M h i)):=Bounded.pow_of_linear (high.mono (fun h fit i=>
    (Nat.mul_le_mul_right (M h i) (Nat.le_mul_of_pos_right (a h i) (live h i))).trans (fit i)))
  have orig:=chunks_bounded (groups.mul blocks) oldPitch
  have combined:=chunks_bounded (groups.mul blocks) (newPitch.mul blocks)
  have stripe:=chunks_bounded groups newPitch
  have runRows:=actors.mul stripe
  have lut:=leaf.add ((Bounded.const 4).mul runRows.padded)
  have pieces : Bounded (fun h i=>Overlap.pieces (G h i*X h i) (A h i) (M h i*X h i)) :=
    orig.of_le (fun _ _=>min_le_left _ _)
  have dictionary:=((pieces.add one).mul (oldPitch.add one)).mul src
  have book:=blocks.mul dst
  have vectors:=blocks.mul (old.mul stripe)
  have cost : Bounded (fun h i=>DescentResetStemProject.volume 1 (O h i) (G h i) (X h i) (a h i) (A h i) (M h i)) :=by
    simpa only [DescentResetStemProject.volume,DescentVectorBookReshape.dictionaryWords,
      DescentVectorBookReshape.rows,Overlap.rows,Nat.one_mul,Nat.mul_one] using
      (((((((one.add (old.mul orig)).add (old.mul combined)).add dictionary).add book).add vectors).add
        (old.mul stripe)).add one)
  constructor
  · exact ((point.add lut).add (blocks.mul runRows)).add runRows.padded
  · have writes:=((Bounded.const 4).add ((Bounded.const 10).mul lut)).add
      ((Bounded.const 4).add (blocks.mul ((Bounded.const 4).add ((Bounded.const 86).mul runRows))))
    have names:=((Bounded.const 15).mul (lut.add one)).add
      ((Bounded.const 15).add (blocks.mul (Bounded.const (11+4*41))))
    exact (((Bounded.const 4096).mul cost).add writes).add ((Bounded.const 7).mul names)

end Hierarchy.DescentSeedTokenTransposition

end OAI
