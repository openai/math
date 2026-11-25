import OAI.Computability.BorderVNP.PackedFrozenOperands
import OAI.Computability.BorderVNP.PackedSelectedScheduleRanges

/-! # Address and sorting widths of the immutable writer on selected geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Cover Cover.AddressCircuit Epoch Crossing Shortening Shortening.StaticRows Shortening.PublicDenseReceipt
open PackedHistoryCircuit PackedHistoryCircuit.Normalized.SelectedSchedule PublicCapacity TeamScales
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- Fixed address-width multiplier for interval, histogram, and site-local writer passes. -/
noncomputable def writerWidth :=
  140 + Nat.clog 2 (bins S) + 90*Fintype.card (Cube D)*66 + Nat.clog 2 (e.count+1)

/-- The immutable writer's lookup keys, cut and count pass widths, and actual
successor rectangle sorting width all fit the same fixed multiple of the public word. -/
theorem writer_ranges {r n start t : ℕ} {i : Fin S.rounds} {den cut : ℕ}
    (ready : Ranges S r n start t i den cut) (hn : 1≤n) (hr : 1≤r) :
    let lev := stageLevel S start t (i.val+1)
    let M := S.fanIn*(before S start t i).edges
    let A := seedCount S start t i
    let w := 60*logWidth r n
    let L := writerWidth S*logWidth r n
    let next := before S start t (i.val+1)
    1≤L ∧ w≤L ∧ Nat.clog 2 (A+M)+operandBits D (S.source.pattern i).bins.Bin lev+w+1 ≤ L ∧
      w+Nat.clog 2 (e.count+1)+1 ≤ L ∧ Nat.clog 2 (12*(next.sites+next.edges+1)) ≤ L := by
  intro lev M A w L next
  let l := logWidth r n
  have hl : 1≤l := by
    rw [show l=Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact (by decide : 1≤Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr]))
  let T := 2^w
  obtain ⟨_,_,_,_,rows,seeds,sites,edges,_,_,logs⟩ := ready.words
  change M ≤ T at rows
  change A ≤ T at seeds
  change next.sites ≤ T at sites
  change next.edges ≤ T at edges
  have sort : Nat.clog 2 (A+M) ≤ w+1 := Nat.clog_le_of_le_pow (by rw [pow_succ]; change A+M ≤ T*2; omega)
  have hT : 1 ≤ T := Nat.one_le_two_pow
  have high : Nat.clog 2 (12*(next.sites+next.edges+1)) ≤ w+6 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_add]
    change 12*(next.sites+next.edges+1) ≤ T*64
    omega
  let vol := CoverScale.sites (Cube D) lev
  change Nat.clog 2 (T+vol+2)+1 ≤ 63*l at logs
  have v := Nat.clog_mono_right 2 (show vol ≤ T+vol+2 by omega)
  have depth := PublicPopulation.depth_le_clog_tiles (Cube D) (lev+1)
  change lev+1 ≤ Nat.clog 2 vol+2 at depth
  have dl : lev+2 ≤ 66*l := by omega
  let B := Nat.clog 2 (bins S)
  let q := Fintype.card (Cube D)
  have bin : Nat.clog 2 (Fintype.card (S.source.pattern i).bins.Bin) ≤ B :=
    Nat.clog_mono_right 2 (Finset.le_sup (f := fun j => Fintype.card (S.source.pattern j).bins.Bin) (Finset.mem_univ i))
  have key : operandBits D (S.source.pattern i).bins.Bin lev ≤ (B+90*q*66)*l := by
    change Nat.clog 2 (Fintype.card (S.source.pattern i).bins.Bin)+q*(30*((lev+1)+1)*3) ≤ _
    nlinarith only [bin,Nat.le_mul_of_pos_right B hl,Nat.mul_le_mul_left (90*q) dl]
  have total : (140+B+90*q*66+Nat.clog 2 (e.count+1))*l = L := rfl
  have term := Nat.le_mul_of_pos_right (Nat.clog 2 (e.count+1)) hl
  have word : w=60*l := rfl
  rw [←total]
  constructor
  · nlinarith only [hl]
  constructor
  · nlinarith only [word]
  constructor
  · nlinarith only [sort,key,word,hl]
  constructor
  · nlinarith only [word,hl,term]
  · nlinarith only [high,word,hl]

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
