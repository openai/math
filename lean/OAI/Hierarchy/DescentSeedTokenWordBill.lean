import OAI.Hierarchy.DescentSeedTokenPrice
import OAI.Hierarchy.DescentSeedTokenAlphabet
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! # Word and bit bills for the ballot-dependent first primitive emitter -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSIMDLookup DescentDyadicSpan DescentSeedRoot

private theorem chunks_count (n m : ℕ) (nz : 0 < m) : chunks n m ≤ n+1 :=by
  change (n+m-1)/m ≤ n+1
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul nz).2
  nlinarith only [nz,Nat.sub_le (n+m) 1,Nat.le_mul_of_pos_right n nz]

theorem token_tariff_words (O H G r a A M : ℕ) (old : O ≤ H) (blocks : 0 < r) (_pitch : 0 < A) (_host : 0 < H)
    (overlap : (Overlap.pieces (G*r) A (M*r)+1)*(A+1)*2^(a*A) ≤ H)
    (project : r*2^((a*r)*M) ≤ H) (table : 2^(a*M) ≤ H) :
    DescentSeedTokenTransposition.tariff O H G r a A M ≤
      50000*(H+O*chunks (G*r) A+O*chunks (G*r) (M*r)+r*(H*chunks G M)+r+1) :=by
  let n:=H*chunks G M
  have small:=span_le n
  have core:=Nat.mul_le_mul_right (chunks G M) old
  have copies:=Nat.mul_le_mul_left r core
  have all : n ≤ r*n:=Nat.le_mul_of_pos_left _ blocks
  simp only [DescentSeedTokenTransposition.tariff,DescentResetStemProject.volume,
    DescentSeedTokenColumns.size,DescentVectorBookReshape.rows,DescentVectorBookReshape.dictionaryWords,
    Overlap.rows,Nat.one_mul,Nat.mul_one]
  change 4096*(1+_+_+_+_+_+_+1)+(4+10*(_+4*span n)+(4+r*(4+86*n)))+
    7*(15*((_+4*span n)+1)+(15+r*(11+4*41))) ≤ _
  dsimp only [n] at all small ⊢
  nlinarith only [small,core,copies,all,overlap,project,table,Nat.zero_le (r*(H*chunks G M)),
    Nat.zero_le (O*chunks (G*r) (M*r)),Nat.zero_le (O*chunks (G*r) A),_host]

theorem token_tariff_bits (O H G r a A M w oldShort newShort : ℕ)
    (old : O ≤ H) (blocks : 0 < r) (pitch : 0 < A) (host : 0 < H)
    (overlap : (Overlap.pieces (G*r) A (M*r)+1)*(A+1)*2^(a*A) ≤ H)
    (project : r*2^((a*r)*M) ≤ H) (table : 2^(a*M) ≤ H)
    (oldUse : w ≤ A*oldShort) (newUse : w ≤ M*newShort) :
    DescentSeedTokenTransposition.tariff O H G r a A M*w ≤
      50000*(H*w*(5+2*r)+H*(G*r)*(oldShort+2*newShort)) :=by
  have charged:=Nat.mul_le_mul_right w (token_tariff_words O H G r a A M old blocks pitch host overlap project table)
  have increase : w ≤ (M*r)*newShort :=
    newUse.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ blocks))
  have packed (s z : ℕ) (fits : w ≤ z*s) :
      O*chunks (G*r) z*w ≤ H*w+H*(G*r)*s :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ old)).trans (chunk_work H (G*r) z w s fits)
  have one:=packed oldShort A oldUse
  have two:=packed newShort (M*r) increase
  have page:=Nat.mul_le_mul_left r (chunk_work H G M w newShort newUse)
  have shared:=Nat.mul_le_mul_right w host
  have repeated:=Nat.mul_le_mul_left r shared
  calc
    _ ≤ _:=charged
    _ ≤ _:=by
      rw [Nat.mul_assoc 50000]
      apply Nat.mul_le_mul_left
      nlinarith only [one,two,page,shared,repeated,Nat.zero_le (H*w),Nat.zero_le (H*w*r)]

theorem shared_token_tables :
    ∀ᶠ h : ℕ in Filter.atTop,∀s H G r M : ℕ,
      2^h ≤ H → 0 < DescentPackedSeed.Primitive.pieces h s → r ≤ h → M*r ≤ h →
      (DescentPackedSeed.Primitive.roleBits s*r)*M ≤ h/2 →
      let a:=DescentPackedSeed.Primitive.roleBits s
      let A:=DescentPackedSeed.Primitive.pieces h s
      (Overlap.pieces (G*r) A (M*r)+1)*(A+1)*2^(a*A) ≤ H ∧
        r*2^((a*r)*M) ≤ H ∧ 2^(a*M) ≤ H ∨ r=0 :=by
  filter_upwards [small_role_tables 1 2] with h bounds
  intro s H G r M ambient live rcap bundle small
  dsimp only
  let A:=DescentPackedSeed.Primitive.pieces h s
  let a:=DescentPackedSeed.Primitive.roleBits s
  by_cases zero : r=0
  · exact Or.inr zero
  left
  have op : Overlap.pieces (G*r) A (M*r)+1 ≤ h+3 :=
    (Nat.succ_le_succ (Nat.min_le_right ..)).trans (by have:=chunks_count (M*r) A live;omega)
  have ac : A ≤ h:=Nat.div_le_self ..
  have ap : A+1 ≤ h+3:=by omega
  have cash:=bounds (a*A) (source_token_exponent h s)
  have lookup:=(Nat.mul_le_mul op ap)
  have upper : (h+3)*(h+3)=1*(h+3)^2:=by ring
  have bigger : r ≤ 1*(h+3)^2:=by nlinarith only [rcap,Nat.zero_le (h*h),Nat.zero_le h]
  change (a*r)*M ≤ h/2 at small
  have proj:=bounds ((a*r)*M) (by omega)
  have inc:=Nat.mul_le_mul_right M (Nat.le_mul_of_pos_right a (by omega : 0 < r))
  exact ⟨((Nat.mul_le_mul_right _ (lookup.trans_eq upper)).trans cash).trans ambient,
    ((Nat.mul_le_mul_right _ bigger).trans proj).trans ambient,
    (Nat.pow_le_pow_right (by decide) (inc.trans (small.trans (Nat.div_le_self ..)))).trans ambient⟩

end Hierarchy.DescentDatedSeedStartup

end OAI
