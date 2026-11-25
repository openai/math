import OAI.Hierarchy.ProtocolRAMPackedRanked
import OAI.Hierarchy.ProtocolRAMPackedBias

namespace OAI
/-! # Flat workspace of the translated group-counter and rank passes -/

namespace Hierarchy.ProtocolRAMPackedRanked
open ProtocolRAM

def fresh (start N bins : ℕ) : Layout :=
  let groupBase := start+2*N
  let cols := groupBase+2^(groupBits (3*N))
  let scratch := cols+N+2^(groupBits N)
  let rd := scratch+2*N
  let ks := rd+3*N
  let ct := ks+4*N
  let rs := ct+bins
  ⟨start,⟨groupBase,groupBits (3*N)⟩,cols,groupBits N,scratch,rd,ks,ct,rs,groupBits (4*N)⟩

def finish (start N bins : ℕ) := (fresh start N bins).rank.base+(fresh start N bins).rank.size

theorem finish_words (start N bins : ℕ) : finish start N bins ≤ start+28*N+bins+9 := by
  have g := bias_words (3*N)
  have c := bias_words N
  have r := bias_words (4*N)
  dsimp [finish,fresh,Layout.rank,Bank.size]
  omega

theorem fresh_fits (start N bins W : ℕ) (room : finish start N bins < 2^W) :
    (fresh start N bins).Fits W N bins := by
  have g := group_capacity (3*N)
  have c := group_capacity N
  have r := group_capacity (4*N)
  dsimp [finish,fresh,Layout.rank,Bank.size] at room
  constructor
  · exact le_rfl
  · exact g
  · exact ⟨Nat.two_pow_pos _,by dsimp [fresh,Bank.size];omega,le_rfl⟩
  · dsimp [fresh];omega
  · constructor
    · trivial
    · refine ⟨Nat.two_pow_pos _,?_,?_⟩ <;> dsimp [ProtocolRAMPackedCommon.inputBanks,fresh,Layout.weights,Bank.size] <;> omega
    · refine ⟨Nat.two_pow_pos _,?_,?_⟩ <;> dsimp [ProtocolRAMPackedCommon.inputBanks,fresh,Layout.keyBank,Bank.size] <;> omega
    · exact c
    · exact c
    · exact le_rfl
    · exact le_rfl
    · dsimp [fresh];omega
  · exact le_rfl
  · exact le_rfl
  · exact r
  · dsimp [fresh];omega
  · dsimp [fresh];omega

theorem canonical_words (start N groups menu : ℕ) :
    finish start N (2^groupBits groups*(menu+1)) ≤ start+28*N+2*(groups+1)*(menu+1)+9 :=
  (finish_words ..).trans (by
    have h := Nat.mul_le_mul_right (menu+1) (bias_words groups)
    omega)

end Hierarchy.ProtocolRAMPackedRanked

end OAI
