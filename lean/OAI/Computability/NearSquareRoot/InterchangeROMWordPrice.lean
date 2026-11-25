import OAI.Computability.NearSquareRoot.InterchangeROMWordLedger

/-! # A computable coefficient for the whole address word

Each instruction has a frozen numerical weight. The header maintenance
performed by the sequence contributes one additional fixed cost per opcode.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMSequence

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  NearSquareRoot.InterchangeBatch NearSquareRoot.InterchangeSpace

/-- A numerical cost computed from the word, outside of the runtime geometry. -/
def weight (sum length : ℕ) := sum+110*(length+1)+2

theorem primrec_weight : Primrec₂ weight :=
  (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.const 110) (Primrec.succ.comp Primrec.snd))) (Primrec.const 2)).to₂

theorem Step.mono {Q : Type} {job : Job Q} {cmd : Cmd} {h x y : Tree} {children : List Q}
    {t s d T S D : ℕ} (run : Step job cmd h x y children t s d)
    (ht : t ≤ T) (hs : s ≤ S) (hd : d ≤ D) : Step job cmd h x y children T S D := by
  intro parent env clock data ret ih r b hb
  exact (run parent env clock data ret ih r b hb).mono (by omega) (by omega) (by omega)

private theorem total_le {U : Type} (ms : List U) (c coeff : U → ℕ) (G : ℕ)
    (hc : ∀ z∈ms, c z≤coeff z*G) : (ms.map c).sum ≤ (ms.map coeff).sum*G := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons,List.sum_cons,Nat.add_mul]
    exact Nat.add_le_add (hc m List.mem_cons_self) (ih (fun z hz => hc z (List.mem_cons_of_mem _ hz)))

private theorem peak_le {U : Type} (ms : List U) (c coeff : U → ℕ) (G : ℕ)
    (hc : ∀ z∈ms, c z≤coeff z*G) : childPeak c ms ≤ (ms.map coeff).sum*G := by
  apply childPeak_le
  intro z hz
  exact (hc z hz).trans (Nat.mul_le_mul_right G (List.single_le_sum
    (fun n _ => Nat.zero_le n) (coeff z) (List.mem_map_of_mem (f:=coeff) hz)))

/-- Time, data space, and return depth have a common computable coefficient
under any geometry which covers the physical row and header. -/
theorem scaled {Q U : Type} (job : Job Q) (cmd : Cmd) (header x y : Tree) (children : List Q)
    (ms : List U) (time space depth coeff : U → ℕ) (V G : ℕ)
    (hs : V≤G) (hh : header.count+1≤G)
    (ht : ∀ z∈ms, time z≤coeff z*G) (hsp : ∀ z∈ms, space z≤coeff z*G)
    (hd : ∀ z∈ms, depth z≤coeff z*G)
    (run : Step job cmd header x y children
      ((ms.map time).sum +(ms.length+1)*(110*(header.count+1)))
      (dataSpace V header.count (childPeak space ms))
      (returnSpace header.count (childPeak depth ms))) :
    let F := weight (ms.map coeff).sum ms.length * G
    Step job cmd header x y children F F F := by
  dsimp only
  have t := total_le ms time coeff G ht
  have s := peak_le ms space coeff G hsp
  have d := peak_le ms depth coeff G hd
  have u := Nat.mul_le_mul_left (ms.length+1) (Nat.mul_le_mul_left 110 hh)
  have localCap : 110*G ≤ 110*(ms.length+1)*G :=
    Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have admin : (ms.length+1)*(110*G)=110*(ms.length+1)*G := by ring
  rw [admin] at u
  unfold weight
  simp only [Nat.add_mul]
  apply Step.mono run
  · omega
  · unfold dataSpace
    apply max_le
    · omega
    · omega
  · unfold returnSpace
    apply max_le
    · omega
    · omega

end InterchangeROMSequence

end NearSquareRoot
end Computability
end OAI
