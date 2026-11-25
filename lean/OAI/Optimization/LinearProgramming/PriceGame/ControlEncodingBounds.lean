import OAI.Optimization.LinearProgramming.PriceGame.ControlWire
import OAI.Optimization.LinearProgramming.PriceGame.LearningBits
import OAI.Optimization.LinearProgramming.PriceGame.LearningPool
import OAI.Optimization.LinearProgramming.RAM.Basic

/-! Bounds for the actual bit-stack codes of the numeric records of a suspended trial.
Product and list bounds include the bytes used to delimit each item. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)
open States.Mass Learning

/-- Binary framing quotes the left component of a pair. -/
def pairBound (left right : ℕ) : ℕ := 2*left + right + 1

/-- One element marker and a quoted payload per element, plus the list terminator. -/
def listBound (count width : ℕ) : ℕ := count*(2*width+2)+1

theorem prod_le {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (a : A) (b : B)
    {x y : ℕ} (ha : (ea a).length ≤ x) (hb : (eb b).length ≤ y) :
    (prodCode ea eb (a,b)).length ≤ pairBound x y := by
  simp only [prodCode,pairBits_length,pairBound]
  omega

theorem list_le {A : Type} (enc : A → List Bool) (xs : List A) {count width : ℕ}
    (hc : xs.length ≤ count) (hw : ∀ x ∈ xs, (enc x).length ≤ width) :
    (listCode enc xs).length ≤ listBound count width := by
  have aux (ys : List A) (h : ∀ x ∈ ys, (enc x).length ≤ width) :
      (listCode enc ys).length ≤ ys.length*(2*width+2)+1 := by
    induction ys with
    | nil => simp [listCode]
    | cons y ys ih =>
      rw [listCode_length_cons,List.length_cons,Nat.add_mul ys.length 1 (2*width+2),Nat.one_mul]
      have h₁ := h y (by simp)
      have h₂ := ih (fun z hz => h z (by simp [hz]))
      omega
  exact (aux xs hw).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hc) 1)

theorem nat_le_self (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr n.lt_two_pow_self

theorem rat_length (q : ℚ) :
    (ratCode q).length = 7 + 2 * q.num.natAbs.size + q.den.size := by
  simp only [ratCode,intCode,intData,prodCode,pairBits_length,boolCode,List.length_cons,
    List.length_nil,Nat.size_eq_bits_len]
  omega

theorem rat_le_machine (q : ℚ) : (ratCode q).length ≤ 2*RAM.ratBits q+4 := by
  rw [rat_length,RAM.ratBits]
  have hn : q.num.natAbs.size ≤ q.num.natAbs.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  have hd : q.den.size ≤ q.den.log2 + 1 := Nat.size_le.mpr Nat.lt_log2_self
  omega

def rowBound (vertices width : ℕ) : ℕ := listBound vertices width

def historyBound (depth vertices width : ℕ) : ℕ := listBound depth (rowBound vertices width)

def probeBound (depth vertices width : ℕ) : ℕ :=
  pairBound depth (pairBound (rowBound vertices width) (historyBound depth vertices width))

def expertBound (depth vertices coordinates rawWidth : ℕ) : ℕ :=
  pairBound depth (pairBound 1 (pairBound (listBound 64 vertices)
    (pairBound (1 + pairBound depth vertices) (rowBound coordinates rawWidth))))

def roundBound (vertices experts scoreWidth probes probeWidth priceWidth : ℕ) : ℕ :=
  pairBound (rowBound vertices priceWidth)
    (pairBound (listBound experts scoreWidth) (listBound probes probeWidth))

def populationBound (experts expertWidth weightWidth : ℕ) : ℕ :=
  pairBound (listBound experts expertWidth) (listBound experts weightWidth)

theorem packTable_le {N l W V : ℕ} (f : Vertex N l → ℚ) (hV : N*2^l ≤ V)
    (hw : ∀ i, (ratCode (f i)).length ≤ W) :
    (listCode ratCode (packTable N l f)).length ≤ rowBound V W := by
  apply list_le
  · simpa using hV
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hw _

theorem packHistory_le {N l D V W : ℕ} (h : History N) (hl : l ≤ D)
    (hV : ∀ j < l, N*2^j ≤ V) (hW : ∀ j < l, ∀ i, (ratCode (h j i)).length ≤ W) :
    (listCode (listCode ratCode) (packHistory l h)).length ≤ historyBound D V W := by
  apply list_le
  · simpa [packHistory] using hl
  · intro xs hxs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hxs
    exact packTable_le _ (hV i i.isLt) (hW i i.isLt)

theorem packProbe_le {N D V W : ℕ} (p : Probe N) (hl : p.level ≤ D)
    (hV : ∀ j ≤ p.level, N*2^j ≤ V)
    (hw : ∀ i, (ratCode (p.prices i)).length ≤ W)
    (hh : ∀ j < p.level, ∀ i, (ratCode (p.history j i)).length ≤ W) :
    (packedProbeCode (packProbe p)).length ≤ probeBound D V W := by
  exact prod_le _ _ _ _ ((nat_le_self _).trans hl) (prod_le _ _ _ _
    (packTable_le _ (hV _ le_rfl) hw) (packHistory_le _ hl (fun j hj => hV j hj.le) hh))

theorem packExpert_le {N D V W : ℕ} (e : Expert N) (hl : e.skeleton.level ≤ D)
    (hV : ∀ j ≤ e.skeleton.level, N*2^j ≤ V) (hw : ∀ i, (ratCode (e.raw i)).length ≤ W) :
    (packedExpertCode (packExpert e)).length ≤ expertBound D V N W := by
  let s := e.skeleton
  have haddr {j : ℕ} (hj : j ≤ s.level) (i : Vertex N j) :
      ((vertexEquivFin N j i).val).bits.length ≤ V :=
    (nat_le_self _).trans ((vertexEquivFin N j i).isLt.le.trans (hV j hj))
  have ht : (listCode Nat.bits (packExpert e).tuple).length ≤ listBound 64 V := by
    apply list_le
    · simp [packExpert]
    · intro i hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      exact haddr le_rfl _
  have hpi : (pivotCode (packExpert e).pivot).length ≤ 1 + pairBound D V := by
    change (pivotCode (s.pivot.map _)).length ≤ _
    cases hn : s.pivot with
    | none => simp [pivotCode, Learning.BitMachine.optionCode]
    | some p =>
      simp only [Option.map_some, pivotCode, Learning.BitMachine.optionCode, List.length_cons]
      have hb := prod_le Nat.bits Nat.bits p.1.val (vertexEquivFin N p.1 p.2).val
        ((nat_le_self _).trans (p.1.isLt.le.trans hl)) (haddr p.1.isLt.le _)
      omega
  have hraw : (listCode ratCode (packExpert e).raw).length ≤ rowBound N W := by
    apply list_le
    · simp [packExpert]
    · intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact hw i
  exact prod_le _ _ _ _ ((nat_le_self _).trans hl) (prod_le _ _ _ _ le_rfl
    (prod_le _ _ _ _ ht (prod_le _ _ _ _ hpi hraw)))

/-- For every expert actually generated in a batch, the rational bit bound comes
from its difference-constraint representative; no encoded width is assumed. -/
theorem batch_raw_width {N R : ℕ} {ps : List (Probe N)} {e : Expert N}
    (he : e ∈ Pool.batch N R ps) (i : Fin N) :
    (ratCode (e.raw i)).length ≤ 28 + 2*(R+1).size := by
  obtain ⟨s,_,hs⟩ := List.mem_flatMap.mp he
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hs
  by_cases hi : i ∈ s.sources
  · change (ratCode (Compact.unpack s v i)).length ≤ _
    rw [Compact.unpack_index s v hi, rat_length]
    obtain ⟨hd,hn⟩ := Bits.generated_bit_lengths hv (Compact.index s i)
    have hc : (s.sources.card+1).size ≤ 7 := Nat.size_le.mpr (by have := s.card_sources_le; omega)
    omega
  · change (ratCode (Compact.unpack s v i)).length ≤ _
    simp only [Compact.unpack,hi,ite_false]
    rw [rat_length]
    change 10 ≤ 28 + 2*(R+1).size
    omega

/-- Real generated experts use only 64 vertex addresses and N encoded raw values. -/
theorem batch_expert_length {N R : ℕ} (hN : 0 < N) {ps : List (Probe N)} {e : Expert N}
    (he : e ∈ Pool.batch N R ps) :
    (packedExpertCode (packExpert e)).length ≤
      expertBound (depth N) (2*N^2) N (28 + 2*(R+1).size) := by
  apply packExpert_le e e.skeleton.1.isLt.le _ (batch_raw_width he)
  intro j hj
  simpa [card_vertices,Nat.mul_comm] using card_vertices_le N j hN (hj.trans e.skeleton.1.isLt.le)

theorem packRound_le {N ne V W S H Z : ℕ} (r : RoundResult N) (hN : N ≤ V)
    (hw : ∀ i, (ratCode (r.prices i)).length ≤ W)
    (hs : ∀ i : Fin ne, ((r.scores i.val).bits).length ≤ S)
    (hh : r.observations.length ≤ H) (hp : ∀ p ∈ r.observations, (packedProbeCode (packProbe p)).length ≤ Z) :
    (packedRoundCode (packRound ne r)).length ≤ roundBound V ne S H Z W := by
  apply prod_le
  · apply list_le
    · simpa [packRound] using hN
    · intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact hw i
  · apply prod_le
    · apply list_le
      · simp [packRound]
      · intro x hx
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
        exact hs i
    · apply list_le
      · simpa [packRound] using hh
      · intro p h
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
        exact hp q hq

theorem packPopulation_le {N M E W : ℕ} (p : Population N) (hc : p.experts.length ≤ M)
    (he : ∀ e ∈ p.experts, (packedExpertCode (packExpert e)).length ≤ E)
    (hw : ∀ q ∈ p.weights.toList, (ratCode q).length ≤ W) :
    (packedPopulationCode (packPopulation p)).length ≤ populationBound M E W := by
  apply prod_le
  · apply list_le
    · simpa [packPopulation] using hc
    · intro e h
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
      exact he q hq
  · apply list_le
    · simpa [packPopulation] using hc
    · exact hw

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
