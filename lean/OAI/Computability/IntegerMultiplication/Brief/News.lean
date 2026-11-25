import OAI.Computability.IntegerMultiplication.Brief.Plan
import OAI.Computability.IntegerMultiplication.Grid.Stage
import OAI.Computability.IntegerMultiplication.Param.Payout

namespace OAI
namespace Computability
namespace IntegerMultiplication

/- packet standards and pricing -/
namespace Brief
open Code Carry Bits Staff Param Strip Loom Filter

/- Header size measured in budget. Always the binary input length; all
other data in directory generated on the tapes. -/
variable {I:Type} (n:I→ℕ)
def messenger i:=send (born (n i))
private theorem post :
    Dom (budget ∘ n) (fun i=>(messenger n i).count) := by
  refine ⟨1,4,fun i=>?_⟩
  have e:= Carry.depth (n i)
  have Q:= four_beta (n i)
  unfold beta at Q
  change size _ ≤ _
  rw [size_word,pow_one,Function.comp_apply]
  omega
def journals : Regime I := {
  scale:=budget ∘ n
  header:=messenger n
  gauge:=post n }
theorem guide_journals : Guide (journals n) n :=
  ⟨born ∘ n,Regime.self,fun _i=>birthValue _⟩

-- Resize to memory scale for table assembly
variable {n}
def extend (r:Regime I) (g:I→ℕ) (v:Dom g r.scale) : Regime I :=
  ⟨g,r.header,r.gauge.sub v⟩
theorem increase {r:Regime I} {g:I→ℕ} (v:Dom g r.scale) {f:I→Tree}
    (h:r.Small f) : (extend r g v).Small f :=
  Code.Task.BT.mono h v

-- eventually can be turned into uniform monomial bound
section eventual
theorem constant (f d : ℕ→ℕ) (h:Large fun n=> f n ≤ d n)
    (z:∀ n,1≤d n) :
    ∃ C:ℕ, ∀ n,f n ≤ C*d n := by
  obtain ⟨k,e⟩ := Filter.eventually_atTop.mp h
  refine ⟨(∑ n∈Finset.range k,f n)+1,fun n=>?_⟩
  rcases lt_or_ge n k with g|g
  · have t:= Finset.single_le_sum (f:=f) (s:=Finset.range k) (fun i _=>Nat.zero_le (f i)) (Finset.mem_range.mpr g)
    exact le_trans t (le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (z _)))
  exact le_trans (e n g) (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _))

-- Real budget inequalities given Large
theorem realConstant (f d : ℕ→ℝ) (h:Large fun n=> f n ≤ d n)
    (z:∀ n,1≤d n) :
    ∃ C:ℕ,∀ n, f n ≤ C*d n := by
  obtain ⟨k,e⟩ := Filter.eventually_atTop.mp h
  let C:= (∑ i∈Finset.range k,|f i|)+1
  obtain ⟨D,E⟩:= exists_nat_gt C
  refine ⟨D,fun n=>?_⟩
  have p:0 ≤ ∑ i∈Finset.range k,|f i| := Finset.sum_nonneg (fun i _=>abs_nonneg _)
  have u:1≤(D:ℝ) := by dsimp [C] at E; linarith
  rcases lt_or_ge n k with g|g
  · have t:=Finset.single_le_sum (f:=fun i=>|f i|) (s:=Finset.range k)
      (fun i _=> abs_nonneg _) (Finset.mem_range.mpr g)
    have t0 := le_abs_self (f n)
    have t1 : (D:ℝ)≤ D*(d n) := le_mul_of_one_le_right (Nat.cast_nonneg _) (z _)
    dsimp [C] at E; linarith
  exact le_trans (e _ g) (le_mul_of_one_le_left (by linarith [z n]) u)
end eventual

section Regime
variable (n)
private theorem scaleL : Dom (wall ∘ n) (journals n).scale := by
  obtain ⟨C,e⟩ := constant budget wall (Param.room_hold 1 |>.mono
    (fun i (h:budget i^1 ≤room i)=> le_trans (by simpa using h) (room_le i)))
    (fun i=> Nat.pow_pos (by decide))
  refine ⟨1,C,fun i=> le_trans (e (n i)) ?_⟩
  simp [Function.comp_apply]; gcongr; omega
def city : Regime I :=
  extend (journals n) (wall ∘ n) (scaleL n)
theorem cityRoof {f:I→Tree} (v:(journals n).Small f) :
    (city n).Small f := increase (scaleL n) v

theorem guide_city : Guide (city n) n :=
  ⟨born ∘ n,Regime.self,fun _i=>birthValue _⟩

theorem wealthy :
    Regime.ripe (r:=city n) (fun i=>(load (n i):ℝ)) := by
  refine ⟨(fun i=> by change (1:ℝ)≤(load (n i):ℝ); exact_mod_cast (Nat.pow_pos (by decide : 0<(2:ℕ)) : 1≤ load (n i))),fun k=>?_⟩
  obtain ⟨C,v⟩:= constant (fun i=>(wall i+1)^k) load ((loads 1 k).mono (by simp)) (fun _=>Nat.pow_pos (by decide))
  exact ⟨C,fun i=> by change (((wall (n i)+1)^k:ℕ):ℝ)≤ (C:ℝ)* (load (n i):ℝ); exact_mod_cast v (n i)⟩

theorem columnRoof :
    Regime.ripe (r:=journals n) (fun i=>(room (n i):ℝ)) := by
  refine ⟨(fun i=> by change (1:ℝ)≤(room (n i):ℝ); exact_mod_cast (Nat.pow_pos (by decide : 0<(2:ℕ)) : 1≤ room (n i))),fun k=>?_⟩
  obtain ⟨C,v⟩:= constant (fun i=>(budget i+1)^k) room ((rooms 1 k).mono (by simp)) (fun _=>Nat.pow_pos (by decide))
  exact ⟨C,fun i=> by change (((budget (n i)+1)^k:ℕ):ℝ)≤ (C:ℝ)* (room (n i):ℝ); exact_mod_cast v (n i)⟩
-- Often require RIP station where budget overhead measured per fat-record, multiply powers by width to absorb.
end Regime

-- elementwise axis list issuance
theorem sector {r:Regime I} (n:I→ℕ) (g:Guide r n) (w:I→ℕ) (W:Realizes r w) :
    let L (x:I) := List.ofFn fun j:Param.Direction (n x)=> Bits.short (w x)
      (Param.moduli (n x) j.val)
    r.Has L := by
  let d:= lanes ∘ n
  let D:=g.spread n
  apply harvest d D
  let I':=Across d
  let p:= Sigma.fst (β:=fun i=>Fin (d i))
  exact ((g.abroad n D).size_ (n ∘ p) (floor_ d D)).write (landing d D w W)

-- Of just simultaneous scouts
theorem camera {r:Regime I} (n:I→ℕ) (g:Guide r n) :
    let L (x:I) := List.ofFn fun j:Fin (scouts (n x))=> Bits.short (span_ (n x))
      (Param.moduli (n x) j.val)
    r.Has L := by
  let f := scouts ∘ n
  let F:=g.positions n
  apply harvest f F
  let p:= Sigma.fst (β:=fun i=>Fin (f i))
  exact ((g.abroad n F).size_ (n ∘ p) (floor_ f F)).write (landing f F _ (g.tensorSize n))
end Brief

end IntegerMultiplication
end Computability
end OAI
