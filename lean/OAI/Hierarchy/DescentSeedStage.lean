import OAI.Hierarchy.DescentMeasuredHistory
import OAI.Hierarchy.DescentSeedWorld
import OAI.Hierarchy.DescentCommonGroups

namespace OAI
/-! # The actual first subround input for independent copies of the user's network -/

namespace Hierarchy.DescentInitialHost
open DescentSixParty DescentHostDirectory DescentColonies StarKeys Computability.BorderVNP.Crossing Catalyst
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
variable (G : PoweredGadget F) {J : Type} [Fintype J] [DecidableEq J]
variable {R s r : ℕ} (digits : Fin R≃J×Block r) (c : (initialGroup X R s).Choice)
local notation "N" => X.network.copyGraph

def seedStage {ε : ℝ} (q : ℝ) (w hist z : ℕ) (field : 0<r) (hq : 0<q)
    (hw : 0<w) (hz : 0<z) (units : s=z*G.b)
    (room : 3*(w*s)+hist≤256*(w*s))
    (retained : (q*hist)*((R*Fintype.card (N).Site:ℕ):ℝ)≤ε)
    (root : ((Fintype.card J*Fintype.card (Site N):ℕ):ℝ)*
      ((2:ℝ)^(DescentHostDegree.packExponent 20 3)*(q*((w*s*256:ℕ):ℝ)))≤ε) :
    StageInput ((initialGroup X R s).state c) G (q*w) ε where
  V := J×Site N
  finite := inferInstance
  decideV := inferInstance
  Atoms := Σv : (N).Site,Count (markedInput X).graph s (.inl v)
  k := r
  pos := seedPos X c digits
  block := seedBlock X c digits
  hub := seedHub X c
  records := seedRecords X c
  wire := w
  hist := hist
  z := z
  cap := 256
  Δ := 3
  near := groupedNear (near N)
  fieldBits := field
  degreeMin := by decide
  degree := fun v=>(grouped_degree (near N) v).le.trans ((«initialize» X).1 v.2)
  wirePos := hw
  unitPos := hz
  capPos := by decide
  small v i := by simpa only [←units,Nat.mul_comm 256] using seed_small X c digits w hist room v i
  adjacent := by
    rintro ⟨i,e⟩ _
    exact Finset.mem_map.mpr ⟨_,(wire_near N e).1,rfl⟩
  reverse := by
    rintro ⟨i,e⟩ _
    exact Finset.mem_map.mpr ⟨_,(wire_near N e).2,rfl⟩
  internal := by rintro ⟨i,e⟩ _;rfl
  widths := by
    rintro ⟨i,e⟩ _
    change s*(hubbed N).width e=z*G.b
    exact ((congrArg (s * ·) (hub_unit N (CorrectionBatch.physical_output X).1 e)).trans
      (Nat.mul_one s)).trans units
  inside := by
    rintro ⟨i,e⟩ he
    cases e with
    | inl e=>exact ⟨rfl,rfl⟩
    | inr port =>
      change (⟨i,Sum.inr port⟩ : Σ _ : Fin R,Wire N)∈Finset.univ.sigma
        (fun _=> Finset.univ.map (Function.Embedding.inl : (N).Edge ↪ Wire N)) at he
      obtain ⟨_,_,bad⟩:=Finset.mem_map.mp (Finset.mem_sigma.mp he).2
      cases bad
  outside := by
    rintro ⟨i,e⟩ he
    cases e with
    | inl e =>
      apply False.elim (he ?_)
      change (⟨i,Sum.inl e⟩ : Σ _ : Fin R,Wire N)∈Finset.univ.sigma
        (fun _=> Finset.univ.map (Function.Embedding.inl : (N).Edge ↪ Wire N))
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _,Finset.mem_map.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩
    | inr port =>
      change false ≠ true
      decide
  q := q
  qpos := hq
  unitPrice := rfl
  retained := by exact_mod_cast (by simpa only [←Nat.cast_sum,seed_record_total] using retained :
    q*hist*(∑v,((seedRecords X c v).length:ℝ))≤ε)
  roots := by simpa only [Fintype.card_prod,←units] using root

end
end Hierarchy.DescentInitialHost

end OAI
