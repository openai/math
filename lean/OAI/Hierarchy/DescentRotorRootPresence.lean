import OAI.Hierarchy.DescentMixedPrivateRoots
import OAI.Hierarchy.DescentPackedVenueOrdinals
import OAI.Hierarchy.DescentCoarseCoordinates

namespace OAI
/-! # Presence of a good-base ticket from its true selected depth and one old stencil bit -/
namespace Hierarchy.DescentRotorRootPresence
open DescentSixParty DescentIssuedFallbackPanel DescentColonies DescentGL DescentResetHostSize
open DescentHostDirectory DescentChosenRouter DescentCanonicalPorts
open scoped Classical
noncomputable section

def sample {r : ℕ} (t : Code r) : Block r :=
  ⟨t.val.2*2^(r-t.val.1),by
    have ok:=codes_valid t.property
    calc _<2^t.val.1*2^(r-t.val.1):=Nat.mul_lt_mul_of_pos_right ok.2 (Nat.two_pow_pos _)
         _=2^r:=by rw [←pow_add,Nat.add_sub_of_le ok.1]⟩

def number {c r : ℕ} (hi : Block c) (t : Code r) := hi.val*2^t.val.1+t.val.2

theorem sample_group {k c : ℕ} (small : c≤k) (hi : Block c) (t : Code (k-c)) :
    group (c+t.val.1) (join small hi (sample t))=number hi t := by
  have ok:=codes_valid t.property
  have power : 2^(k-c)=2^t.val.1*2^(k-c-t.val.1):=by rw [←pow_add,Nat.add_sub_of_le ok.1]
  change (hi.val*2^(k-c)+t.val.2*2^(k-c-t.val.1))/2^(k-(c+t.val.1))=_
  rw [show k-(c+t.val.1)=k-c-t.val.1 by omega,power,←Nat.mul_assoc,←Nat.add_mul,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  rfl

def present {r : ℕ} (c depth : ℕ) (oldWord : Block r→ℕ) (t : Code r) : Bool :=
  decide (depth=c+t.val.1 ∧ oldWord (sample t)%2=0)

variable {F P : Type} [Field F] {d : ℕ} {bw : P→ℕ} {A : MarkedWorld F d P bw}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Z.Terminals)
local notation "R" => Z.placement
local notation "c" => T.commonDepth
local notation "r" => Z.k-c

theorem root_present (v : Z.V) (hi : Block c) (t : Code r) (oldWord : Block r→ℕ)
    (mode : ∀i,oldWord i%2=Bool.toNat (decide ((R).hub v ∨ (v,group ((R).b v)
      (join ((T.commonLow v).trans ((R).depth v)) hi i))∈(R).keys))) :
    present c ((R).b v) oldWord t=true ↔
      ∃g : (R).Good,Z.rootVertex T (.inl g)=v ∧ Z.rootBlock T (.inl g)=hi ∧ Z.goodLabel T g=t := by
  let d₀:=(R).b v
  let small: c≤Z.k:=(T.commonLow v).trans ((R).depth v)
  let full:=number hi t
  have ok:=codes_valid t.property
  have encode : ∀z : ℕ,z%2^t.val.1=t.val.2→z/2^t.val.1=hi.val→z=full := by
    intro z low high
    calc z=z%2^t.val.1+2^t.val.1*(z/2^t.val.1):=(Nat.mod_add_div ..).symm
         _=full:=by simp [low,high,full,number,Nat.mul_comm,Nat.add_comm]
  simp only [present,decide_eq_true_eq]
  constructor
  · rintro ⟨dep,alive⟩
    have groupNo : group ((R).b v) (join small hi (sample t))=full:=by rw [dep];apply sample_group
    have clean : ¬((R).hub v ∨ (v,full)∈(R).keys):=by
      intro wrong
      rw [mode,groupNo] at alive
      simp [wrong] at alive
    have fits : full<2^((R).b v) := groupNo ▸ group_lt ((R).depth v) _
    let g' : (R).Good:=⟨⟨v,⟨full,fits⟩⟩,by
      change _∉validBases (R).b (R).keys ∧ ¬(R).hub v
      exact ⟨fun bad=>clean (.inr ((Finset.mem_filter.mp bad).2)),fun hub=>clean (.inl hub)⟩⟩
    refine ⟨g',rfl,Fin.ext ?_,Subtype.ext ?_⟩
    · change full/2^((R).b v-c)=hi.val
      simp only [full,number,dep,Nat.add_sub_cancel_left]
      rw [Nat.mul_comm hi.val,Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt ok.2,Nat.add_zero]
    · change ((R).b v-c,full%2^((R).b v-c))=t.val
      apply Prod.ext
      · omega
      · simp [full,number,dep,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt ok.2]
  · rintro ⟨g',atV,atHigh,atLabel⟩
    change g'.val.1=v at atV
    have d₀v : (R).b v-c=t.val.1 := by
      have num:=congrArg (fun z : Code r=>z.val.1) atLabel
      change (R).b g'.val.1-c=t.val.1 at num
      rwa [atV] at num
    have depthAt : (R).b g'.val.1-c=t.val.1 := (congrArg (fun w => (R).b w-c) atV).trans d₀v
    have dep : (R).b v=c+t.val.1:=by have:=T.commonLow v;omega
    refine ⟨dep,?_⟩
    have low : g'.val.2.val%2^t.val.1=t.val.2:=by
      have num:=congrArg (fun z : Code r=>z.val.2) atLabel
      change g'.val.2.val%2^((R).b g'.val.1-c)=t.val.2 at num
      rwa [depthAt] at num
    have high : g'.val.2.val/2^t.val.1=hi.val:=by
      have num:=congrArg Fin.val atHigh
      change g'.val.2.val/2^((R).b g'.val.1-c)=hi.val at num
      rwa [depthAt] at num
    have contains:=encode _ low high
    have clean : ¬((R).hub v ∨ (v,full)∈(R).keys) := by
      rintro (hub|bad)
      · exact g'.property.2 (by rw [atV];exact hub)
      · apply g'.property.1
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        exact (congrArg (fun pair => pair ∈ (R).keys) (congrArg₂ Prod.mk atV contains)).mpr bad
    have groupNo : group ((R).b v) (join small hi (sample t))=full :=
      (congrArg (fun depth => group depth (join small hi (sample t))) dep).trans (sample_group small hi t)
    rw [mode,groupNo]
    change (decide ((R).hub v ∨ (v,full)∈(R).keys)).toNat=0
    simp [clean]

end
end Hierarchy.DescentRotorRootPresence

end OAI
