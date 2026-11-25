import OAI.Computability.BorderVNP.TransmissionPinsRead
import OAI.Computability.BorderVNP.TransmissionPinsEffects

/-! # Semantics of one substituted index position -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Pins

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

instance (L : Layout) (x : ℕ) : Decidable (L.active x) := inferInstanceAs
  (Decidable (L.team = 0 ∧ x < L.width))

/-- Only the real prefix on team zero contributes a bit to the nondeterministic path. -/
def stepBits (L : Layout) (x : ℕ) (b : Bool) : List Bool :=
  if L.active x then [b] else []

/-- The exact scratch-memory updates, retaining the true physical live word at active positions. -/
def nextMemory (L : Layout) (x : ℕ) (m : Memory w) (b : Bool) : Memory w :=
  if L.active x then
    Function.update (Function.update m (L.hbase+x) (m (livePinAddress L.teams L.literal L.link x)))
      (L.ibase+x) (Fin.ofNat _ b.toNat)
  else Function.update m (L.ibase+x) 0

private theorem word_sum {s : Bank w} {u v : Reg} {a b : ℕ}
    (hu : readings s u = a) (hv : readings s v = b) (fit : a+b < 2^w) :
    (s u + s v).val = a+b := by
  change ((s u).val+(s v).val) % 2^w = a+b
  rw [show (s u).val = a from hu, show (s v).val = b from hv, Nat.mod_eq_of_lt fit]

private theorem Ready.agree {L : Layout} {x : ℕ} {s t : Bank w} (h : Ready L x s)
    (he : SamePrefix s t) : Ready L x t := h.congr fun i hi => congrArg Fin.val (he i hi)

private theorem Ready.advance {L : Layout} {x : ℕ} {s t : Bank w} (h : Ready L x s)
    (hx : x < L.count) (he : SamePrefix (Function.update s 6 (s 6+s 1)) t) :
    Ready L (x+1) t := by
  have fit : x+1 < 2^w := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hx) (h.count ▸ (s 7).isLt)
  have h6 := word_sum h.cursor h.one fit
  have hup : Ready L (x+1) (Function.update s 6 (s 6+s 1)) := by
    rcases h with ⟨a,b,c,d,e,f,g,h,i,j,k,l⟩
    constructor <;> simp (config := {decide := true}) only [readings, Function.update_apply, ite_false,
      ite_true] at * <;> assumption
  exact hup.agree he

private def condition : Code :=
  .ifEq 0 2 (.ifLt 6 8 chooseRealPin (.copy 15 2)) (.copy 15 2)

private theorem zeroBit (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (L : Layout) (x : ℕ) (h : Ready L x s) :
    ∃ es t, Runs pub macros (.copy 15 2) s m es t m ∧ traceCost es = 1 ∧
      es.flatMap TeamRAM.Event.choices = [] ∧ Ready L x t ∧ t 15 = 0 := by
  refine ⟨_,_,Runs.localStep m rfl rfl, rfl, rfl, h.agree ?_, ?_⟩
  · intro i hi
    have ne : i ≠ 15 := by intro he; subst i; omega
    simp [ne]
  · exact (Function.update_self ..).trans (Fin.ext h.zero)

private theorem chooseRealPin_run (L : Layout) (x : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w) (b : Bool)
    (h : Ready L x s) (hl : 0<L.literal)
    (ha : livePinAddress L.teams L.literal L.link x < 2^w) (hc : L.hbase+x < 2^w) :
    ∃ es t, Runs pub macros chooseRealPin s m es t
      (Function.update m (L.hbase+x) (m (livePinAddress L.teams L.literal L.link x))) ∧
      traceCost es ≤ 10 ∧ es.flatMap TeamRAM.Event.choices = [b] ∧ Ready L x t ∧
      t 15 = Fin.ofNat _ b.toNat := by
  obtain ⟨es,t,r,ct,hr,h14⟩ := fetchLivePin_run L x pub macros m s h hl ha
  obtain ⟨fs,z,q,cs,hs,hpref,hbit⟩ := realTail_run pub macros t m b
  have read : t 14 = m (livePinAddress L.teams L.literal L.link x) := Fin.ext h14
  rw [word_sum hr.hbase hr.cursor hc, read] at q
  refine ⟨es++fs,z, r.seq q, ?_, ?_, hr.agree hpref, ?_⟩
  · have : fetchLivePin.slots = 6 := rfl
    have hcost : traceCost (es++fs) = traceCost es + traceCost fs := VPVNP.RAMBuckets.cost_append ..
    rw [hcost, cs]
    omega
  · simp [List.flatMap_append, noChoices r (by rfl), hs]
  · rw [hbit]
    cases b
    · exact Fin.ext hr.zero
    · apply Fin.ext
      change (t 1).val = 1 % 2^w
      exact hr.one.trans (Nat.mod_eq_of_lt (hr.one ▸ (t 1).isLt)).symm

private theorem condition_run (L : Layout) (x : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w) (b : Bool)
    (h : Ready L x s) (hl : 0<L.literal)
    (ha : livePinAddress L.teams L.literal L.link x < 2^w) (hc : L.active x → L.hbase+x < 2^w) :
    ∃ es t, Runs pub macros condition s m es t
      (if L.active x then Function.update m (L.hbase+x) (m (livePinAddress L.teams L.literal L.link x)) else m) ∧
      traceCost es ≤ 12 ∧ es.flatMap TeamRAM.Event.choices = stepBits L x b ∧ Ready L x t ∧
      t 15 = (if L.active x then Fin.ofNat _ b.toNat else 0) := by
  have he : s 0 = s 2 ↔ L.team = 0 := (Fin.ext_iff).trans (by change readings s 0 = readings s 2 ↔ _; rw [h.team,h.zero])
  have hw : s 6 < s 8 ↔ x < L.width := by change readings s 6 < readings s 8 ↔ _; rw [h.cursor,h.width]
  by_cases ht : L.team = 0
  · by_cases hh : x < L.width
    · have hact : L.active x := ⟨ht,hh⟩
      obtain ⟨es,t,r,ct,bs,hr,hb⟩ := chooseRealPin_run L x pub macros m s b h hl ha (hc hact)
      refine ⟨tick w :: tick w :: es,t,.ifEq ?_, ?_, ?_, hr, ?_⟩
      · rw [ite_eq_left (he.mpr ht), ite_eq_left hact]
        exact .ifLt (by rw [ite_eq_left (hw.mpr hh)]; exact r)
      · change 1+(1+traceCost es) ≤ 12; omega
      · simp [tick,stepBits,hact,bs]
      · simpa [hact] using hb
    · have hact : ¬ L.active x := fun a => hh a.2
      obtain ⟨es,t,r,ct,bs,hr,hb⟩ := zeroBit pub macros s m L x h
      refine ⟨tick w :: tick w :: es,t,.ifEq ?_, ?_, ?_, hr, ?_⟩
      · rw [ite_eq_left (he.mpr ht), ite_eq_right hact]
        exact .ifLt (by rw [ite_eq_right (hw.not.mpr hh)]; exact r)
      · change 1+(1+traceCost es) ≤ 12; omega
      · simp [tick,stepBits,hact,bs]
      · simpa [hact] using hb
  · have hact : ¬ L.active x := fun a => ht a.1
    obtain ⟨es,t,r,ct,bs,hr,hb⟩ := zeroBit pub macros s m L x h
    refine ⟨tick w :: es,t,.ifEq ?_, ?_, ?_, hr, ?_⟩
    · rw [ite_eq_right (he.not.mpr ht), ite_eq_right hact]
      exact r
    · change 1+traceCost es ≤ 12; omega
    · simp [tick,stepBits,hact,bs]
    · simpa [hact] using hb

/-- One actual evaluation-loop iteration costs at most sixteen ticks, records its guess
only on the real prefix, preserves the frame registers and makes precisely the prescribed
physical memory updates. -/
theorem preparePinStep_run (L : Layout) (x : ℕ) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (m : Memory w) (s : Bank w) (b : Bool) (h : Ready L x s)
    (hx : x < L.count) (hl : 0<L.literal)
    (ha : livePinAddress L.teams L.literal L.link x < 2^w) (hi : L.ibase+x < 2^w)
    (hc : L.active x → L.hbase+x < 2^w) :
    ∃ es t, Runs pub macros preparePinStep s m es t (nextMemory L x m b) ∧
      traceCost es ≤ 16 ∧ es.flatMap TeamRAM.Event.choices = stepBits L x b ∧ Ready L (x+1) t := by
  obtain ⟨es,t,r,ct,bs,hr,hv⟩ := condition_run L x pub macros m s b h hl ha hc
  obtain ⟨fs,z,q,cs,hs,pref⟩ := stepTail_run pub macros t _
  rw [word_sum hr.ibase hr.cursor hi, hv] at q
  refine ⟨es++fs,z, ?_, ?_, ?_, hr.advance hx pref⟩
  · have run := r.seq q
    by_cases act : L.active x <;> simpa only [preparePinStep, condition, stepTail, Code.block,
      nextMemory, act, ite_true, ite_false] using run
  · have hcost : traceCost (es++fs) = traceCost es + traceCost fs := VPVNP.RAMBuckets.cost_append ..
    rw [hcost, cs]; omega
  · simp only [List.flatMap_append, bs, hs, List.append_nil]

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
