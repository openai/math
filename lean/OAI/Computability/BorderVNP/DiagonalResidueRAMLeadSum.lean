import OAI.Computability.BorderVNP.DiagonalResidueRAMLead

/-! # The lead team's signed native sum and burst-accounted tick cost -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator
variable {w : ℕ} {S : Type*}

private def unsigned : TeamRAM.Instr w S → Bool
  | .call .. => false
  | .localStep _ z => z == .plus
  | _ => true

private theorem plain_action (i : TeamRAM.Instr w S) (h : unsigned i = true)
    {a b vs t sign} (ha : i.action = some a) (ht : i.advance b vs = some (t,sign)) :
    a.extra = 0 ∧ sign = .plus := by
  cases i with
  | accept | reject | call => contradiction
  | localStep s z =>
    simp [TeamRAM.Instr.action] at ha
    subst a
    cases b <;> cases vs <;> try contradiction
    simp [TeamRAM.Instr.advance] at ht
    simp_all [unsigned, TeamTranscript.Action.extra]
  | choose f =>
    simp [TeamRAM.Instr.action] at ha; subst a
    cases b with
    | nil => contradiction
    | cons x xs =>
      cases xs <;> cases vs <;> try contradiction
      simp [TeamRAM.Instr.advance] at ht
      simp [ht.2.symm,TeamTranscript.Action.extra]
  | load | store =>
    simp [TeamRAM.Instr.action] at ha; subst a
    cases b <;> try contradiction
    cases vs with
    | nil => contradiction
    | cons x xs =>
      cases xs <;> try contradiction
      simp [TeamRAM.Instr.advance] at ht
      simp [ht.2.symm,TeamTranscript.Action.extra]

private theorem plain_prefix {P : S → TeamRAM.Instr w S} (hp : ∀ s, unsigned (P s) = true)
    {s m es z mz} (r : NativePrefix P s m es z mz) :
    traceCost es = es.length ∧ signedWeight es = 1 := by
  induction r with
  | nil => exact ⟨rfl,rfl⟩
  | @cons s m a bits t sign es z mz ha ht _ ih =>
    have hh := plain_action (P s) (hp s) ha ht
    simp [traceCost, VPVNP.RAMBuckets.cost,signedWeight,hh.1,hh.2,TeamRAM.Sign.value] at ih ⊢
    exact ⟨by rw [ih.1, Nat.add_comm],ih.2⟩

/-- Every ordinary signed-team program with only native opcodes uses one
ordinary tick per event and contributes sign plus on each returning path. -/
theorem plain_return {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} (c : Code)
    (hc : ∀ pc, c.program.tag pc = .native) {s m es z mz} (r : Runs pub mac c s m es z mz) :
    traceCost es = es.length ∧ signedWeight es = 1 := by
  apply plain_prefix _ (at_last r)
  intro q
  simp only [TeamOpcode.Program.fetch,hc]
  split
  · cases ((c.program.base.code q.pc).resize w).runLogged pub q.logged <;> try rfl
    rename_i a
    cases a <;> rfl
  · rfl

/-- Reduction of the lead team's count, with the deterministic other-team
branch represented by its one physical trace. -/
theorem lead_card (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) :
    Nat.card (LeadReturns pub mac s m) =
      if m (pub 0).val = 0 then Nat.card (StagedPaths pub mac (leadBank pub s m) m) else 1 := by
  split
  next h => exact (Nat.card_congr (leadZeroEquiv s m h)).symm
  next h => exact lead_other_card s m h

/-- The lead fragment has finitely many returns. The finite reader proof is
needed only for team zero, since every other team follows its single unit path. -/
theorem lead_finite (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (h : m (pub 0).val = 0 → Finite (StagedPaths pub mac (leadBank pub s m) m)) :
    Finite (LeadReturns pub mac s m) := by
  by_cases zero : m (pub 0).val = 0
  · let _ := h zero
    exact Finite.of_equiv _ (leadZeroEquiv s m zero)
  · exact Nat.finite_of_card_ne_zero (by rw [lead_other_card s m zero]; decide)

/-- With any finite enumeration of actual returning event histories the
signed sum is the residue path count on team zero and the integer one on
every other team. -/
theorem lead_signed (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    [Fintype (LeadReturns pub mac s m)] :
    (∑ z : LeadReturns pub mac s m, signedWeight z.val) =
      if m (pub 0).val = 0 then (Nat.card (StagedPaths pub mac (leadBank pub s m) m) : ℤ) else 1 := by
  have one (p : LeadReturns pub mac s m) : signedWeight p.val = 1 := by
    obtain ⟨_,_,r⟩ := p.property
    exact (plain_return leadEntry (by decide) r).2
  simp only [one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,mul_one,← Nat.card_eq_fintype_card,
    lead_card pub mac s m, Nat.cast_ite, Nat.cast_one]

/-- The nonzero team has exactly seven charged ticks. -/
theorem lead_other_ticks {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es z mz}
    (team : m (pub 0).val ≠ 0) (r : Runs pub mac leadEntry s m es z mz) :
    traceCost es = 7 ∧ signedWeight es = 1 := by
  have hr := (lead_other_iff s m team).mp r
  have eq := plain_return leadEntry (by decide) r
  exact ⟨eq.1.trans (hr.1 ▸ rfl),eq.2⟩

variable {u v k : ℕ}

/-- Exact charged clock and private choices of every accepting lead-team
path, including staging and the six actual team-ID checks. -/
theorem lead_zero_ticks (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (mem : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
    (c : VPVNP.BooleanTranscript.Circuit (Fin u ⊕ Fin v) k) (x : Fin u → Bool)
    (L : Layout base start dense src v k w) (hpub : (pub 0).val+30 < 2^w)
    (hframe : packFrame pub mem dense start (6+3*k+u))
    (hbits : DiagonalTallyBits.WordsAt mem dense ((payload w base start c src).map wordBits))
    (hsrc : ∀ i, mem (src i) = wordBit w (x i)) (team : mem (pub 0).val = 0)
    {es z mz} (r : Runs pub mac leadEntry s mem es z mz) :
    ∃ y : Fin v → Bool, c.eval (Sum.elim x y) = true ∧ es.flatMap TeamRAM.Event.choices = List.ofFn y ∧
      traceCost es = 6 + (prepareTicks u k w + ticks k v) ∧ signedWeight es = 1 := by
  obtain ⟨tail,he,rt⟩ := (lead_iff s mem).mp r
  rw [ite_eq_left team] at rt
  obtain ⟨y,hy,ht⟩ := staged_trace pub mac (leadBank pub s mem) mem base start dense src c x L hpub hframe
    hbits hsrc ⟨tail,rt.execute⟩
  have tr := (leadPrefix_trace pub mem).append ht
  rw [← he] at tr
  have hc := plain_return leadEntry (by decide) r
  exact ⟨y,hy,tr.2.1,hc.1.trans tr.1,hc.2⟩

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
