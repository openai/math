import OAI.Computability.VPVNP.RAMTapePublicGeometryPorts

/-!
# Public-expression registers initialized from the original site tape

The record startup first parses the physical input and prepares its public
processor fields. The next finite routine forms the four fixed-width
arithmetic inputs. Its quadratic preparation cost fits the existing startup
clock for all lengths and sites satisfying the processor input bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicGeometry.Physical

open BurstRAM LiveProgram PublicExprMachine RAMLayout ProcessorInput StackCompiler

private theorem geometry_fit {B n d e w : ℕ} (hB : 1 ≤ B) (hd : d = B * Nat.clog 2 n) (hcap : d+e < w) :
    ∀ i, geometryNat ⟨n,d,2^e,w⟩ i < 2^w := by
  have hclog : Nat.clog 2 n ≤ d := hd ▸ Nat.le_mul_of_pos_left _ hB
  have hdw : d < w := by omega
  have hn := (Nat.le_pow_clog (by decide : 1 < 2) n).trans_lt
    (Nat.pow_lt_pow_right (by decide) (hclog.trans_lt hdw))
  have hh : 2^e < 2^w := Nat.pow_lt_pow_right (by decide) (by omega)
  intro i
  fin_cases i
  · exact hn
  · exact hdw.trans Nat.lt_two_pow_self
  · exact hh
  · exact Nat.lt_two_pow_self

private theorem budget_le {g : Geometry} (r : ℕ) (hd : g.d ≤ g.w) (hw : g.w ≤ g.n) (hH : g.H ≤ 2*g.n) :
    budget g r ≤ (140+11*r)*(g.n+1)^2 := by
  have hsum : g.n+g.d+g.H+g.w+1 ≤ 5*(g.n+1) := by omega
  have hprep := (PublicGeometry.steps_le g).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 25 hsum) (Nat.succ_le_succ hw))
  have hadd : r*(8*g.w+3) ≤ r*(11*(g.n+1)) := Nat.mul_le_mul_left _ (by omega)
  unfold budget
  nlinarith only [hprep, hadd, hw, Nat.zero_le g.n, Nat.zero_le (g.n*g.n), Nat.zero_le (r*g.n*g.n),
    Nat.zero_le (r*g.n), Nat.zero_le r]

/-- Parse the raw site and prepare its initial-record words, then convert the geometry tallies
and initialize the arithmetic registers. -/
def startup (r B p q u lit : ℕ) (hq : 0 < q) : FiniteRoutine (Port r) :=
  ((ProcessorPublic.recordStartup B p q u lit hq).onPorts Sum.inl).followedBy (prepare r)

/-- The fixed public arithmetic register bank is ready after parsing an
actual complete processor input, with every original public stack retained. -/
theorem startup_runs (r B p q u lit : ℕ) (hB : 1 ≤ B) (hq : 0 < q) (hpq : p ≤ q) (hu : 1 ≤ u)
    (prog : UniversalMachine.Program) (n : ℕ) (hn : 1 ≤ n) :
    let d := B*Nat.clog 2 n
    let e := roundedUp p q n
    let w := (d+10)^4
    ∀ (v : Word d) (hdr : Header) (inc : Fin (width d (2^e) w) → Bool), Fits prog n d (2^e) w →
      let processor := ProcessorPublic.recordResult (ProcessorPublic.rawResult prog n d (2^e) w v hdr inc)
        n d e w u lit v hdr (ProcessorPublic.capFits B p q n hB hq hpq hn) (ProcessorPublic.recordWidth_ge_four d)
      ∃ t ≤ (ProcessorPublic.recordClockCoefficient B p q u + 140+11*r)*(n+1)^(max 7 (u+1)),
        (startup r B p q u lit hq).Runs t
          (labeledInput (.inl ProcessorPublic.rawPort) (ProcessorInput.tape prog n v hdr inc))
          (Sum.elim processor (ISA.bank (geometryWords ⟨n,d,2^e,w⟩) 0 (fun _ => 0) [])) := by
  intro d e w v hdr inc fit processor
  let g : Geometry := ⟨n,d,2^e,w⟩
  let tape := ProcessorInput.tape prog n v hdr inc
  obtain ⟨u₁,hw₁,h₁⟩ := ProcessorPublic.recordStartup_runs B p q u lit hB hq hpq hu prog n hn v hdr inc fit
  have lifted : ((ProcessorPublic.recordStartup B p q u lit hq).onPorts (Sum.inl : _ → Port r)).Runs u₁
      (labeledInput (.inl ProcessorPublic.rawPort) tape) (Sum.elim processor (fun _ => [])) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective h₁
    · intro j; simp [labeledInput, tape]
    · intro j; rfl
    · rintro (j | j) h
      · exact (h j rfl).elim
      · rfl
  have cap := ProcessorPublic.capFits B p q n hB hq hpq hn
  change d+e < w at cap
  obtain ⟨u₂,hw₂,h₂⟩ := prepare_runs (r := r) g processor rfl rfl rfl rfl rfl (geometry_fit hB rfl cap)
  refine ⟨u₁+u₂,?_,lifted.followedBy h₂⟩
  have hwn : w ≤ n := by
    change (UniversalMachine.programPrefix prog).length + (d + 4 + width d (2^e) w) ≤ n at fit
    rw [width_eq] at fit
    omega
  have hbudget := budget_le (g := g) r (by change d ≤ w; omega) hwn (InputBucketFromSize.bucket_le hq hpq hn)
  have hpow := Nat.pow_le_pow_right (Nat.succ_pos n) (show 2 ≤ max 7 (u+1) by omega)
  rw [Nat.add_assoc, Nat.add_mul]
  exact Nat.add_le_add hw₁ (hw₂.trans (hbudget.trans (Nat.mul_le_mul_left _ hpow)))

end RAMTape.PublicGeometry.Physical

end VPVNP
end Computability
end OAI
