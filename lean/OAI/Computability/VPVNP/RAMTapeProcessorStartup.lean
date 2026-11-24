import OAI.Computability.VPVNP.RAMTapeProcessorPublic
import OAI.Computability.VPVNP.RAMTapeSiteRecordWords

/-!
# Preparing the live processor's public bank and initial-record words

Starting with only the raw site input, the program parses its literal prefix and fields,
computes the public bounds and the two cost endpoints, and zero-extends the parsed address
and four header bits into the two words used by the initial memory record.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProcessorPublic

open BurstRAM ProcessorInput RAMLayout StackCompiler

private def recordPorts : SiteRecordWords.Port → Port
  | .address => addressPort
  | .header => headerPort
  | .siteLog => addressWidthPort
  | .width => widthPort
  | .addressWord => addressWordPort
  | .headerWord => headerWordPort
  | .count => .inr (.scratch 0)
  | .tmp => .inr (.scratch 1)

private theorem recordPorts_inj : Function.Injective recordPorts := by decide

/-- The two record words occupy their dedicated stacks in the prepared bank. -/
def recordResult (base : Stacks SiteSetup.Port) (n d e w u lit : ℕ) (v : Word d) (hdr : Header)
    (hcap : d+e<w) (hw : 4≤w) : Stacks Port :=
  Function.update (Function.update (result base n d e w u lit v hcap) addressWordPort
    (BurstRAM.wordBits (SiteRecordWords.addressWord (by omega : d ≤ w) v))) headerWordPort
    (BurstRAM.wordBits (headerWord hw hdr))

section Projections

variable (base : Stacks SiteSetup.Port) (n d e w u lit : ℕ) (v : Word d) (hdr : Header)
  (hcap : d+e<w) (hw : 4≤w)

/-- Every parsed input and tally in the setup bank survives the record preparation. -/
@[simp] theorem recordResult_site (i : SiteSetup.Port) :
    recordResult base n d e w u lit v hdr hcap hw (.inl i) = base i := rfl

/-- All public output registers, including the empty shared scratch bank. -/
@[simp] theorem recordResult_extra (i : Extra) :
    recordResult base n d e w u lit v hdr hcap hw (.inr i) =
      match i with
      | .fuel => List.replicate (n^u) true
      | .callCredit => List.replicate (2 * 2^e - 1) true
      | .choiceBudget => List.replicate (2 * 2^e * (n^u+w)) true
      | .bucketLog => List.replicate e true
      | .globalCap => BurstRAM.wordBits (SuccessorParameters.capWord d e w hcap)
      | .startCost => BurstRAM.wordBits (SiteEndpoints.startWord e w v hcap)
      | .endCost => BurstRAM.wordBits (SiteEndpoints.endWord e w v hcap)
      | .initial => BurstRAM.wordBits (Fin.ofNat (2^w) lit)
      | .addressWord => BurstRAM.wordBits (SiteRecordWords.addressWord (by omega : d≤w) v)
      | .headerWord => BurstRAM.wordBits (headerWord hw hdr)
      | .scratch _ => [] := by cases i <;> rfl

end Projections

/-- Fixed processor preparation, including both words of the initial record. -/
def recordStartup (B p q u lit : ℕ) (hq : 0 < q) : FiniteRoutine Port :=
  (startup B p q u lit hq).followedBy (SiteRecordWords.prepare recordPorts)

/-- Clock coefficient for public startup including preparation of the initial record’s address
and header words. -/
def recordClockCoefficient (B p q u : ℕ) := clockCoefficient B p q u + 89

theorem recordWidth_ge_four (d : ℕ) : 4 ≤ (d+10)^4 :=
  (show 4 ≤ d+10 by omega).trans (Nat.le_self_pow (by decide) _)

set_option maxHeartbeats 1000000 in
/-- The only initially occupied stack carries the complete input, including the program prefix.
On return all parsed fields, cost and fuel registers, and initial-record words are present. -/
theorem recordStartup_runs (B p q u lit : ℕ) (hB : 1 ≤ B) (hq : 0 < q) (hpq : p ≤ q) (hu : 1 ≤ u)
    (prog : UniversalMachine.Program) (n : ℕ) (hn : 1 ≤ n) :
    let d := B * Nat.clog 2 n
    let e := roundedUp p q n
    let w := (d+10)^4
    ∀ (v : Word d) (hdr : Header) (inc : Fin (width d (2^e) w) → Bool),
      Fits prog n d (2^e) w →
      ∃ t ≤ recordClockCoefficient B p q u * (n+1)^(max 7 (u+1)),
        (recordStartup B p q u lit hq).Runs t (labeledInput rawPort (ProcessorInput.tape prog n v hdr inc))
          (recordResult (rawResult prog n d (2^e) w v hdr inc) n d e w u lit v hdr
            (capFits B p q n hB hq hpq hn) (recordWidth_ge_four d)) := by
  intro d e w v hdr inc fit
  let hcap := capFits B p q n hB hq hpq hn
  have hdw : d ≤ w := by change d+e < w at hcap; omega
  have hw := recordWidth_ge_four d
  let base := rawResult prog n d (2^e) w v hdr inc
  obtain ⟨t, ht, run⟩ := startup_runs B p q u lit hB hq hpq hu prog n hn v hdr inc fit
  have words := SiteRecordWords.prepare_runs recordPorts recordPorts_inj
    (result base n d e w u lit v hcap) v hdr hdw hw rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨_, ?_, run.followedBy words⟩
  have hsize : w ≤ n := by
    change (UniversalMachine.programPrefix prog).length + (d + 4 + width d (2^e) w) ≤ n at fit
    rw [width_eq] at fit
    omega
  have hpow : n+1 ≤ (n+1)^(max 7 (u+1)) := Nat.le_self_pow (by omega) _
  have hcost := SiteRecordWords.steps_le hdw
  unfold recordClockCoefficient
  rw [Nat.add_mul]
  exact Nat.add_le_add ht ((hcost.trans (by omega : 23*w+66 ≤ 89*(n+1))).trans
    (Nat.mul_le_mul_left _ hpow))

end RAMTape.ProcessorPublic

end VPVNP
end Computability
end OAI
