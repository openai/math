import OAI.Computability.VPVNP.RAMTapeSiteFuel
import OAI.Computability.VPVNP.RAMTapeSiteLiteral
import OAI.Computability.VPVNP.RAMTapeValidatorSetup
import OAI.Computability.VPVNP.RAMTapeSuccessorParameters
import OAI.Computability.VPVNP.RAMTapeSiteEndpoints

/-!
# Public registers of the fixed site processor

The fields produced by the physical reader share a bank with the cost endpoints
and three instruction tallies. All routines use four temporary stacks in common.
Their finite tables depend only on the processor's fixed parameters.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ProcessorPublic

open BurstRAM ProcessorInput RAMLayout StackCompiler TapeWord

/-- Additional processor registers for fuel, credits, choice bounds, costs, initial-record
words, and four scratch stacks. -/
inductive Extra where
  | fuel | callCredit | choiceBudget | bucketLog | globalCap | startCost | endCost | initial
  | addressWord | headerWord | scratch (i : Fin 4)
  deriving DecidableEq

instance : Fintype Extra := derive_fintype% _
/-- Combined site-setup ports and the additional public processor registers. -/
abbrev Port := SiteSetup.Port ⊕ Extra

/-- Input stack carrying the physical site tape before parsing. -/
def rawPort : Port := .inl SiteSetup.rawPort
/-- Unary per-call private instruction allowance. -/
def fuelPort : Port := .inr .fuel
/-- Unary call credits prepared from the site’s bucket capacity. -/
def creditPort : Port := .inr .callCredit
/-- Unary upper bound on the length of the site’s private choice string. -/
def budgetPort : Port := .inr .choiceBudget
/-- Word encoding the global cumulative-cost cap. -/
def capPort : Port := .inr .globalCap
/-- Word encoding the beginning of the site’s cost interval. -/
def startPort : Port := .inr .startCost
/-- Word encoding the end of the site’s cost interval. -/
def endPort : Port := .inr .endCost
/-- Word holding the validator’s fixed initial-state literal. -/
def initPort : Port := .inr .initial
/-- Padded word containing the site address for the initial record. -/
def addressWordPort : Port := .inr .addressWord
/-- Padded word containing the four header bits for the initial record. -/
def headerWordPort : Port := .inr .headerWord
/-- Unary width of each word in the physical RAM records. -/
def widthPort : Port := .inl SiteSetup.wordPort
/-- Retained unary length of the original input tape. -/
def lengthPort : Port := .inl (.inl InputReader.lengthPort)
/-- Retained unary address width of the site. -/
def addressWidthPort : Port := .inl (.inl InputReader.addressWidthPort)
/-- Retained unary capacity of a site’s cost bucket. -/
def bucketPort : Port := .inl (.inl InputReader.bucketPort)
/-- Stack carrying the parsed site-address bits. -/
def addressPort : Port := .inl (.inl (.inl .address))
/-- Stack carrying the four parsed header bits. -/
def headerPort : Port := .inl (.inl (.inl .header))
/-- Stack carrying the parsed incident vector. -/
def incidentPort : Port := .inl (.inl (.inl .incident))
/-- Stack holding the binary logarithm of the power-of-two bucket capacity in unary. -/
def bucketLogPort : Port := .inr .bucketLog

private def fuelPorts : SiteFuel.Port → Port
  | .length => lengthPort
  | .bucket => bucketPort
  | .word => widthPort
  | .fuel => fuelPort
  | .credit => creditPort
  | .choice => budgetPort
  | .acc => .inr (.scratch 0)
  | .sum => .inr (.scratch 1)
  | .outer => .inr (.scratch 2)
  | .tmp => .inr (.scratch 3)

private def capPorts : SuccessorParameters.Port → Port
  | .siteLog => addressWidthPort
  | .bucket => bucketPort
  | .width => widthPort
  | .bucketLog => bucketLogPort
  | .cap => capPort
  | .work => .inr (.scratch 0)
  | .tmp => .inr (.scratch 1)

private def endpointPorts : SiteEndpoints.Port → Port
  | .address => addressPort
  | .siteLog => addressWidthPort
  | .bucketLog => bucketLogPort
  | .width => widthPort
  | .startCost => startPort
  | .endCost => endPort
  | .count => .inr (.scratch 0)
  | .tmp => .inr (.scratch 1)

private def literalPorts : ScanPort → Port
  | .left => .inl SiteSetup.zerosPort
  | .right => .inr (.scratch 0)
  | .tmp => .inr (.scratch 1)
  | .out => initPort

private theorem fuelPorts_inj : Function.Injective fuelPorts := by decide
private theorem capPorts_inj : Function.Injective capPorts := by decide
private theorem endpointPorts_inj : Function.Injective endpointPorts := by decide
private theorem literalPorts_inj : Function.Injective literalPorts := by decide

private def fueled (base : Stacks SiteSetup.Port) (n H w u : ℕ) : Stacks Port
  | .inl j => base j
  | .inr .fuel => List.replicate (n^u) true
  | .inr .callCredit => List.replicate (2*H-1) true
  | .inr .choiceBudget => List.replicate (2*H*(n^u+w)) true
  | _ => []

private def capped (base : Stacks SiteSetup.Port) (n d e w u : ℕ) (h : d+e<w) : Stacks Port :=
  Function.update (Function.update (fueled base n (2^e) w u) bucketLogPort (List.replicate e true))
    capPort (BurstRAM.wordBits (SuccessorParameters.capWord d e w h))

private def costed (base : Stacks SiteSetup.Port) (n d e w u : ℕ) (v : Word d) (h : d+e<w) :
    Stacks Port :=
  Function.update (Function.update (capped base n d e w u h) startPort
    (BurstRAM.wordBits (SiteEndpoints.startWord e w v h))) endPort
    (BurstRAM.wordBits (SiteEndpoints.endWord e w v h))

/-- Public bank after fuel, credits, choice budget, global cap, site endpoints, and the fixed
initial word have been prepared. -/
def result (base : Stacks SiteSetup.Port) (n d e w u lit : ℕ) (v : Word d) (h : d+e<w) : Stacks Port :=
  Function.update (costed base n d e w u v h) initPort (BurstRAM.wordBits (Fin.ofNat (2^w) lit))

private def fuel (u : ℕ) : FiniteRoutine Port :=
  (FiniteRoutine.ofRoutine (SiteFuel.program u).code).onPorts fuelPorts

/-- Prepare the fuel and choice tallies, global cap, site cost endpoints, and fixed
initial-state word in that order. -/
def parameters (u lit : ℕ) : FiniteRoutine Port :=
  (((fuel u).followedBy (SuccessorParameters.prepare.onPorts capPorts)).followedBy
    (SiteEndpoints.prepare endpointPorts)).followedBy (SiteLiteral.routine lit literalPorts)

/-- Sum of the step counts for fuel preparation, the global cap, endpoint words, and the
initial literal. -/
def steps (n d e w u : ℕ) :=
  (SiteFuel.program u).work (SiteFuel.initial n (2^e) w) + SuccessorParameters.steps d e w +
    SiteEndpoints.steps d e w + (7*w+3)

theorem parameters_runs (base : Stacks SiteSetup.Port) (n d e w u lit : ℕ) (v : Word d) (h : d+e<w)
    (hn : base (.inl InputReader.lengthPort) = List.replicate n true)
    (hd : base (.inl InputReader.addressWidthPort) = List.replicate d true)
    (hH : base (.inl InputReader.bucketPort) = List.replicate (2^e) true)
    (hw : base SiteSetup.wordPort = List.replicate w true)
    (hv : base (.inl (.inl .address)) = BurstRAM.wordBits v)
    (hz : base SiteSetup.zerosPort = List.replicate w false) :
    (parameters u lit).Runs (steps n d e w u) (Sum.elim base (fun _ => []))
      (result base n d e w u lit v h) := by
  have h₁ : (fuel u).Runs ((SiteFuel.program u).work (SiteFuel.initial n (2^e) w))
      (Sum.elim base (fun _ => [])) (fueled base n (2^e) w u) := by
    apply FiniteRoutine.runs_onPorts_framed _ fuelPorts_inj (SiteFuel.runs n (2^e) w u)
    · intro j; cases j <;> first | rfl | exact hn | exact hH | exact hw
    · intro j; cases j <;> first | rfl | exact hn | exact hH | exact hw
    · rintro (i | j) hi
      · rfl
      · cases j <;> first | rfl | exact (hi .fuel rfl).elim | exact (hi .credit rfl).elim |
                            exact (hi .choice rfl).elim
  have h₂ := SuccessorParameters.prepare_onPorts_runs capPorts capPorts_inj
    (fueled base n (2^e) w u) d e w h (by intro j; cases j <;> first | rfl | exact hd | exact hH | exact hw)
  have h₃ := SiteEndpoints.prepare_runs endpointPorts endpointPorts_inj (capped base n d e w u h)
    v e w h hv hd rfl hw rfl rfl rfl rfl
  have h₄ := SiteLiteral.runs lit literalPorts literalPorts_inj (costed base n d e w u v h) (0 : Word w)
    (hz.trans (UnaryWord.zeros_wordBits w)) rfl rfl
  rw [show (costed base n d e w u v h (literalPorts .out)).length = 0 from rfl, Nat.zero_add] at h₄
  exact ((h₁.followedBy h₂).followedBy h₃).followedBy h₄

theorem steps_le (n d e w u : ℕ) (h : d+e<w) (hu : 1 ≤ u) (hH : 2^e ≤ 2*n) (hw : w ≤ n) :
    steps n d e w u ≤ (26*u+285)*(n+1)^(u+1) := by
  let M := (n+1)^(u+1)
  have hm : n+1 ≤ M := Nat.le_self_pow (by omega) _
  have h₁ := SiteFuel.work_le n (2^e) w u hu hH hw
  have h₂ := SuccessorParameters.steps_le d e w
  have h₃ := SiteEndpoints.steps_le d e w h
  change _ ≤ (26*u+285)*M
  change _ ≤ (26*u+113)*M at h₁
  rw [show 26*u+285 = (26*u+113)+172 by omega, Nat.add_mul]
  unfold steps
  omega

/-- The fixed register table derives its cost width from the length. -/
theorem capFits (B p q n : ℕ) (hB : 1 ≤ B) (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n) :
    B*Nat.clog 2 n + roundedUp p q n < (B*Nat.clog 2 n+10)^4 := by
  let d := B*Nat.clog 2 n
  have he : roundedUp p q n ≤ Nat.clog 2 n := by
    rw [roundedUp, Nat.clog_le_iff_le_pow (Nat.one_lt_pow hq.ne' (by decide))]
    calc
      n^p ≤ n^q := Nat.pow_le_pow_right (by omega) hpq
      _ ≤ (2^(Nat.clog 2 n))^q := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) n) q
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hd : Nat.clog 2 n ≤ d := Nat.le_mul_of_pos_left _ (by omega)
  have hs : (d+10)^2 ≤ (d+10)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have h₁ : d + roundedUp p q n < (d+10)^2 := by rw [pow_two]; nlinarith
  exact h₁.trans_le hs

/-- Site-setup bank for the parsed program prefix, address, header, and incident vector with
word and sorting sizes prepared. -/
def rawResult (prog : UniversalMachine.Program) (n d H w : ℕ) (v : Word d)
    (hdr : Header) (inc : Fin (width d H w) → Bool) : Stacks SiteSetup.Port :=
  SiteSetup.prepared (InputReader.physicalResult n d H (UniversalMachine.programPrefix prog)
    (BurstRAM.wordBits v) (List.ofFn hdr) (List.ofFn inc)) d H

/-- Parse and size the physical site, then initialize the public execution parameters. -/
def startup (B p q u lit : ℕ) (hq : 0 < q) : FiniteRoutine Port :=
  ((SiteSetup.routine B p q hq).onPorts Sum.inl).followedBy (parameters u lit)

/-- Fixed coefficient bounding the work of parsing, sizing, and initializing the public
processor bank. -/
def clockCoefficient (B p q u : ℕ) :=
  InputParameters.clockCoefficient B p q+43+1026*(B+13)^7+(26*u+285)

/-- Run the actual parser and cost register table from the sole original input stack. -/
theorem startup_runs (B p q u lit : ℕ) (hB : 1 ≤ B) (hq : 0 < q) (hpq : p ≤ q) (hu : 1 ≤ u)
    (prog : UniversalMachine.Program) (n : ℕ) (hn : 1 ≤ n) :
    let d := B * Nat.clog 2 n
    let e := roundedUp p q n
    let w := (d+10)^4
    ∀ (v : Word d) (hdr : Header) (inc : Fin (width d (2^e) w) → Bool),
      Fits prog n d (2^e) w →
      ∃ t ≤ clockCoefficient B p q u * (n+1)^(max 7 (u+1)),
        (startup B p q u lit hq).Runs t (labeledInput rawPort (ProcessorInput.tape prog n v hdr inc))
          (result (rawResult prog n d (2^e) w v hdr inc) n d e w u lit v (capFits B p q n hB hq hpq hn)) := by
  intro d e w v hdr inc fit
  let base := rawResult prog n d (2^e) w v hdr inc
  let raw := ProcessorInput.tape prog n v hdr inc
  let hcap := capFits B p q n hB hq hpq hn
  obtain ⟨t, ht, run⟩ := SiteSetup.runs B p q hq hpq prog n hn v hdr inc fit
  have h₁ : ((SiteSetup.routine B p q hq).onPorts Sum.inl).Runs t
      (labeledInput rawPort raw) (Sum.elim base (fun _ => [])) := by
    apply FiniteRoutine.runs_onPorts_framed _ Sum.inl_injective run
    · intro j; simp [labeledInput, raw, rawPort]
    · intro j; rfl
    · rintro (i | j) hi
      · exact (hi i rfl).elim
      · rfl
  have h₂ := parameters_runs base n d e w u lit v hcap rfl rfl rfl rfl rfl rfl
  refine ⟨_, ?_, h₁.followedBy h₂⟩
  have hw : w ≤ n := by
    change (UniversalMachine.programPrefix prog).length + (d + 4 + width d (2^e) w) ≤ n at fit
    rw [width_eq] at fit
    omega
  have hh := steps_le n d e w u hcap hu (InputBucketFromSize.bucket_le hq hpq hn) hw
  unfold clockCoefficient
  rw [Nat.add_mul]
  exact Nat.add_le_add (ht.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_left ..))))
    (hh.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) (le_max_right ..))))

end RAMTape.ProcessorPublic

end VPVNP
end Computability
end OAI
