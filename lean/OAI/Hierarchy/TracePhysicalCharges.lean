import OAI.Hierarchy.TraceReceiverPublishedWork
import OAI.Hierarchy.TraceRecordScale
import OAI.Hierarchy.TraceSeedCharge
import OAI.ThreeFlat.Diagonal.PhysicalPeakCharges

namespace OAI
/-! # The work scan and descriptor allocation on physical cursor histories -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Filter
open scoped Classical BigOperators Topology

variable {F : Type} [Field F] (B : PhysicalStage.Block F)

/-- Scheduled total for the actual binary shrink and refresh moves with the
cursor graph's initial energy and the uniform upper bound on one seed charge. -/
theorem cursor_scan_total (n rem low offsets slots M : ℕ)
    (hk : 2 ≤ (B.repeat n).charge+rem)
    (h : ((B.repeat n).run rem (B.cursorState hk low offsets slots)).plan.History)
    (start : (B.cursorState hk low offsets slots).Site → ℕ) (seed : ∀ v, start v ≤ M) :
    let A := B.cursorState hk low offsets slots
    let k := (B.repeat n).charge+rem
    let sites : ℝ := (k*2^k : ℕ)
    let width : ℝ := (2^low*(offsets*slots*3) : ℕ)
    let r := (B.repeat n).run rem A
    (r.rootTotal h (B.charges n rem A) start : ℝ) ≤
      sites*M + 2*(B.costFactors.sum : ℝ)*(((B.levels+1)*n+1 : ℕ) : ℝ)*
        (sites+Real.sqrt B.stageGrowth*
          (sites*(2^(B.exponent 0) : ℕ)*width + (4*Real.sqrt B.blockError+1)*sites)) := by
  intro A k sites width r
  have positions : (A.positions : ℝ) = sites := by
    dsimp only [A,sites,k]
    rw [B.cursorState_positions]
  have energy : Real.sqrt A.energy ≤ sites*(2^(B.exponent 0) : ℕ)*width :=
    B.cursorState_energy hk low offsets slots
  have budget : B.initialBudget ⟨A.energy,A.positions⟩ ≤
      sites*(2^(B.exponent 0) : ℕ)*width+(4*Real.sqrt B.blockError+1)*sites := by
    dsimp only [Block.initialBudget,Block.potential]
    rw [positions]
    linarith
  have initial : (∑ v,start v) ≤ A.positions*M := by
    simpa only [State.positions,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using
      (Finset.sum_le_sum (s:=Finset.univ) (fun v _ => seed v))
  have initial' : ((∑ v,start v : ℕ) : ℝ) ≤ sites*M := by
    rw [← positions, ← Nat.cast_mul]
    exact_mod_cast initial
  apply (B.scheduled_root_charge n rem A h start).trans
  apply add_le_add initial'
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add positions.le (mul_le_mul_of_nonneg_left budget (Real.sqrt_nonneg _))

/-- A fixed block contributes a fixed real coefficient to the work bound.
The only dependence on the number of repetitions is the factor n+1. -/
def scanRate : ℝ :=
  1+2*(B.costFactors.sum : ℝ)*(B.levels+2)*
    (1+Real.sqrt B.stageGrowth*((2^(B.exponent 0) : ℕ)+4*Real.sqrt B.blockError+1))

theorem cursor_scan_growth (n rem low offsets slots m : ℕ)
    (hk : 2 ≤ (B.repeat n).charge+rem) (hm : 1 ≤ m)
    (hwidth : 2^low*(offsets*slots*3) ≤ m)
    (h : ((B.repeat n).run rem (B.cursorState hk low offsets slots)).plan.History)
    (start : (B.cursorState hk low offsets slots).Site → ℕ) (seed : ∀ v, start v ≤ m) :
    let A := B.cursorState hk low offsets slots
    let k := (B.repeat n).charge+rem
    ((B.repeat n).run rem A).rootTotal h (B.charges n rem A) start ≤
      (k*2^k)*m*(n+1)*⌈scanRate B⌉₊ := by
  intro A k
  let p : ℝ := (k*2^k : ℕ)
  let d : ℝ := (2^(B.exponent 0) : ℕ)
  let e := 4*Real.sqrt B.blockError
  let g := Real.sqrt B.stageGrowth
  let K : ℝ := B.costFactors.sum
  let x : ℝ := (2^low*(offsets*slots*3) : ℕ)
  have hp : 0≤p := by dsimp [p]; positivity
  have hd : 0≤d := by dsimp [d]; positivity
  have he : 0≤e := by dsimp [e]; positivity
  have hg : 0≤g := Real.sqrt_nonneg _
  have hK : 0≤K := Nat.cast_nonneg _
  have one : 1≤(m:ℝ) := by exact_mod_cast hm
  have width : x ≤ m := Nat.cast_le.mpr hwidth
  have payload : p*d*x + (e+1)*p ≤ p*d*m + (e+1)*p*m :=
    add_le_add (by gcongr) (le_mul_of_one_le_right (by positivity) one)
  have positions : p ≤ p*m := le_mul_of_one_le_right hp one
  have inner : p+g*(p*d*x+(e+1)*p) ≤ p*m*(1+g*(d+e+1)) := by
    have h₁ := add_le_add positions (mul_le_mul_of_nonneg_left payload hg)
    convert h₁ using 1; ring
  have count : (((B.levels+1)*n+1 : ℕ) : ℝ) ≤ ((B.levels:ℝ)+2)*(n+1) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) B.levels,Nat.cast_nonneg (α:=ℝ) n]
  have first : p*m ≤ p*m*((n:ℝ)+1) :=
    le_mul_of_one_le_right (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have raw := cursor_scan_total B n rem low offsets slots m hk h start seed
  apply (Nat.cast_le (α:=ℝ)).mp
  change (((B.repeat n).run rem A).rootTotal h _ start : ℝ) ≤ _
  calc
    _ ≤ p*m + 2*K*(((B.levels+1)*n+1 : ℕ) : ℝ)*(p+g*(p*d*x+(e+1)*p)) := raw
    _ ≤ (p*m)*((n:ℝ)+1) +
        2*K*(((B.levels:ℝ)+2)*(n+1))*(p*m*(1+g*(d+e+1))) :=
      add_le_add first (by gcongr)
    _ = (p*m)*((n:ℝ)+1)*scanRate B := by dsimp only [scanRate,d,e,g,K]; ring
    _ ≤ p*m*((n:ℝ)+1)*(⌈scanRate B⌉₊ : ℕ) :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
    _ = _ := by dsimp only [p]; push_cast; ring

/-- With the actual high/low cursor split, the total root scan is linear in
the time cap times a fixed polynomial in the word width. -/
theorem cursor_scan_volume {u w n rem low offsets slots b a : ℕ}
    (hk : 2≤(B.repeat n).charge+rem) (ha : 0<a)
    (axes : (B.repeat n).charge+rem ≤ 2*(w+1)) (round : (B.repeat n).charge+rem+low ≤ u+1)
    (blocks : n≤w) (slot : offsets*slots*3 ≤ a*(w+1)^b)
    (h : ((B.repeat n).run rem (B.cursorState hk low offsets slots)).plan.History)
    (start : (B.cursorState hk low offsets slots).Site → ℕ)
    (seed : ∀ v, start v ≤ 2^low*(a*(w+1)^b)) :
    let A := B.cursorState hk low offsets slots
    ((B.repeat n).run rem A).rootTotal h (B.charges n rem A) start ≤
      2^u*(4*a*⌈scanRate B⌉₊)*(w+1)^(b+2) := by
  intro A
  let k := (B.repeat n).charge+rem
  have grow := cursor_scan_growth B n rem low offsets slots (2^low*(a*(w+1)^b)) hk
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.two_pow_pos low) (Nat.mul_pos ha (pow_pos (Nat.succ_pos w) b))))
    (Nat.mul_le_mul_left _ slot) h start seed
  have total : 2^k*2^low ≤ 2^u*2 := by
    rw [←pow_add,←pow_succ]
    exact Nat.pow_le_pow_right (by decide) round
  calc
    _ ≤ (k*2^k)*(2^low*(a*(w+1)^b))*(n+1)*⌈scanRate B⌉₊ := grow
    _ = (2^k*2^low)*k*(a*(w+1)^b)*(n+1)*⌈scanRate B⌉₊ := by ac_rfl
    _ ≤ (2^u*2)*(2*(w+1))*(a*(w+1)^b)*(w+1)*⌈scanRate B⌉₊ := by gcongr
    _ = _ := by rw [pow_add]; ring

/-- The maximum charge of the actual repeated block, including its native
polynomial tariff, fits in a single factor's work allowance. -/
theorem published_peak_room {u s : ℕ → ℕ} (scale : Scale u s)
    (a b rate degree : ℕ) (pos : 0<a) :
    ∀ᶠ w : ℕ in atTop, ∀ (rem low unitWork : ℕ)
        (A : State (2^(B.exponent 0)) ((B.repeat (s w)).charge+rem))
        (h : ((B.repeat (s w)).run rem A).plan.History) (start : A.Site → ℕ),
      low ≤ w/2 → unitWork ≤ rate*(w+1)^degree →
      A.maxWidth ≤ 2^low*(a*(w+1)^b) → (∀ z,start z ≤ 2^low*(a*(w+1)^b)) →
      ∀ v, publishedWork ((B.repeat (s w)).run rem A) h (B.charges (s w) rem A) start unitWork v ≤
        2^(3*w/5) := by
  filter_upwards [factor_room scale (rate*(3*a)) (degree+b) B.peakBase] with w room
  intro rem low unitWork A h start lowBound tariff widths seeds v
  let cap := 2^low*(a*(w+1)^b)
  have one : 1≤cap := Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos pos (Nat.pow_pos (Nat.succ_pos _)))
  have size : 1+A.maxWidth+cap ≤ 3*cap := by change A.maxWidth≤cap at widths; omega
  have peak := B.individual_terminal_charge (s w) rem A h start cap seeds v
  have lo : 2^low ≤ 2^(max (w/2) (u w-w/2)) :=
    Nat.pow_le_pow_right (by decide) (lowBound.trans (le_max_left ..))
  calc
    _ ≤ (rate*(w+1)^degree)*(B.peakBase^(s w)*(3*cap)) :=
      Nat.mul_le_mul tariff (peak.trans (Nat.mul_le_mul_left _ size))
    _ = (rate*(3*a))*(w+1)^(degree+b)*B.peakBase^(s w)*2^low := by
      dsimp only [cap]; rw [pow_add]; ac_rfl
    _ ≤ _ := (Nat.mul_le_mul_left _ lo).trans room

section Native
open Computability.VPVNP.BurstRAM PrivateRAM
variable [Fintype F] {w pc regs words S base d fuel : ℕ}
variable (M : Machine (64*w) pc regs words) (fit : NativeTrace.Fits M S base d fuel)
    (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w))
private abbrev chargeTable :=
  TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words d

private abbrev chargeDesc :=
  TraceSourceOwner.shape (64*w) pc regs words S fuel d (chargeTable M fit hF st).internal

/-- Each actual seed row may charge both incident arc banks, its clipped input
interval, and the compiled low-row bucket. Charging a full bucket at every
cursor covers idle relay positions as well. -/
theorem initial_charge {k : ℕ} (hk : 2≤k) (low : ℕ) (q : Fintype.card F≤64*w)
    (p : pc≤64*w) (r : regs≤64*w) (a : words≤64*w) (depth : d≤64*w)
    (v : (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells).Site) :
    let A := B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells
    1+A.incidentWidth v+2^low+TraceBitHeader.seedTraceWork low (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d ≤
      2^low*(((2*2^(B.exponent 0)+3)*seedRate B.cursorCopies)*(w+1)^15) := by
  intro A
  let cap := 2^low*(seedRate B.cursorCopies*(w+1)^15)
  have seed : TraceBitHeader.seedTraceWork low (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d ≤ cap :=
    native_seed_charge M fit hF st low B.cursorCopies q p r a depth
  have width : A.maxWidth ≤ cap := A.maxWidth_le fun e => by
    rw [B.cursorState_width]
    exact (seed_covers_arc low (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d).trans seed
  have incident := (A.incidentWidth_le v).trans (Nat.mul_le_mul_left _ width)
  have pairs : 2^low≤cap := Nat.le_mul_of_pos_right _
    (Nat.mul_pos (seedRate_pos _) (Nat.pow_pos (Nat.succ_pos _)))
  calc
    _ ≤ cap+(2*2^(B.exponent 0))*cap+cap+cap :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add ((Nat.succ_le_of_lt (Nat.two_pow_pos low)).trans pairs) incident) pairs) seed
    _ = _ := by dsimp only [cap]; ring

/-- Initial maximum width and price of the actual masked native cursor
rows. A relay pays only its incident arcs and its node. -/
theorem native_seed_bounds {k : ℕ} (hk : 2≤k) (low : ℕ) (q : Fintype.card F≤64*w)
    (p : pc≤64*w) (r : regs≤64*w) (a : words≤64*w) (depth : d≤64*w)
    (active : (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells).Site → Bool)
    (pairs : (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells).Site → ℕ) (clipped : ∀ v,pairs v≤2^low) :
    let A := B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells
    let cap := 2^low*(((2*2^(B.exponent 0)+3)*seedRate B.cursorCopies)*(w+1)^15)
    A.maxWidth ≤ cap ∧ ∀ v,1+(A.incidentWidth v+(if active v then
      pairs v+TraceBitHeader.seedTraceWork low (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d else 0))≤cap := by
  intro A cap
  constructor
  · apply A.maxWidth_le
    intro e
    rw [B.cursorState_width]
    have width := (seed_covers_arc low (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d).trans
      (native_seed_charge M fit hF st low B.cursorCopies q p r a depth)
    exact width.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by positivity))))
  · intro v
    have maxCharge := initial_charge B M fit hF st hk low q p r a depth v
    have paid := clipped v
    change 1+A.incidentWidth v+2^low+TraceBitHeader.seedTraceWork low (chargeDesc M fit hF st).stride
      (chargeTable M fit hF st).cells B.cursorCopies d ≤ cap at maxCharge
    cases active v <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- Scheduled weighted work on the fully instantiated native cursor, with
its clipped seed input bounded by the number of rows in its low bucket. -/
theorem native_scan_total {u n rem low : ℕ} (hk : 2≤(B.repeat n).charge+rem)
    (q : Fintype.card F≤64*w) (p : pc≤64*w) (r : regs≤64*w) (a : words≤64*w) (depth : d≤64*w)
    (axes : (B.repeat n).charge+rem ≤ 2*(w+1)) (round : (B.repeat n).charge+rem+low ≤ u+1)
    (blocks : n≤w)
    (h : ((B.repeat n).run rem (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells)).plan.History)
    (active : (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells).Site → Bool)
    (pairs : (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells).Site → ℕ) (clipped : ∀ v,pairs v≤2^low) :
    let A := B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells
    let R := (B.repeat n).run rem A
    R.rootTotal h (B.charges n rem A)
        (fun v => 1+(A.incidentWidth v + (if active v then
          pairs v+TraceBitHeader.seedTraceWork low (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d else 0))) ≤
      2^u*(4*((2*2^(B.exponent 0)+3)*seedRate B.cursorCopies)*⌈scanRate B⌉₊)*(w+1)^17 := by
  intro A R
  let c := (2*2^(B.exponent 0)+3)*seedRate B.cursorCopies
  have rate : seedRate B.cursorCopies ≤ c := Nat.le_mul_of_pos_left _ (by positivity)
  have slots : (1+(d+d))*(chargeTable M fit hF st).cells*3 ≤ c*(w+1)^15 := by
    have s := (seed_covers_arc 0 (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d).trans
      (native_seed_charge M fit hF st 0 B.cursorCopies q p r a depth)
    simpa only [pow_zero,one_mul] using s.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ rate))
  have positive : 0<c := Nat.mul_pos (Nat.succ_pos _) (seedRate_pos _)
  exact cursor_scan_volume B (u:=u) (w:=w) (n:=n) (rem:=rem) (low:=low)
    (offsets:=1+(d+d)) (slots:=(chargeTable M fit hF st).cells) (b:=15) (a:=c)
    hk positive axes round blocks slots h _
    (native_seed_bounds B M fit hF st hk low q p r a depth active pairs clipped).2

private theorem scale_volume (unit raw rate x degree base coefficient : ℕ)
    (tariff : unit ≤ rate*x^degree) (volume : raw ≤ base*coefficient*x^17) :
    unit*raw ≤ base*(rate*coefficient)*x^(degree+17) := by
  exact (Nat.mul_le_mul tariff volume).trans_eq (by rw [pow_add]; ac_rfl)


/-- The exact sum of the work words charged to all terminal sites on this
admitted history is linear in the time cap up to a fixed power of w. -/
theorem native_published_total {u n rem low : ℕ} (hk : 2≤(B.repeat n).charge+rem)
    (q : Fintype.card F≤64*w) (p : pc≤64*w) (r : regs≤64*w) (a : words≤64*w) (depth : d≤64*w)
    (axes : (B.repeat n).charge+rem ≤ 2*(w+1)) (round : (B.repeat n).charge+rem+low ≤ u+1)
    (blocks : n≤w)
    (h : ((B.repeat n).run rem (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells)).plan.History)
    (active : (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells).Site → Bool)
    (pairs : (B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells).Site → ℕ) (clipped : ∀ v,pairs v≤2^low)
    (unitWork rate degree : ℕ) (tariff : unitWork ≤ rate*(w+1)^degree) :
    let A := B.cursorState hk low (1+(d+d)) (chargeTable M fit hF st).cells
    let R := (B.repeat n).run rem A
    let start := fun v => 1+(A.incidentWidth v+(if active v then
      pairs v+TraceBitHeader.seedTraceWork low (chargeDesc M fit hF st).stride (chargeTable M fit hF st).cells B.cursorCopies d else 0))
    (∑ v, publishedWork R h (B.charges n rem A) start unitWork v) ≤
      2^u*(rate*(4*((2*2^(B.exponent 0)+3)*seedRate B.cursorCopies)*⌈scanRate B⌉₊))*(w+1)^(degree+17) := by
  intro A R start
  rw [publishedWork_sum]
  have paid := native_scan_total B M fit hF st hk q p r a depth axes round blocks h active pairs clipped
  exact scale_volume unitWork _ rate (w+1) degree (2^u) _ tariff paid

/-- The largest work word registered for an actual admitted native history. -/
theorem native_published_peak {u s : ℕ → ℕ} (scale : Scale u s) (rate degree : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words S base d fuel : ℕ}
      (M : Machine (64*w) pc regs words) (fit : NativeTrace.Fits M S base d fuel)
      (hF : Fintype.card F≤2^(64*w)) (st : Word (64*w)) (rem low : ℕ)
      (hk : 2≤(B.repeat (s w)).charge+rem) (_q : Fintype.card F≤64*w) (_p : pc≤64*w)
      (_r : regs≤64*w) (_a : words≤64*w) (_depth : d≤64*w),
      let grid :=  TraceStaticRow.gateTable hF fit.width fit.labels base fuel st regs words d
      let desc :=  TraceSourceOwner.shape (64*w) pc regs words S fuel d grid.internal
      let A := B.cursorState hk low (1+(d+d)) grid.cells
      let R := (B.repeat (s w)).run rem A
      ∀ (h : R.plan.History) (active : A.Site → Bool) (pairs : A.Site → ℕ) (unitWork : ℕ),
        low ≤ w/2 → unitWork ≤ rate*(w+1)^degree → (∀ v,pairs v≤2^low) →
        ∀ v, publishedWork R h (B.charges (s w) rem A)
          (fun x => 1+(A.incidentWidth x+(if active x then
            pairs x+TraceBitHeader.seedTraceWork low desc.stride grid.cells B.cursorCopies d else 0))) unitWork v ≤
          2^(3*w/5) := by
  have pos := seedRate_pos B.cursorCopies
  filter_upwards [published_peak_room B scale ((2*2^(B.exponent 0)+3)*seedRate B.cursorCopies)
    15 rate degree (by positivity)] with w room
  intro pc regs words S base d fuel M fit hF st rem low hk q p r a depth grid desc A R h active pairs unitWork lowBound tariff clipped v
  obtain ⟨width,seeds⟩ := native_seed_bounds B M fit hF st hk low q p r a depth active pairs clipped
  exact room rem low unitWork A h _ lowBound tariff width seeds v

end Native

/-- Number of bits in the chronological 64-word headers, retained heap arrays,
and selected histogram counts laid out in the actual fixed-size word format. -/
def descriptorBits (n rem base alphabet wordBits : ℕ) : ℕ :=
  let P := B.repeat n
  let dir := P.directory rem base
  wordBits*(64*P.length + (dir.map NavigationDirectory.Stage.heapWords).sum +
    alphabet*(dir.map NavigationDirectory.Stage.motifs).sum)

private theorem programLength {a : ℕ} (P : PhysicalStage.Program F a) :
    P.length = (P.effects shrinkError).length := by
  induction P <;> simp_all only [Program.length,Program.effects,List.length_nil,List.length_cons]

theorem repeated_stages (n : ℕ) : (B.repeat n).length=(B.levels+1)*n :=
  (programLength (B.repeat n)).trans (B.repeat_effects_length n)

theorem descriptorBits_le (n rem base alphabet W : ℕ) :
    descriptorBits B n rem base alphabet W ≤
      W*((B.levels+1)*n)*(64+B.allocations.sum+alphabet*B.costFactors.sum)*
        (1+base*2^((B.repeat n).charge+rem)) := by
  let P := B.repeat n
  let area := base*2^(P.charge+rem)
  let len := (B.levels+1)*n
  have length : P.length = len := repeated_stages B n
  have heap := P.allocation_words B.allocations.sum (B.allocation_bound n) rem base
  have hist := P.histogram_rows B.costFactors.sum (B.factor_bound n) rem base
  change _ ≤ P.length*_*(1+area) at heap
  change _ ≤ P.length*_*area at hist
  rw [length] at heap hist
  have header : 64*len ≤ 64*len*(1+area) := Nat.le_mul_of_pos_right _ (by omega)
  have history := hist.trans (Nat.mul_le_mul_left _ (Nat.le_add_left area 1))
  change W*(64*P.length + _ + alphabet*_) ≤ _
  rw [length]
  calc
    _ ≤ W*(64*len*(1+area) + len*B.allocations.sum*(1+area) +
      alphabet*(len*B.costFactors.sum*(1+area))) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.add_le_add header heap) (Nat.mul_le_mul_left _ history))
    _ = _ := by dsimp only [len,area,P]; ring

/-- The history and all retained numerical heap fields fit at the paper's
three-fifths volume cap, including the word factor for binary width counters. -/
theorem descriptor_room {u s : ℕ → ℕ} (scale : Scale u s) (alphabet wordFactor : ℕ) :
    ∀ᶠ w : ℕ in Filter.atTop, ∀ rem : ℕ,
      (B.repeat (s w)).charge+rem = u w+1-w/2 →
      descriptorBits B (s w) rem ((B.repeat (s w)).charge+rem) alphabet (wordFactor*(w+1))
        ≤ 2^(3*w/5) := by
  let fixed := 64+B.allocations.sum+alphabet*B.costFactors.sum
  let C := wordFactor*(B.levels+1)*fixed
  filter_upwards [TraceAdmission.record_room scale C] with w room
  intro rem split
  let k := (B.repeat (s w)).charge+rem
  calc
    _ ≤ _ := descriptorBits_le B (s w) rem k alphabet (wordFactor*(w+1))
    _ = C*s w*(1+k*2^k)*(w+1) := by dsimp only [C,fixed,k]; ring
    _ ≤ C*(s w+1)*(1+k*2^k)*(64*w+1) := by gcongr <;> omega
    _ ≤ _ := by simpa only [k,split] using room

end Hierarchy.TraceDistribution.Physical

end
end OAI
