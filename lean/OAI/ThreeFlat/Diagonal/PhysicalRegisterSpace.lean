import OAI.ThreeFlat.Diagonal.FoldPhysicalClock
import OAI.ThreeFlat.Diagonal.TraceCursorOrdinals
import OAI.ThreeFlat.Diagonal.TraceSeedWork
import OAI.ThreeFlat.Diagonal.TickProgramRegister
import OAI.ThreeFlat.Diagonal.PhysicalRunCharges
import OAI.ThreeFlat.Diagonal.DefectBudget

namespace OAI
/-! # The complete shared register fits on every physical cursor history -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F]

private theorem gap {u : ℕ} (hu : 16≤u) (n : ℕ) : 16*u^n≤u^(n+2) := by
  rw [pow_add]
  have h : 16≤u^2 := hu.trans (Nat.le_self_pow (by decide) _)
  simpa only [Nat.mul_comm 16] using Nat.mul_le_mul_left (u^n) h

/-- The two distinct factors in the paper's register bound: the graph has one physical
site per bucket and cursor, while the final wire mass has lost one power of two per block. -/
theorem register_exponents {u k low e : ℕ} (hu : 16≤u) (he : e≤u)
    (halves : low=u^10/2) (depth : k+low≤u^10+2*u^6) :
    8*(u^e*2^k)≤2^(u^10-u^4) ∧
      8*(u^e*2^(k+low))≤2^(u^10-u^4)*2^(u^8) := by
  have a : 16*u^2≤u^4 := gap hu 2
  have b : 16*u^4≤u^6 := gap hu 4
  have c : 16*u^6≤u^8 := gap hu 6
  have d : 16*u^8≤u^10 := gap hu 8
  have hp : 1≤u^2 := Nat.pow_pos (by omega)
  have poly := width_pow_le_two_pow_sq he
  constructor
  · calc
      8*(u^e*2^k) ≤ 2^3*(2^(u^2)*2^k) := by gcongr; decide
      _ = 2^(3+u^2+k) := by rw [pow_add,pow_add]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  · calc
      8*(u^e*2^(k+low)) ≤ 2^3*(2^(u^2)*2^(k+low)) := by gcongr; decide
      _ = 2^(3+u^2+(k+low)) := by rw [pow_add,pow_add]; ring
      _ ≤ 2^((u^10-u^4)+u^8) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := pow_add ..

theorem program_length {s : ℕ} (P : Program F s) :
    P.length=(P.effects shrinkError).length := by
  induction P <;> simp_all only [Program.length,Program.effects,List.length_nil,List.length_cons]

namespace Block
variable (B : Block F)

/-- Every stage retains its output graph, widths, choices, descriptors and owner arrays.
Even all these disjoint allocations together fit within one eighth of one AUX register. -/
theorem cursor_heap_space {u rem low : ℕ} (hu : 40≤u)
    (levels : B.levels+1≤u) (factor : B.allocations.sum≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6) :
    let k := (B.repeat (u^8)).charge+rem
    8*((((B.repeat (u^8)).directory rem k).map NavigationDirectory.Stage.heapWords).sum)≤2^(u^10-u^4) := by
  intro k
  have high : k≤u^11 := by
    have a : 16*u^6≤u^8 := gap (by omega : 16≤u) 6
    have b : 16*u^8≤u^10 := gap (by omega : 16≤u) 8
    have m := Nat.mul_le_mul_left (u^10) (by omega : 3≤u)
    dsimp [k]
    rw [pow_succ u 10]
    omega
  have basis : 1+k*2^k≤u^12*2^k := by
    calc
      _ ≤ (1+u^11)*2^k := by
        rw [Nat.add_mul 1 (u^11) (2^k),Nat.one_mul]
        exact Nat.add_le_add (Nat.two_pow_pos k) (Nat.mul_le_mul_right _ high)
      _ ≤ _ := by
        apply Nat.mul_le_mul_right
        rw [pow_succ u 11]
        have h := Nat.mul_le_mul_left (u^11) (by omega : 2≤u)
        have hp : 0<u^11 := Nat.pow_pos (by omega)
        omega
  have bound := (B.repeat (u^8)).allocation_words B.allocations.sum (B.allocation_bound _) rem k
  rw [program_length,B.repeat_effects_length] at bound
  have b : (((B.repeat (u^8)).directory rem k).map NavigationDirectory.Stage.heapWords).sum ≤ u^22*2^k := by
    calc
      _ ≤ ((B.levels+1)*u^8)*B.allocations.sum*(1+k*2^k) := bound
      _ ≤ ((u*u^8)*u)*(u^12*2^k) := by gcongr
      _ = _ := by ring
  exact (Nat.mul_le_mul_left 8 b).trans ((register_exponents (by omega : 16≤u) (by omega : 22≤u) half depth).1)

/-- Charge assigned by the native two-word row writer to each original cursor site.
Only the first cursor has a real trace forest and external endpoint requests. -/
def seedWork {k : ℕ} (hk : 2≤k) (low off slots total copies depth stride cells : ℕ)
    (v : (B.cursorState hk low off slots).Site) :=
  let row := B.cursorOrdinal hk low off slots v.1 v.2
  1+((B.cursorState hk low off slots).incidentWidth v+
    (if row<2^k then min (total-row*2^low) (2^low)+
      TraceBitHeader.seedTraceWork low stride cells copies depth else 0))

/-- Actual external pairs present at the original cursor after masking inactive rows. -/
def clippedPairs {k : ℕ} (hk : 2≤k) (low off slots total : ℕ)
    (v : (B.cursorState hk low off slots).Site) :=
  let row := B.cursorOrdinal hk low off slots v.1 v.2
  if row<2^k then min (total-row*2^low) (2^low) else 0

theorem seedWork_covers {k : ℕ} (hk : 2≤k) (low off slots total copies depth stride cells : ℕ)
    (v : (B.cursorState hk low off slots).Site) :
    1+(B.cursorState hk low off slots).incidentWidth v+B.clippedPairs hk low off slots total v ≤
      B.seedWork hk low off slots total copies depth stride cells v := by
  by_cases ha : B.cursorOrdinal hk low off slots v.1 v.2 < 2^k <;>
    simp only [seedWork,clippedPairs,ha,ite_true,ite_false] <;> omega

theorem cursor_start_le {u k low off slots total copies depth stride cells e : ℕ} (hu : 4≤u)
    (hk : 2≤k) (degree : 2^(B.exponent 0)≤u) (slot : off*slots*3≤u^e)
    (traceCost : TraceBitHeader.seedTraceWork low stride cells copies depth≤2^low*u^e)
    (v : (B.cursorState hk low off slots).Site) :
    B.seedWork hk low off slots total copies depth stride cells v≤2^low*u^(e+2) := by
  let A := B.cursorState hk low off slots
  let bucket := 2^low*u^e
  have width : A.maxWidth≤bucket := A.maxWidth_le (fun j=>by
    rw [B.cursorState_width]; exact Nat.mul_le_mul_left _ slot)
  have inc := (A.incidentWidth_le v).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 2 degree) width)
  have baseline : 2^low≤bucket := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  have positive : 1≤bucket := (Nat.two_pow_pos low).trans_le baseline
  have square : 2*u+3≤u^2 := by nlinarith [Nat.mul_le_mul_left u hu]
  change 1+(A.incidentWidth v+(if _ then _ else _))≤_
  have met : ∀ p : Prop, [Decidable p] → ∀ a : ℕ,
      (if p then min a (2^low)+TraceBitHeader.seedTraceWork low stride cells copies depth else 0)≤2*bucket := by
    intro p inst a
    split_ifs
    · have := (Nat.min_le_right a (2^low)).trans baseline
      change TraceBitHeader.seedTraceWork low stride cells copies depth≤bucket at traceCost
      omega
    · omega
  calc
    _ ≤ (2*u+3)*bucket := by
      have h := met ((B.cursorOrdinal hk low off slots v.1 v.2)<2^k) (total-(B.cursorOrdinal hk low off slots v.1 v.2)*2^low)
      nlinarith only [inc,h,positive]
    _ ≤ u^2*bucket := Nat.mul_le_mul_right _ square
    _ = _ := by unfold bucket; rw [pow_add]; ring

/-- Total scheduler work on the concrete H trace. Every root receives the same native
work tariff; this is the sum of the work column eventually published to S11. -/
theorem cursor_total_work {u rem low off slots total copies depth stride cells e unitWork Aexp : ℕ}
    (hu : 40≤u) (hk : 2≤(B.repeat (u^8)).charge+rem)
    (axes : (B.repeat (u^8)).charge+rem≤u^11)
    (degree : 2^(B.exponent 0)≤u) (slot : off*slots*3≤u^e)
    (traceCost : TraceBitHeader.seedTraceWork low stride cells copies depth≤2^low*u^e)
    (level : B.levels+1≤u) (coeff : B.costFactors.sum≤u)
    (energy : 4*Real.sqrt B.blockError≤(u:ℝ)) (growth : Real.sqrt B.stageGrowth≤(u:ℝ))
    (tariff : unitWork≤u^e) (enough : 146+2*e+26≤Aexp)
    (clock : 2^((B.repeat (u^8)).charge+rem+low)≤2*FoldTrace.hFuel u Aexp)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History) :
    let _k := (B.repeat (u^8)).charge+rem
    let A := B.cursorState hk low off slots
    let r := (B.repeat (u^8)).run rem A
    let initial := B.seedWork hk low off slots total copies depth stride cells
    r.rootTotal h (r.scaled unitWork (B.charges (u^8) rem A)) (fun v=>unitWork*initial v)
      ≤ FoldTrace.total u/u^(Aexp-(146+2*e+26)) := by
  intro k A r initial
  let P := k*2^k
  let b := 2^low*u^e
  have pos : 0<u := by omega
  have bpos : 1≤b := Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos pos)
  have ub : (1:ℕ)≤u^8 := Nat.pow_pos pos
  have hp : A.positions=P := B.cursorState_positions hk low off slots
  have start : (∑ v,initial v) ≤ P*(b*u^2) := by
    have cap (v) : initial v≤b*u^2 := by
      simpa only [b,pow_add,Nat.mul_assoc] using
        B.cursor_start_le (by omega : 4≤u) hk degree slot traceCost v
    calc
      _ ≤ ∑ _v : A.Site,b*u^2 := Finset.sum_le_sum (fun v _=>cap v)
      _ = A.positions*(b*u^2) := by simp [State.positions]
      _ = _ := by rw [hp]
  have init : B.initialBudget ⟨A.energy,A.positions⟩ ≤ (P*u*b+(u+1)*P : ℕ) := by
    have z := B.cursorState_energy hk low off slots
    have small : 2^low*(off*slots*3)≤b := Nat.mul_le_mul_left _ slot
    change Real.sqrt A.energy≤(P:ℝ)*(2^B.exponent 0:ℕ)*(2^low*(off*slots*3):ℕ) at z
    have z' : Real.sqrt A.energy≤((P*u*b:ℕ):ℝ) := z.trans (by push_cast; gcongr <;> exact_mod_cast ‹_›)
    dsimp only [initialBudget,potential]
    rw [hp]
    push_cast
    have mu := mul_le_mul_of_nonneg_right energy (Nat.cast_nonneg P)
    push_cast at z'
    linarith only [z',mu]
  have ceiling := B.scheduled_root_charge (u^8) rem A h initial
  change (r.rootTotal h _ initial : ℝ)≤_ at ceiling
  have numeric : r.rootTotal h (B.charges (u^8) rem A) initial≤
      P*(b*u^2)+2*u*((u*u^8)+1)*(P+u*(P*u*b+(u+1)*P)) := by
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [hp] at ceiling
    let budget := B.initialBudget ⟨A.energy,(P:ℝ)⟩
    have nonneg : 0≤budget := B.initialBudget_nonneg _ ⟨A.energy_nonneg,Nat.cast_nonneg P⟩
    have bounded : budget≤((P*u*b+(u+1)*P:ℕ):ℝ) := by simpa only [hp,budget] using init
    have count : 2*(B.costFactors.sum:ℝ)*(((B.levels+1)*u^8+1:ℕ):ℝ) ≤ ((2*u*(u*u^8+1):ℕ):ℝ) := by
      exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul_left 2 coeff) (Nat.add_le_add_right (Nat.mul_le_mul_right _ level) 1)
    have aggregate : (P:ℝ)+Real.sqrt B.stageGrowth*budget≤((P+u*(P*u*b+(u+1)*P):ℕ):ℝ) := by
      rw [Nat.cast_add, Nat.cast_mul u]
      exact add_le_add (le_refl (P:ℝ)) (mul_le_mul growth bounded nonneg (Nat.cast_nonneg u))
    have sumBound : ((∑ v,initial v:ℕ):ℝ)≤((P*(b*u^2):ℕ):ℝ) :=by exact_mod_cast start
    calc
      _ ≤ _ := ceiling
      _ ≤ _ := add_le_add sumBound (mul_le_mul count aggregate
        (add_nonneg (Nat.cast_nonneg P) (mul_nonneg (Real.sqrt_nonneg _) nonneg)) (Nat.cast_nonneg _))
      _ = _ := by push_cast;ring
  have inner : P*u*b+(u+1)*P≤3*u*P*b := by
    have t := Nat.mul_le_mul_left ((u+1)*P) bpos
    have z := Nat.mul_le_mul_right (P*b) (by omega : 1≤u)
    nlinarith only [t,z]
  have outer : P+u*(P*u*b+(u+1)*P)≤4*u^2*P*b := by
    have x := Nat.mul_le_mul_left u inner
    have q : 1≤u^2*b := Nat.mul_pos (Nat.pow_pos pos) bpos
    have y := Nat.mul_le_mul_left P q
    nlinarith only [x,y]
  have stages : u*u^8+1 ≤ 2*u^9 := by
    have q : u*u^8=u^9 := by ring
    have q' : 1≤u^9 := Nat.pow_pos pos
    omega
  have marginal : 17*u^12≤u^14 := by
    rw [show 14=12+2 by decide,pow_add]
    have q : 17≤u^2 := (by omega : 17≤u).trans (Nat.le_self_pow (by decide) _)
    simpa only [Nat.mul_comm 17] using Nat.mul_le_mul_left (u^12) q
  have cell : P*(b*u^2)≤P*b*u^12 := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (P*b) (Nat.pow_le_pow_right pos (by decide : 2≤12))
  have major :
      r.rootTotal h (B.charges (u^8) rem A) initial ≤ P*b*u^14 := calc
    _ ≤ P*b*u^12+2*u*(2*u^9)*(4*u^2*P*b) := numeric.trans
      (Nat.add_le_add cell (Nat.mul_le_mul (Nat.mul_le_mul_left _ stages) outer))
    _ = (P*b)*(17*u^12) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ marginal
  rw [Run.rootTotal_scaled]
  calc
    _ ≤ u^e*((u^11*2^k)*(2^low*u^e)*u^14) :=
      Nat.mul_le_mul tariff (major.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ axes))))
    _ = 2^(k+low)*u^(2*e+25) := by rw [show 2*e+25=e+e+25 by omega,pow_add,pow_add,pow_add]; ring
    _ ≤ (2*FoldTrace.hFuel u Aexp)*u^(2*e+25) := Nat.mul_le_mul_right _ clock
    _ ≤ FoldTrace.hFuel u Aexp*u^(2*e+26) := by
      calc
        _ = (FoldTrace.hFuel u Aexp*u^(2*e+25))*2 := by ring
        _ ≤ (FoldTrace.hFuel u Aexp*u^(2*e+25))*u := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by rw [show 2*e+26=(2*e+25)+1 by omega,pow_succ u (2*e+25),Nat.mul_assoc]
    _ ≤ _ := by
      apply (Nat.le_div_iff_mul_le (Nat.pow_pos pos)).mpr
      rw [Nat.mul_assoc,←pow_add,show 2*e+26+(Aexp-(146+2*e+26))=Aexp-146 by omega]
      exact Nat.div_mul_le_self _ _

theorem cursor_histogram_space {u K rem low : ℕ} (hu : 40≤u) (alphabet : K≤u)
    (levels : B.levels+1≤u) (factor : B.costFactors.sum≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6) :
    let k := (B.repeat (u^8)).charge+rem
    let rows := (((B.repeat (u^8)).directory rem k).map NavigationDirectory.Stage.motifs).sum
    8*(rows*K*(16*u^10))≤2^(u^10-u^4) := by
  intro k rows
  have positive : 0<u := by omega
  have slots : k≤u^11 := by
    have small : u^6≤u^10 := Nat.pow_le_pow_right (by omega) (by decide : 6≤10)
    calc
      k ≤ u^10+2*u^6 := by dsimp only [k]; omega
      _ ≤ u^10*3 := by omega
      _ ≤ u^10*u := Nat.mul_le_mul_left _ (by omega)
      _ = u^11 := (pow_succ u 10).symm
  have h := (B.repeat (u^8)).histogram_rows B.costFactors.sum (B.factor_bound _) rem k
  rw [program_length,B.repeat_effects_length] at h
  have total : rows*K*(16*u^10)≤u^33*2^k := by
    calc
      _ ≤ (((B.levels+1)*u^8)*B.costFactors.sum*(k*2^k))*K*(16*u^10) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h)
      _ ≤ ((u*u^8)*u*(u^11*2^k))*u*(u*u^10) := by gcongr; omega
      _ = _ := by ring
  exact (Nat.mul_le_mul_left 8 total).trans
    ((register_exponents (by omega : 16≤u) (by omega : 33≤u) half depth).1)

/-- Final-wire shrinkage is applied to the concrete final state on the same history as
the histogram rows, including the varying occupied width of every selected trace edge. -/
theorem cursor_terminal_space {u rem low off slots e : ℕ} (hu : e+40≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (hk : 2≤(B.repeat (u^8)).charge+rem) (degree : 2^(B.exponent 0)≤u)
    (error : 4*Real.sqrt B.blockError≤(u:ℝ)) (slot : off*slots*3≤u^e)
    (h : ((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).plan.History) :
    8*(((B.repeat (u^8)).run rem (B.cursorState hk low off slots)).terminalLayer h).state.widthSum ≤
      2^(u^10-u^4) := by
  let k := (B.repeat (u^8)).charge+rem
  let r := (B.repeat (u^8)).run rem (B.cursorState hk low off slots)
  let w := r.readTerminal (fun x=>x.widthSum) h
  have kb : k≤u^11 := by
    have small : u^6≤u^10 := Nat.pow_le_pow_right (by omega) (by decide : 6≤10)
    calc
      k ≤ u^10+2*u^6 := by dsimp only [k]; omega
      _ ≤ u^10*3 := by omega
      _ ≤ u^10*u := Nat.mul_le_mul_left _ (by omega)
      _ = u^11 := (pow_succ u 10).symm
  have hb := (B.cursor_history_widths (u^8) rem low off slots hk h).2
  have sites_nonneg : (0:ℝ) ≤ ((k*2^k:ℕ):ℝ) := Nat.cast_nonneg _
  have realBound : (w:ℝ)*(2:ℝ)^(u^8) ≤ (k*2^k:ℕ)*(2^B.exponent 0:ℕ)*(2^low*(off*slots*3):ℕ)
      +(u:ℝ)*(k*2^k:ℕ) :=
    ((le_div_iff₀ (by positivity)).mp hb).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right error sites_nonneg))
  have natBound : w*2^(u^8)≤(k*2^k)*2^B.exponent 0*(2^low*(off*slots*3))+u*(k*2^k) := by
    exact_mod_cast realBound
  have dominate : w*2^(u^8) ≤ u^(e+14)*2^(k+low) := by
    have positive : 0<u := by omega
    have unit : 1≤u^e := Nat.pow_pos positive
    have bucket : 1≤2^low := Nat.two_pow_pos _
    calc
      _ ≤ (u^11*2^k)*u*(2^low*u^e)+u*(u^11*2^k) := natBound.trans (by gcongr)
      _ ≤ (2*u^12*u^e)*2^(k+low) := by
        have extra := Nat.mul_le_mul (Nat.mul_le_mul_left (u*(u^11*2^k)) bucket) unit
        simp only [Nat.mul_one] at extra
        calc
          _ ≤ (u^11*2^k)*u*(2^low*u^e)+(u*(u^11*2^k)*2^low*u^e) :=
            Nat.add_le_add le_rfl extra
          _ = _ := by rw [pow_add 2 k low]; ring
      _ ≤ _ := by
        apply Nat.mul_le_mul_right
        rw [pow_add]
        have g := gap (by omega : 16≤u) 12
        have g' : 2*u^12≤u^14 := (Nat.mul_le_mul_right _ (by decide : 2≤16)).trans g
        simpa only [Nat.mul_comm (u^e)] using Nat.mul_le_mul_right (u^e) g'
  have complete := (Nat.mul_le_mul_left 8 dominate).trans
    (register_exponents (by omega : 16≤u) (by omega : e+14≤u) half depth).2
  rw [Run.terminalLayer_width]
  change 8*w≤_
  apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos (u^8))
  simpa only [Nat.mul_assoc] using complete

theorem cursor_repeat_word {u rem low off slots e : ℕ} (hu : e+40≤u) (lowBound : low≤u^10)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) (slot : off*slots*3≤u^e)
    (hk : 2≤(B.repeat (u^8)).charge+rem) :
    B.repeatFactor*(((B.cursorState hk low off slots).maxWidth+1)*B.widthBase^(u^8))<2^(16*u^10) := by
  have pos : 0<u := by omega
  have width : (B.cursorState hk low off slots).maxWidth ≤ 2^low*u^e :=
    (B.cursorState hk low off slots).maxWidth_le fun j=>by
      rw [B.cursorState_width]; exact Nat.mul_le_mul_left _ slot
  have poly := width_pow_le_two_pow_sq (by omega : e≤u)
  have bit : 2^low*u^e ≤ 2^(low+u^2) := by rw [pow_add]; gcongr
  have one : 1≤2^(low+u^2) := Nat.two_pow_pos _
  have up := Nat.le_of_lt (Nat.lt_two_pow_self (n:=u))
  have rep : B.widthBase^(u^8) ≤ 2^(u^9) := by
    calc
      _ ≤ (2^u)^(u^8) := Nat.pow_le_pow_left (growth.trans up) _
      _ = 2^(u^9) := by rw [←pow_mul,pow_succ u 8,Nat.mul_comm u]
  have m1 : u≤u^10 := Nat.le_self_pow (by decide) _
  have m2 := Nat.pow_le_pow_right pos (by decide : 2≤10)
  have m9 := Nat.pow_le_pow_right pos (by decide : 9≤10)
  calc
    _ ≤ 2^u*((2^(low+u^2+1))*2^(u^9)) := by
      apply Nat.mul_le_mul (factor.trans up)
      apply Nat.mul_le_mul _ rep
      calc
        _ ≤ 2^(low+u^2)+1 := Nat.add_le_add_right (width.trans bit) _
        _ ≤ 2^(low+u^2)*2 := by omega
        _ = _ := (pow_succ 2 (low+u^2)).symm
    _ = 2^(u+(low+u^2+1+u^9)) := by
      rw [pow_add 2 u (low+u^2+1+u^9),pow_add 2 (low+u^2+1) (u^9)]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

/-- The same fixed choice of K and of the allocated half-AUX interval works on every
terminal branch, including ones with no live terminal width at all. -/
def cursorRegister {u rem low off slots e : ℕ} (hu : e+40≤u)
    (half : low=u^10/2) (depth : (B.repeat (u^8)).charge+rem+low≤u^10+2*u^6)
    (hk : 2≤(B.repeat (u^8)).charge+rem) (degree : 2^(B.exponent 0)≤u)
    (error : 4*Real.sqrt B.blockError≤(u:ℝ)) (slot : off*slots*3≤u^e)
    (alphabet : B.alphabetCap≤u) (levels : B.levels+1≤u) (score : B.costFactors.sum≤u)
    (growth : B.widthBase≤u) (factor : B.repeatFactor≤u) :
    let A := B.cursorState hk low off slots
    let Q := B.recordTable B.alphabetCap (16*u^10) (u^8) rem A le_rfl
      (B.cursor_repeat_word hu (by omega) growth factor slot hk)
    let r := (B.repeat (u^8)).run rem A
    TickAuxiliary.GroupRegister r.plan Q.codes (fun h => (r.terminalLayer h).state.widthSum) (2^(u^10-u^4)) := by
  intro A Q r
  exact Q.groupRegister (a:=2^(u^10-u^4)) (capacity:=2^(u^10-u^4)/2)
    (by have := Nat.two_pow_pos (u^10-u^4); omega)
    (fun h=>by
      have count := B.cursor_histogram_space (by omega : 40≤u) alphabet levels score half depth
      have fin := B.cursor_terminal_space hu half depth hk degree error slot h
      have cardinal : Fintype.card A.Base=(B.repeat (u^8)).charge+rem := Fintype.card_fin _
      have fits {x y room : ℕ} (rows : 8*x≤room) (terminal : 8*y≤room) : x+y≤room/2 := by omega
      rw [cardinal]
      exact fits count fin)

end Block

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
