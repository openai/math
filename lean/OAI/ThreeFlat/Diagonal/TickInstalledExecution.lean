import OAI.ThreeFlat.Diagonal.TickAgeTrace
import OAI.ThreeFlat.RAM.TickRejectedRun
import OAI.ThreeFlat.Diagonal.TickMountedBudget
import OAI.ThreeFlat.Diagonal.TraceStartupAtScale
import OAI.ThreeFlat.RAM.SharedTickPrelude
import OAI.ThreeFlat.RAM.TickHeaderShift

namespace OAI
/-! # Tensor of the installed, fixed-size native tick at a dyadic age -/

noncomputable section
namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM ApproximateImage RAM RAM.ContinuationLink
open RAM.TickMachine RAM.TickActiveROM RAM.Contraction RAM.BitLayout RAM.TickMountedPins
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] {u H J e np sp nr sr nk sk nt ns pk teams capacity : ℕ}
local notation "w" => (16*u^10)
local notation "q" => (2^(u^3))
local notation "a" => (2^(u^10-u^4))
local notation "B" => TickPhysicalABI.mounted u a teams capacity q nt ns pk
local notation "p" => pinCount q nt ns pk a

theorem eval_installed_procedures (age : TraceVolume.cm ≤ u) (hF : Fintype.card F ≤ 2^w)
    (cl : TickChronology.Clock) (fit : Fits (TickWeightedBank.shape F p H J) w)
    (nav : Block w np nr nk) (prep : Block w sp sr sk) (nd : Fin nk → Word w) (sd : Fin sk → Word w)
    (big : textCutoff F np sp nr sr nk sk ≤ u) (x : CellInput B cl fit)
    (tail : Fin q → Bool) (params : Fin pk → Bool) (oa na oc nc : Fin a → Bool)
    (team step navTime prepTime : ℕ) (st : Word w)
    (ft : team < 2^nt) (fs : step < 2^ns) (wt : team < 2^w) (ws : step < 2^w)
    (dur : cl.groupDuration < 2^w) (last : cl.last < 2^w) (begin : cl.beginTick < 2^w)
    (room : 2+p+a < 2^w) (space : WordBounds B fit) (he : e ≤ u) (param : 2+nt+ns+pk ≤ u^e)
    (pre admitted slotInput : Memory w → Prop) :
    let d := TraceVolume.depth u
    let text := linkedProgram B cl fit nav prep nd sd big q nt ns
    let limits := linkedProgram_fits B cl fit big
    let D := installProgram (CapacityPadding.pad text limits.1 (Nat.le_refl u) limits.2) tail
    let ph := cl.phase step
    let pin := fields D (digits team nt) (digits step ns) params oa na oc nc
    let start := TickNavigationEntry.input B cl team step (TickMountedPins.memory pin : Memory w)
    let field := codec (TickWeightedBank.shape F p H J) fit
    let budget := (159+6*(nt+ns)+25+18*a)+(1470+navTime+21+x.tail prepTime)
    let hu : 128 ≤ u := by dsimp [TraceVolume.cm] at age; omega
    let hw : 3 ≤ w+1 := by have := Nat.le_self_pow (by decide : 10≠0) u; omega
    let bounds := CapacityPadding.textFits_scale hu
    let pc : u ≤ 2^(w+1) := bounds.registers.trans (Nat.pow_le_pow_right (by decide) (by omega))
    let hs : 2+p ≤ 2^w := (Nat.le_add_right (2+p) a).trans (Nat.le_of_lt room)
    let hf : 2^d ≤ 2^(w+1) := (TraceVolume.tick_grid age he param).2.1
    TickStageSpec.Admission field nav nd pre admitted (fun _ out => NavOutput x ph oa na oc nc slotInput out) navTime →
    pre start → TickStageSpec.Prepare prep sd slotInput
      (fun _ out => TickWeightedBank.Ready fit x.net x.lib pin (B).metadata (B).lut out) prepTime →
    budget ≤ TraceVolume.cap u/2 →
    (network hF hw pc 2 st hs hf u u d).eval (advicePins 2 D (raw pin)) =
      if TickAuxiliary.branch x.aux ph oa na then
        if admitted start then x.weight ph oa na oc nc pin else 0
      else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0 := by
  intro d text limits D ph pin start field budget hu hw bounds pc hs hf admission initial ready duration
  apply eval_age_returns age hF text limits.1 (Nat.le_refl _) limits.2 tail team step params
    oa na oc nc st he param duration
  exact linked_execution cl fit nav prep nd sd big x D params oa na oc nc team step navTime prepTime
    ft fs wt ws dur last begin room space pre admitted slotInput admission initial ready


end ThreeFlat.Diagonal.TraceBitHeader

namespace ThreeFlat.Diagonal.TraceStartupAtScale

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory ApproximateImage RAM ContinuationLink TickMachine
open TickActiveROM Contraction BitLayout TickMountedPins TickFuel
open scoped Classical Fin.CommRing

variable {F : Type} [Fintype F] [Field F] {u e nt ns pk np sp nr sr nk sk H J teams capacity : ℕ}

local notation "W" => (16*u^10)
local notation "Q" => (2^(u^3))
local notation "A" => (2^(u^10-u^4))
local notation "PINS" => pinCount Q nt ns pk A
local notation "B" => TickPhysicalABI.mounted u A teams capacity Q nt ns pk

/-- Both presentations count just the replaceable strings and the single public advice block. -/
theorem fields_size (q nt ns pk a : ℕ) : (4*a+(nt+ns+pk))+q=pinCount q nt ns pk a := by
  unfold pinCount
  omega

/-- Casting the arity of the actual trace network preserves its tensor in numeric pin order. -/
theorem eval_cast_arity {K : Type*} [CommSemiring K] {n m : ℕ} (h : n=m)
    (N : BitNetwork K n) (pin : Fin m → Bool) :
    (cast (congrArg (BitNetwork K) h) N).eval pin = N.eval (fun i => pin (i.cast h)) := by
  subst m
  rfl

private def unshifted {n : ℕ} (pin : Fin n → Bool) (i : ℕ) :=
  if h : i<n then pin ⟨i,h⟩ else false

private theorem startup_on_fields {pc r k : ℕ} (hu : cutoff≤u) (hq : Fintype.card F≤u)
    (he : e≤u) (hparams : nt+ns+pk≤u^e)
    (M : Machine W pc r k) (hp : pc≤u) (hr : r≤u) (hk : k≤u) (st : Word W)
    (tail : Fin Q → Bool) (t : Fin nt → Bool) (s : Fin ns → Bool) (par : Fin pk → Bool)
    (oa na oc nc : Fin A → Bool) :
    let D := installProgram (CapacityPadding.pad M hp hr hk) tail
    let pin := fields D t s par oa na oc nc
    (network hu hq he hparams 0 st).eval (fun i => pin (i.cast (fields_size Q nt ns pk A))) =
      value (FieldCode.ofCardLe (fieldBound hu hq)) M (2^(TraceVolume.depth u)) st
        (TickHeaderShift.initial W pin) := by
  intro D pin
  let S := (4*A+(nt+ns+pk))+Q
  have sz : S=PINS := fields_size ..
  have qle : Q≤PINS := Nat.le_add_right ..
  have advice_at (j : Fin Q) : pin ⟨j.val,lt_of_lt_of_le j.isLt qle⟩=D j := by
    change Fin.append D _ (j.castAdd _)=D j
    exact Fin.append_left ..
  have asgn : TraceBitHeader.advicePins (S:=S) 0 D (unshifted pin) =
      (fun i => pin (i.cast sz)) := by
    funext i
    have hsize : i.val<PINS := i.isLt.trans_le sz.le
    have same : i.cast sz = (⟨i.val,hsize⟩ : Fin PINS) := by
      apply Fin.ext
      simp only [Fin.val_cast]
    change TraceBitHeader.advicePins 0 D (unshifted pin) i = pin (i.cast sz)
    rw [same]
    by_cases h : i.val<Q
    · have x := advice_at ⟨i.val,h⟩
      simpa [TraceBitHeader.advicePins,h] using x.symm
    · simp [TraceBitHeader.advicePins,h,unshifted,hsize]
  have bits (b : Bool) : TraceBitHeader.binaryWord W b=bitWord W b := by cases b <;> rfl
  have initial : initialMemory S (fun a => TraceBitHeader.binaryWord W (unshifted pin a)) =
      TickHeaderShift.initial W pin := by
    rw [sz]
    funext a
    by_cases h : a<PINS <;>
      simp [TickHeaderShift.initial,initialMemory,unshifted,h,bits,bitWord]
  have stored : memoryWithAdvice 0 D (TickHeaderShift.initial W pin)=TickHeaderShift.initial W pin := by
    apply TickMountedPins.advice_agrees
    intro j
    have h := lt_of_lt_of_le j.isLt qle
    have atWord : TickHeaderShift.initial W pin j.val=bitWord W (D j) := by
      simp [TickHeaderShift.initial,initialMemory,h,advice_at j]
    rw [Nat.zero_add,atWord]
    cases D j <;> rfl
  have sim := TraceBitHeader.eval_tick_installed (volumeLarge hu) he hparams hq M hp hr hk
    0 (by omega) st tail (unshifted pin)
  change (network hu hq he hparams 0 st).eval (TraceBitHeader.advicePins 0 D (unshifted pin)) =
    value (FieldCode.ofCardLe (fieldBound hu hq)) M (2^(TraceVolume.depth u)) st
      (memoryWithAdvice 0 D (initialMemory S (fun a => TraceBitHeader.binaryWord W (unshifted pin a)))) at sim
  simpa only [asgn,initial,stored] using sim

/-- The back-shift executes in the native register frame and jumps directly to the fixed tick's
entry. This is the actual text that is padded and placed in the pin vector at address zero. -/
abbrev shiftedProgram {pc k : ℕ} (p : ℕ) (hu : cutoff≤u) (native : Machine W pc u k) :=
  SharedTickPrelude.attach (TickHeaderShift.procedure W p)
    (by have := (TickHeaderShift.text W p).2.1; have := large hu; omega) native

private theorem shift_room (hu : cutoff≤u) (he : e≤u) (hparams : nt+ns+pk≤u^e) :
    2+PINS+PINS<2^W := by
  have ub := large hu
  have small := (TraceVolume.pins_at_scale (volumeLarge hu) he hparams).1
  have dep := Nat.pow_le_pow_right (by decide : 0<2) (TraceVolume.depth_le u)
  have bound : PINS≤2^(u^10) := by unfold pinCount; omega
  have pos : 0<u^10 := Nat.pow_pos (by omega)
  have ample := Nat.pow_le_pow_right (by decide : 0<2) (show u^10+2≤W by omega)
  rw [pow_add] at ample
  have two := Nat.one_lt_two_pow pos.ne'
  norm_num at ample
  omega

private theorem eval_callee {pc k : ℕ} (hu : cutoff≤u) (hq : Fintype.card F≤u) (he : e≤u)
    (hparams : nt+ns+pk≤u^e) (native : Machine W pc u k)
    (hp : (TickHeaderShift.procedure W PINS).labels+pc≤u)
    (hk : (TickHeaderShift.procedure W PINS).slots+k≤u)
    (st : Word W) (tail : Fin Q → Bool) (t : Fin nt → Bool) (s : Fin ns → Bool)
    (par : Fin pk → Bool) (oa na oc nc : Fin A → Bool) (budget : ℕ) (v : F) :
    let M := shiftedProgram PINS hu native
    let D := installProgram (CapacityPadding.pad M hp (Nat.le_refl u) hk) tail
    let pin := fields D t s par oa na oc nc
    (∀ c : Config W pc u, c.pc=native.entry → Returns (FieldCode.ofCardLe (fieldBound hu hq))
      native.program budget c (TickMountedPins.memory pin) v) →
    28+16*PINS+budget≤2^(TraceVolume.depth u) →
    (network hu hq he hparams 0 st).eval (fun i => pin (i.cast (fields_size Q nt ns pk A)))=v := by
  intro M D pin tick fuel
  rw [startup_on_fields hu hq he hparams M hp (Nat.le_refl u) hk st tail t s par oa na oc nc]
  have run := SharedTickPrelude.attach_returns (TickHeaderShift.procedure W PINS)
    (by have := (TickHeaderShift.text W PINS).2.1; have := large hu; omega) native
    (FieldCode.ofCardLe (fieldBound hu hq))
    (fun m => m=TickHeaderShift.initial W pin) (fun _ out => out=TickMountedPins.memory pin)
    (28+16*PINS) budget (TickHeaderShift.spec pin (shift_room hu he hparams))
    (TickHeaderShift.initial W pin) rfl v (fun out eq => by subst out; exact tick)
    (M.program.start st) rfl
  change mass _ M.program (2^(TraceVolume.depth u)) _ _ = _
  simpa only [Nat.zero_add] using (run.later fuel) 0

/-- The sole universal trace on the unshifted p-pin input executes the installed shift and tick.
The final row semantics are the same for every tail of the installed program. -/
theorem eval_installed_shifted (hu : cutoff≤u) (hq : Fintype.card F≤u) (he : e≤u)
    (hparams : nt+ns+pk≤u^e) (cl : TickChronology.Clock) (fit : Fits (TickWeightedBank.shape F PINS H J) W)
    (nav : Block W np nr nk) (prep : Block W sp sr sk) (nd : Fin nk → Word W) (sd : Fin sk → Word W)
    (largeText : textCutoff F np sp nr sr nk sk≤u)
    (labelRoom : 37+(3400+9*(Fintype.card F*Fintype.card F)+np+sp)≤u)
    (publicRoom : 6+TickPublicData.count nk sk≤u)
    (x : CellInput B cl fit) (tail : Fin Q → Bool) (par : Fin pk → Bool) (oa na oc nc : Fin A → Bool)
    (team step navTime prepTime replay selected suffix C : ℕ) (st : Word W)
    (ft : team<2^nt) (fs : step<2^ns) (wt : team<2^W) (ws : step<2^W)
    (dur : cl.groupDuration<2^W) (last : cl.last<2^W) (begin : cl.beginTick<2^W)
    (space : WordBounds B fit) (pre admitted slotInput : Memory W → Prop) :
    let native := linkedProgram B cl fit nav prep nd sd largeText Q nt ns
    let M := shiftedProgram PINS hu native
    let hp : (TickHeaderShift.procedure W PINS).labels+
        Fintype.card (All (n:=np) (m:=sp) (k:=TickPublicData.count nk sk) B cl fit)≤u := by
      rw [(TickHeaderShift.text W PINS).1]
      exact (Nat.add_le_add_left (text_count B cl fit) 37).trans labelRoom
    let hk : (TickHeaderShift.procedure W PINS).slots+TickPublicData.count nk sk≤u := by
      rwa [(TickHeaderShift.text W PINS).2.2]
    let D := installProgram (CapacityPadding.pad M hp (Nat.le_refl u) hk) tail
    let ph := cl.phase step
    let pin := fields D (digits team nt) (digits step ns) par oa na oc nc
    let start := TickNavigationEntry.input B cl team step (TickMountedPins.memory (w:=W) pin)
    let field := codec (TickWeightedBank.shape F PINS H J) fit
    let _budget := (159+6*(nt+ns)+25+18*A)+(1470+navTime+21+x.tail prepTime)
    TickStageSpec.Admission field nav nd pre admitted (fun _ out => NavOutput x ph oa na oc nc slotInput out) navTime →
    pre start → TickStageSpec.Prepare prep sd slotInput
      (fun _ out => TickWeightedBank.Ready fit x.net x.lib pin (B).metadata (B).lut out) prepTime →
    let charges := TickTotalBudget.charges x nt ns navTime prepTime replay selected suffix
    8*(TickTotalBudget.coefficient charges C+124)≤u → e+1+TraceVolume.cm≤u →
    TickTotalBudget.Bounds charges (TraceVolume.cap u) (TickTotalBudget.replayBound u e C) →
    (network hu hq he hparams 0 st).eval (fun i => pin (i.cast (fields_size Q nt ns pk A))) =
      if TickAuxiliary.branch x.aux ph oa na then
        if admitted start then x.weight ph oa na oc nc pin else 0
      else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0 := by
  intro native M hp hk D ph pin start field budget navOk init prepare charges constant exponent bounds
  have ids : charges.tickBits+charges.teamBits+pk≤u^e := by
    change ns+nt+pk≤u^e
    omega
  have shifted := TickTotalBudget.shifted_trace_fuel (u:=u) (by have := large hu; omega) constant exponent bounds ids
  have counts : TickTotalBudget.shift charges u pk=28+16*PINS := by
    change 28+16*pinCount Q ns nt pk A=28+16*PINS
    unfold pinCount
    omega
  have charge : charges.fuel (TickTotalBudget.chunk u)=budget :=
    TickTotalBudget.charges_fuel x nt ns navTime prepTime replay selected suffix
  have fuel : 28+16*PINS+budget≤2^(TraceVolume.depth u) := by rwa [counts,charge] at shifted
  have room := shift_room hu he hparams
  have size : A≤PINS := by
    rw [← fields_size Q nt ns pk A]
    exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 4)).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  refine eval_callee hu hq he hparams native hp hk st tail (digits team nt) (digits step ns)
    par oa na oc nc budget _ ?_ fuel
  exact linked_execution cl fit nav prep nd sd largeText x D par oa na oc nc team step navTime prepTime
    ft fs wt ws dur last begin (by omega) space pre admitted slotInput navOk init prepare


/-- Only the identifiers and the actual navigation bound are needed on the rejected branch. -/
private def rejectCharges (nt ns nav : ℕ) : TickTotalBudget.Charges :=
  ⟨nt,ns,nav,0,0,0,0,0,0,0,0,0⟩

theorem eval_rejected_shifted (hu : cutoff≤u) (hq : Fintype.card F≤u) (he : e≤u)
    (hparams : nt+ns+pk≤u^e) (cl : TickChronology.Clock) (fit : Fits (TickWeightedBank.shape F PINS H J) W)
    (nav : Block W np nr nk) (prep : Block W sp sr sk) (nd : Fin nk → Word W) (sd : Fin sk → Word W)
    (largeText : textCutoff F np sp nr sr nk sk≤u)
    (labelRoom : 37+(3400+9*(Fintype.card F*Fintype.card F)+np+sp)≤u)
    (publicRoom : 6+TickPublicData.count nk sk≤u)
    (L : TickAuxiliary.Layout A) (tail : Fin Q → Bool) (par : Fin pk → Bool) (oa na oc nc : Fin A → Bool)
    (team step navTime C : ℕ) (st : Word W)
    (ft : team<2^nt) (fs : step<2^ns) (wt : team<2^W) (ws : step<2^W)
    (dur : cl.groupDuration<2^W) (last : cl.last<2^W) (begin : cl.beginTick<2^W)
    (space : WordBounds B fit) (pre admitted : Memory W → Prop) (post : Memory W → Memory W → Prop)
    (ageConstant : 8*((max (11161+28*C) (8*68))+124)≤u) (exponent : e+1+TraceVolume.cm≤u)
    (identifierCost : nt+ns≤TickTotalBudget.replayBound u e C)
    (navigationCost : navTime≤TickTotalBudget.replayBound u e C) :
    let native := linkedProgram B cl fit nav prep nd sd largeText Q nt ns
    let M := shiftedProgram PINS hu native
    let hp : (TickHeaderShift.procedure W PINS).labels+
        Fintype.card (All (n:=np) (m:=sp) (k:=TickPublicData.count nk sk) B cl fit)≤u := by
      rw [(TickHeaderShift.text W PINS).1]
      exact (Nat.add_le_add_left (text_count B cl fit) 37).trans labelRoom
    let hk : (TickHeaderShift.procedure W PINS).slots+TickPublicData.count nk sk≤u := by
      rwa [(TickHeaderShift.text W PINS).2.2]
    let D := installProgram (CapacityPadding.pad M hp (Nat.le_refl u) hk) tail
    let ph := cl.phase step
    let pin := fields D (digits team nt) (digits step ns) par oa na oc nc
    let start := TickNavigationEntry.input B cl team step (TickMountedPins.memory (w:=W) pin)
    let field := codec (TickWeightedBank.shape F PINS H J) fit
    TickStageSpec.Admission field nav nd pre admitted post navTime → pre start → ¬admitted start →
    (network hu hq he hparams 0 st).eval (fun i => pin (i.cast (fields_size Q nt ns pk A))) =
      if TickAuxiliary.branch L ph oa na then 0
      else if oa=(fun _ => false) ∧ na=(fun _ => false) ∧ oc=nc then 1 else 0 := by
  intro native M hp hk D ph pin start field admission initialized malformed
  let v := rejectCharges nt ns navTime
  have bounds : TickTotalBudget.Bounds v (TraceVolume.cap u) (TickTotalBudget.replayBound u e C) := by
    constructor
    · exact identifierCost
    · exact Nat.zero_le _
    · exact navigationCost
    all_goals exact Nat.zero_le _
  have timing := TickTotalBudget.shifted_trace_fuel (v:=v) (np:=pk)
    (by have := large hu; omega) ageConstant exponent bounds hparams
  let budget := (159+6*(nt+ns)+25+18*A)+(1470+navTime+21)
  have cap : budget≤v.fuel (TickTotalBudget.chunk u) := by
    dsimp [budget,v,rejectCharges,TickTotalBudget.Charges.fuel,TickTotalBudget.chunk]
    omega
  have fuel : 28+16*PINS+budget≤2^(TraceVolume.depth u) :=
    (Nat.add_le_add_left cap _).trans timing
  have room := shift_room hu he hparams
  have size : A≤PINS := by
    rw [← fields_size Q nt ns pk A]
    exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 4)).trans
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  refine eval_callee hu hq he hparams native hp hk st tail (digits team nt) (digits step ns)
    par oa na oc nc budget _ ?_ fuel
  exact rejected_execution cl fit nav prep nd sd largeText L D par oa na oc nc team step navTime
    ft fs wt ws dur last begin (by omega) space pre admitted post admission initialized malformed


end ThreeFlat.Diagonal.TraceStartupAtScale

end
end OAI
