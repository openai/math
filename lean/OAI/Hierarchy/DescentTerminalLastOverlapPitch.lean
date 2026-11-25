import OAI.Hierarchy.DescentCalibratedResetChart
import OAI.Hierarchy.DescentMeasuredLaneRoom
import OAI.Hierarchy.DescentNextStagePitch
import OAI.Hierarchy.DescentScheduledResetChart
import OAI.Hierarchy.DescentResetReceiverScale
import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentWalshDyadicChosen

namespace OAI
/-! # The last genuine reset fills the terminal signed word -/
namespace Hierarchy.DescentSixParty
open Filter DescentCompiler DescentPackedWalsh
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem final_walsh_room (t f g reset τ B K : ℕ)
    (cutoff : 2*(τ+(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g))≤B) :
    ∀ᶠ h : ℕ in atTop, ∀M i p,
      let J:=Nat.log 2 h/(2*B)
      let S:=stageNumbers G t J f g reset M (τ*(J+1))
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let m:=S.groupWidth k (τ*(J+1)) i+k
      let b:=S.localWalshBits p m f K
      i≤S.length → p≤h → τ*(J+1)+k≤laneBits m h b := by
  let κ:=1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
  let C:=localCoefficient G t f g reset K τ
  filter_upwards [dyadic_log_room ((8*C)^2) 4,eventually_ge_atTop (2^(2*B))] with h cost late
  intro M i p
  dsimp only
  let L:=Nat.log 2 h
  let J:=L/(2*B)
  let S:=stageNumbers G t J f g reset M (τ*(J+1))
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let m:=S.groupWidth k (τ*(J+1)) i+k
  let b:=S.localWalshBits p m f K
  intro age paid
  have cut : 2*(τ+κ)≤B:=cutoff
  have pos : 0<2*B:=by dsimp [κ] at cut; omega
  have floor : 2*B≤L:=Nat.le_log_of_pow_le (by decide) late
  have start : 0<J:=(Nat.le_div_iff_mul_le pos).2 (by simpa using floor)
  have jL : J≤L:=Nat.div_le_self ..
  have span : τ*(J+1)≤τ*(L+1)^2:=by
    exact Nat.mul_le_mul_left _ ((Nat.succ_le_succ jL).trans (by nlinarith))
  have bk : k≤κ*(J+1):=groupBits_linear ..
  have rb : b≤C*(L+1)^2:=actual_width G t J f g reset M (τ*(J+1)) i h p K τ paid jL span age
  have small : (8*b)^2≤h:=by
    calc
      (8*b)^2 ≤ (8*(C*(L+1)^2))^2:=Nat.pow_le_pow_left (Nat.mul_le_mul_left _ rb) _
      _ = (8*C)^2*(L+1)^4:=by ring
      _ ≤ h:=cost
  have double : 2*(τ*(J+1)+k)≤L:=by
    have bound : τ*(J+1)+k≤(τ+κ)*(J+1):=by rw [Nat.add_mul];omega
    have a:=Nat.mul_le_mul_left (τ+κ) (show J+1≤2*J by omega)
    have b₁:=Nat.mul_le_mul_right J cut
    have c:=Nat.div_mul_le_self L (2*B)
    change J*(2*B)≤L at c
    nlinarith only [bound,a,b₁,c]
  have hk : (2^(τ*(J+1)+k))^2≤h:=by
    rw [←pow_mul]
    apply (Nat.le_log_iff_pow_le (by decide) (show h≠0 by have :=Nat.two_pow_pos (2*B);omega)).mp
    omega
  have fits : 2^(τ*(J+1)+k)*(8*b)≤h:=by
    rcases le_total (2^(τ*(J+1)+k)) (8*b) with le|le
    · exact (Nat.mul_le_mul_right _ le).trans (by simpa only [pow_two] using small)
    · exact (Nat.mul_le_mul_left _ le).trans (by simpa only [pow_two] using hk)
  have bp : 0<8*b:=by
    dsimp [b,AtomSchedule.localWalshBits,DescentWalshPrecision.bits]
    omega
  exact le_min (by change τ*(J+1)+k≤(τ*(J+1)+k*(S.length-i))+k;omega)
    (Nat.le_log_of_pow_le (by decide) ((Nat.le_div_iff_mul_le bp).2 fits))


end Hierarchy.DescentSixParty

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentSIMDLookup DescentPackedWalsh
open ThreeFlat.Routing ThreeFlat.RAM ProtocolRAM
open Filter
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] ResetOutput.groupWidth

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
local notation "resetCut₀" => NativePitch.resetCut S k tail p f h age
local notation "m₀" => S.groupWidth k tail age+k
local notation "prior₀" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "rows₀" => ResetOutput.fromBoard G S board k tail age p f g drift degree h 0 resetCut₀ 1 nextM C packet prior₀ 0
local notation "chosen₀" => receiverCut G S board k tail age p f g drift degree h resetCut₀ nextM C packet oldLanes primitiveLanes printedBits venue

/-- The preceding venue is normalized for this particular reset's Walsh input.
Its dyadic exponent is exactly resetCut, including after an ordinary date. -/
theorem last_receiver (last : age+1=S.length)
    (walsh : tail+k≤laneBits m₀ h (S.localWalshBits p m₀ f (quota S.rounds)))
    (table : 8*(2^tail*(rows₀).groupWidth)≤h) : chosen₀=tail := by
  have previous : tail≤resetCut₀ := by
    change tail ≤ laneBits m₀ h (S.localWalshBits p m₀ f (quota S.rounds)) - k
    omega
  have next : S.groupWidth k tail (age+1)=tail:=by simp [AtomSchedule.groupWidth,last]
  have logRoom : tail≤Nat.log 2 (h/(8*(rows₀).groupWidth)) :=
    Nat.le_log_of_pow_le (by decide) ((Nat.le_div_iff_mul_le (Nat.mul_pos (by decide) (rows₀).groupWidth_pos)).2
      (by simpa only [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using table))
  change min (min resetCut₀ (min resetCut₀ (S.groupWidth k tail (age+1)))) (Nat.log 2 (h/(8*(rows₀).groupWidth)))=tail
  rw [next,min_eq_right previous,min_eq_right previous,min_eq_left logRoom]

/-- The three authentic pitches between the selected stage and the terminal reader:
the incoming previous exponent, the raw signed output and its normalized successor. -/
theorem booked_last (e:ℕ) (ageAt:age=e*(S.rounds+1)+S.rounds) (last:age+1=S.length)
    (base:S.baseGroups=2^tail) (ordinary:ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary)
    (matcher:nextM=NativePitch.incoming S k tail p f h ordinary (age+1))
    (addr:ℕ→ℕ→Bank) (roster:Bank) (floor:ℕ)
    (eb:chosen₀=tail) :
    let z:=selected G S board k tail age p f g drift degree h resetCut₀ nextM C packet oldLanes primitiveLanes
      printedBits venue addr roster floor
    NativePitch.incoming S k tail p f h ordinary age=2^resetCut₀ ∧
      z.successor.venue.next.signedLanes=S.groupCount S.length ∧
      z.successor.venue.next.lanes=S.groupCount S.length ∧
      chunks (S.groupCount S.length) z.successor.venue.next.signedLanes=1 := by
  have total:S.groupCount S.length=2^tail:=by simp [AtomSchedule.groupCount,base]
  have target:nextM=S.groupCount S.length:=by rw [matcher,last,NativePitch.terminal]
  have incoming : NativePitch.incoming S k tail p f h ordinary age=2^resetCut₀ := by
    subst age
    exact NativePitch.at_reset S k tail p f h ordinary e (by omega)
  refine ⟨incoming,?_,target,?_⟩
  · change 2^chosen₀=S.groupCount S.length
    rw [eb,total]
  · change chunks (S.groupCount S.length) (2^chosen₀)=1
    rw [eb,total]
    simpa [chunks] using DescentWalshDyadicBudget.exact_batch tail tail le_rfl

theorem last_date (e:ℕ) (ageAt:age=e*(S.rounds+1)+S.rounds) (last:age+1=S.length)
    (base:S.baseGroups=2^tail) (ordinary:ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary)
    (matcher:nextM=NativePitch.incoming S k tail p f h ordinary (age+1))
    (addr:ℕ→ℕ→Bank) (roster:Bank) (floor:ℕ)
    (walsh:tail+k≤laneBits m₀ h (S.localWalshBits p m₀ f (quota S.rounds)))
    (table:8*(2^tail*(rows₀).groupWidth)≤h) :
    let z:=selected G S board k tail age p f g drift degree h resetCut₀ nextM C packet oldLanes primitiveLanes
      printedBits venue addr roster floor
    NativePitch.incoming S k tail p f h ordinary age=2^resetCut₀ ∧
      z.successor.venue.next.signedLanes=S.groupCount S.length ∧
      z.successor.venue.next.lanes=S.groupCount S.length ∧
      chunks (S.groupCount S.length) z.successor.venue.next.signedLanes=1 := by
  exact booked_last G S board k tail age p f g drift degree h nextM C packet oldLanes primitiveLanes
    printedBits venue e ageAt last base ordinary matcher addr roster floor
    (last_receiver G S board k tail age p f g drift degree h nextM C packet oldLanes primitiveLanes
      printedBits venue last walsh table)


section Cofinal
open DescentCompiler.TerminalScale
variable {t reset τ σ B : ℕ}
local notation "κ" => 1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g
local notation "J_" h:max => Nat.log 2 h/(2*B)
local notation "tail_" h:max => τ*(J_ h+1)
local notation "S_" h:max M:max => stageNumbers G t (J_ h) f g reset M (tail_ h)
local notation "k_" h:max => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "priorCut" h:max M:max i:max p:max => NativePitch.resetCut (S_ h M) (k_ h) (tail_ h) p f h i

/-- Once the exponent of the actual reset's dictionary inventory has been fixed,
one cofinal choice works for all input sizes, venues, and the final chronological date. -/
theorem eventually_last_receiver (bought : 2*(τ+κ+σ)≤B) :
    ∀ᶠ h:ℕ in atTop,∀M age p drift degree nextM C packet oldLanes primitiveLanes printedBits
      (venue:StageVenueTail.Date),
      let S:=S_ h M
      let k:=k_ h
      let tail:=tail_ h
      let prev:=priorCut h M age p
      let old:=ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
      let inventory:=ResetOutput.fromBoard G S board k tail age p f g drift degree h 0 prev 1 nextM C packet old 0
      age+1=S.length → p≤h → inventory.groupWidth≤ scale (J_ h) σ →
      receiverCut G S board k tail age p f g drift degree h prev nextM C packet oldLanes primitiveLanes printedBits venue=tail := by
  have pos : 0<B := by omega
  have walsh := final_walsh_room G t f g reset τ B (quota t) (by omega)
  have shelf := eventually_home τ 0 σ B pos (by omega)
  filter_upwards [walsh,shelf] with h w hs
  intro M i p drift degree nextM C packet oldLanes primitiveLanes printedBits venue
  dsimp only
  intro last paid width
  have wal:=w M i p (by omega) paid
  let S:=S_ h M
  let k:=k_ h
  let tail:=tail_ h
  let prev:=priorCut h M i p
  let old:=ResetOutput.Prior.atDate G S i p drift oldLanes primitiveLanes printedBits venue
  let v:=ResetOutput.fromBoard G S board k tail i p f g drift degree h 0 prev 1 nextM C packet old 0
  have room:=hs.2 0 (2^tail) v.groupWidth (by simp [tail,TerminalScale.tail]) (by simp) width
  exact last_receiver G S board k tail i p f g drift degree h nextM C packet oldLanes primitiveLanes printedBits venue
    last wal ((Nat.mul_le_mul_right (2^tail*v.groupWidth) (by decide : 8 ≤ 32)).trans room)

private theorem equal_width {v w : ResetOutput}
    (roots : v.rootUnits = w.rootUnits) (ports : v.receiverUnits = w.receiverUnits) :
    v.groupWidth = w.groupWidth := by
  unfold ResetOutput.groupWidth
  rw [roots, ports]

/-- The coefficient census is the one on the emitted output of the chronological
instruction. The numerical conclusion does not charge the number of final groups. -/
theorem eventually_scheduled (bought : 2*(τ+κ+σ)≤B) :
    ∀ᶠ h:ℕ in atTop,∀M age p drift degree
      (ordinary:ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary) (op:RotorSpec)
      s Z operandLanes primitiveLanes (old:StageVenueTail.Date) (addr:ℕ→ℕ→Bank) (roster:Bank) floor,
      let S:=S_ h M
      let k:=k_ h
      let tail:=tail_ h
      let z:=scheduled G S board k tail age p f g drift degree h ordinary op s Z operandLanes primitiveLanes
        old addr roster floor
      age+1=S.length → p≤h → z.successor.groupWidth≤ scale (J_ h) σ →
      z.successor.venue.next.signedLanes=S.groupCount S.length ∧
      z.successor.venue.next.lanes=S.groupCount S.length ∧
      chunks (S.groupCount S.length) z.successor.venue.next.signedLanes=1 := by
  filter_upwards [eventually_last_receiver G board (t:=t) (reset:=reset) (τ:=τ) (B:=B) (σ:=σ) (f:=f) (g:=g) bought] with h bound
  intro M i p drift degree ordinary op s Z operandLanes primitiveLanes old addr roster floor
  dsimp only
  intro final paid price
  let S:=S_ h M
  let k:=k_ h
  let tail:=tail_ h
  let pre:=priorCut h M i p
  let nextM:=NativePitch.incoming S k tail p f h ordinary (i+1)
  let bits:=DescentPrimitivePalette.printedBits G s Z op
  let cutNow:=receiverCut G S board k tail i p f g drift degree h pre nextM op.C op.w operandLanes primitiveLanes bits old
  have units := selected_inventory G S board k tail i p f g drift degree h pre nextM op.C op.w
    operandLanes primitiveLanes bits old addr roster floor
  have same := equal_width units.1 units.2.1
  have eq : cutNow=tail := bound M i p drift degree nextM op.C op.w operandLanes primitiveLanes bits old
    final paid (same ▸ price)
  have terminal : S.groupCount S.length=2^tail:=by simp [S,stageNumbers,AtomSchedule.groupCount,tail]
  have next : nextM=S.groupCount S.length:=by
    change NativePitch.incoming S k tail p f h ordinary (i+1)=_
    rw [final,NativePitch.terminal]
  change 2^cutNow=S.groupCount S.length ∧ nextM=S.groupCount S.length ∧ chunks (S.groupCount S.length) (2^cutNow)=1
  refine ⟨(congrArg (fun j:ℕ=>2^j) eq).trans terminal.symm,next,?_⟩
  rw [eq,terminal]
  simpa [chunks] using DescentWalshDyadicBudget.exact_batch tail tail le_rfl

/-- Least uniform size exponent certified by the original physical per-date inventory. -/
noncomputable def receiverExponent {ι : ℕ→Type*} (J : ℕ→ℕ) (rows : ∀h,ι h→ResetOutput)
    (fit : ResetOutput.LocalInputs J rows) : ℕ := by
  classical
  exact Nat.find (ResetOutput.group_width_scale J rows fit)

theorem receiverExponent_le {ι : ℕ→Type*} (J : ℕ→ℕ) (rows : ∀h,ι h→ResetOutput)
    (fit : ResetOutput.LocalInputs J rows) (s : ℕ) (bound : ∀ᶠ h in atTop, ∀j,(rows h j).groupWidth≤ scale (J h) s) :
    receiverExponent J rows fit ≤ s := by
  classical
  exact Nat.find_min' (ResetOutput.group_width_scale J rows fit) bound

/-- The chosen physical reset is looked up in the measured receiver family. The
previous lane exponent, table size and final packet count are all discharged. -/
theorem eventually_scheduled_from_inputs {ι : ℕ→Type*} (rows : ∀h,ι h→ResetOutput)
    (fit : ResetOutput.LocalInputs (fun h=>J_ h) rows)
    (bought : 2*(τ+κ+receiverExponent (fun h=>J_ h) rows fit)≤B) :
    ∀ᶠ h:ℕ in atTop,∀ (j:ι h) M age p drift degree
      (ordinary:ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary) (op:RotorSpec)
      s Z operandLanes primitiveLanes (old:StageVenueTail.Date) (addr:ℕ→ℕ→Bank) (roster:Bank) floor,
      let S:=S_ h M
      let z:=scheduled G S board (k_ h) (tail_ h) age p f g drift degree h ordinary op s Z
        operandLanes primitiveLanes old addr roster floor
      age+1=S.length → p≤h → z.successor=rows h j →
      z.successor.venue.next.signedLanes=S.groupCount S.length ∧
      z.successor.venue.next.lanes=S.groupCount S.length ∧
      chunks (S.groupCount S.length) z.successor.venue.next.signedLanes=1 := by
  classical
  have widths : ∀ᶠ h in atTop,∀j,(rows h j).groupWidth≤ scale (J_ h) (receiverExponent (fun h=>J_ h) rows fit) :=
    Nat.find_spec (ResetOutput.group_width_scale (fun h=>J_ h) rows fit)
  filter_upwards [widths,eventually_scheduled G board (t:=t) (reset:=reset) (τ:=τ) (B:=B) (f:=f) (g:=g) bought] with h read eq
  intro j M age p drift degree ordinary op s Z operandLanes primitiveLanes old addr roster floor
  dsimp only
  intro last paid actual
  exact eq M age p drift degree ordinary op s Z operandLanes primitiveLanes old addr roster floor last paid
    (by rw [actual];exact read j)

/-- Canonical original schedules, with the actual receiver coefficient purchased once. -/
theorem calibrated_final (op : RotorSpec) (D drift : ℕ)
    (branch : G.b≤2^(capRate G t g)) (positive : 0<B)
    (bought : 2*(τ+κ+ResetOutput.receiverRate G board op t f g reset D)≤B) :
    ∀ᶠ h:ℕ in atTop,∀sites age p degree
      (ordinary:ℕ→DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary)
      (old:StageVenueTail.Date) (operandLanes primitiveLanes base : ℕ) (addr:ℕ→ℕ→Bank) (roster:Bank),
      let S:=S_ h sites
      let z:=scheduled G S board (k_ h) (tail_ h) age p f g drift degree h ordinary op
        (S.firstWidth G.b p) (S.grainAt G.b p 0) operandLanes primitiveLanes old addr roster base
      age+1=S.length → p≤h → degree≤D → old.degree=D →
      old.cap=((capCalendar G.b t g (J_ h)).take age).prod*256 → old.paidBits=S.censusBits p →
      z.successor.venue.next.signedLanes=S.groupCount S.length ∧
      z.successor.venue.next.lanes=S.groupCount S.length ∧
      chunks (S.groupCount S.length) z.successor.venue.next.signedLanes=1 := by
  filter_upwards [scheduled_scale G board op t f g reset τ D drift B positive branch,
    eventually_scheduled G board (t:=t) (reset:=reset) (τ:=τ) (B:=B) (f:=f) (g:=g) bought] with h small widths
  intro sites age p degree ordinary old operandLanes primitiveLanes base addr roster
  dsimp only
  intro last hp hd hD cap cbits
  exact widths sites age p drift degree ordinary op _ _ operandLanes primitiveLanes old addr roster base last hp
    (small sites age p degree ordinary old operandLanes primitiveLanes base addr roster hp hd hD cap cbits)

end Cofinal


end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
