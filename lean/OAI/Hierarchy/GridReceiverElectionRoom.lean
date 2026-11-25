import OAI.Hierarchy.GridReceiverDirectoryElection
import OAI.Hierarchy.GridReceiverTaskCount

namespace OAI
/-! # Public allocation for the native selected-root election -/

namespace Hierarchy.GridReceiverDirectory
open ThreeFlat Diagonal PhysicalStage RAM
open GridRegisteredSetting GridInstalledEvaluator TraceAdmission TraceDistribution GridScale Filter
open Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type} [Field F] [Fintype F]

/-- The public receiver directory counts the roots directly from its stages. -/
theorem public_sites {w pc rr pp size base fuel axes : ℕ}
    (D : RunData F (64*w) pc rr pp size base fuel axes (w/2)) (l : GridNativeImage.Layout) :
    (parameters D l).roots≤(axes+1)*2^(axes+1) := by
  let P:=D.block.repeat D.passes
  let rem:=axes+1-P.charge
  let a:=archive D l
  have spent : P.charge≤axes+1 := by dsimp [P];rw [D.block.charge_repeat];exact D.passesFit
  have lanes : P.charge+rem=axes+1 := by dsimp only [rem];omega
  change (NavigationPass.TraceRecovery.lastLayer a.K (P.directory rem (axes+1)) a.cursor a.seedLayer).count≤_
  rw [GridRegisteredOrder.directory_count P a.K rem (axes+1) a.cursor a.seedLayer
    (by rw [lanes]; rfl)]
  simpa only [lanes] using P.finalSites_le rem (axes+1)

private theorem election_banks {w text N rows : ℕ} (age : 4≤w)
    (cal : 4*w≤(receiverAge w)^10 ∧ (receiverAge w)^10≤5*w)
    (frontRoom : 2+text+64*w≤2^w) (sites : N≤2^w) (product : rows≤2^(2*w)) :
    GridReceiverTickDirectory.Room (GridReceiverTickDirectory.banks w (receiverAge w))
      (64*w) (2+text) N rows := by
  let step:=TickWorkspace.stride (receiverAge w)
  let J:=GridDescription.sector w
  let g:=GridPinArena.slab w
  have mono : ∀ {i j : ℕ}, i≤j → (2:ℕ)^i≤2^j := Nat.pow_le_pow_right (by decide)
  have exp : step=2^((receiverAge w)^10*4) := by
    change (2^(receiverAge w)^10)^4=_
    rw [pow_mul]
  have exLo:=cal.1
  have exHi:=cal.2
  have one : (2:ℕ)^w≤ step := exp ▸ mono (by omega)
  have two : (2:ℕ)^(2*w)≤ step := exp ▸ mono (by omega)
  have under : 32*step≤J := calc
    _ = 2^(5+(receiverAge w)^10*4) := by rw [exp,pow_add]; rfl
    _ ≤ _ := mono (show 5+(receiverAge w)^10*4≤32*w by omega)
  have small : (2:ℕ)^w≤g := mono (show w≤16*w by omega)
  have minStep : 5≤ step := ((show 5≤(2:ℕ)^4 by decide).trans (mono age)).trans one
  obtain ⟨low,high⟩:=GridPinArena.scales w (by omega)
  change 32*g≤J at low
  change 32*J<2^(64*w) at high
  have word : step<2^(64*w) := (show step≤32*J by omega).trans_lt high
  constructor
  · change (2+text)+(64*w)≤18*step;omega
  · change 18*step+rows≤19*step;omega
  · change 19*step+5≤15*J+g;omega
  · change 15*J+g+N≤15*J+3*g;omega
  · change 15*J+3*g+N≤15*J+20*g;omega
  · change 15*J+20*g+2<2^(64*w);omega
  · omega
  · omega
  · omega

private theorem election_root_count {w roots axes stages : ℕ}
    (sites : roots ≤ (axes+1)*2^(axes+1))
    (record : 1*(stages+1)*(1+(axes+1)*2^(axes+1))*(64*w+1) ≤ 2^(3*w/5)) :
    roots ≤ 2^w := by
  have first := Nat.le_mul_of_pos_left (1+(axes+1)*2^(axes+1))
    (Nat.mul_pos Nat.zero_lt_one (Nat.succ_pos stages))
  have last := Nat.le_mul_of_pos_right (1*(stages+1)*(1+(axes+1)*2^(axes+1)))
    (Nat.succ_pos (64*w))
  have small := Nat.pow_le_pow_right (by decide : 0<2) (show 3*w/5≤w by omega)
  exact sites.trans ((Nat.le_add_left _ 1).trans (first.trans (last.trans (record.trans small))))

private theorem election_front_room {w text args : ℕ} (textFit : text ≤ w^2)
    (bound : 2*w^2+2+(args+1)*(64*w)+GridReceiverHeader.count w*(64*w) ≤ 2^w) :
    (2+text)+(args+1)*(64*w)+(64*w)*GridReceiverHeader.count w ≤ 2^w ∧
      2+text+(64*w) ≤ 2^w := by
  rw [Nat.mul_comm (64*w) (GridReceiverHeader.count w)]
  have paid : 64*w ≤ (args+1)*(64*w) := Nat.le_mul_of_pos_left (64*w) (Nat.succ_pos args)
  constructor <;> omega

set_option maxHeartbeats 1600000 in
/-- The classifier and selector share the registered root cardinality in
the actual receiver directory at its least sufficient physical age. -/
theorem eventual_election_room (blk : Block F) {Q : ℕ→ℕ} {loss : ℕ→ℝ}
    (env : Envelopes Q loss) (m A degree stageRate rootRate : ℕ) (q : ℕ→ℕ)
    (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop, ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w→
      ∀ I : Installed blk m A w degree stageRate rootRate v,
        ElectionRoom I.D (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate) := by
  let k:=m+1
  let d:=k+2
  let c := GridStructuralHeader.coefficient blk
  have scale:=trace_scale env k A 2 q range
  filter_upwards [TraceAdmission.record_room scale 1, GridReceiverClock.tick_count env k,
    polynomial_room (22^d) d,polynomial_room d 0,polynomial_room 22 1,
    polynomial_room (1500+64*c) 16,eventually_ge_atTop (64^10+1024)] with
    w record tcnt classes dimension threshold headPoly adult
  intro v chosen I
  let a:=overhead Q loss w
  let l:=layout m A w a v.copies degree stageRate rootRate
  let N:=(parameters I.D l).roots
  let T:=(l.sideMinusOne+1)^k*v.copies
  let text:=l.receiverText
  let args:=GridNativeImage.parameterCount I.D l
  let radix:=20*(w+1)+2
  have pos : 0<w := by omega
  have mono : ∀ {i j : ℕ}, i≤j → (2:ℕ)^i≤2^j := Nat.pow_le_pow_right (by decide)
  have little : (2:ℕ)^(w/100)≤2^w := mono (Nat.div_le_self ..)
  have cut : (2:ℕ)^(3*w/5)≤2^w := mono (by omega)
  have dim : I.axes+1=evalDepth w k A 2 a (q w)+1-w/2 := by
    rw [←chosen]
    exact I.axes_eq
  change 1*(traceBlocks k a+1)*
    (1+(evalDepth w k A 2 a (q w)+1-w/2)*2^(evalDepth w k A 2 a (q w)+1-w/2))*
    (64*w+1)≤2^(3*w/5) at record
  rw [←dim] at record
  have full := public_sites I.D l
  change N≤(I.axes+1)*2^(I.axes+1) at full
  have roots : N≤2^w := election_root_count full record
  have width : d≤2^w := (show d≤2^(w/100) by simpa using dimension).trans little
  have radixBound : radix≤22*(w+1) := by dsimp [radix];omega
  have types : radix^d≤2^w := calc
    _ ≤ (22*(w+1))^d := Nat.pow_le_pow_left radixBound _
    _ = 22^d*(w+1)^d := mul_pow ..
    _ ≤ 2^(w/100) := classes
    _ ≤ _ := little
  have steps : 20*(w+1)+1≤2^w := (show 20*(w+1)+1≤22*(w+1) by omega).trans
    ((show 22*(w+1)≤2^(w/100) by simpa using threshold).trans little)
  have prod {x y : ℕ} (hx : x≤2^w) (hy : y≤2^w) : x*y ≤ 2^(2*w) :=
    (Nat.mul_le_mul hx hy).trans_eq (by rw [←pow_add];congr 1;omega)
  have matrix := prod roots width
  have scan := prod types roots
  have time : N*d*(20*(w+1)+1)≤2^(3*w) :=
    (Nat.mul_le_mul matrix steps).trans_eq (by rw [←pow_add];congr 1;omega)
  have narrow : (2:ℕ)^(3*w)<2^(64*w) := Nat.pow_lt_pow_right (by decide) (by omega)
  have small : (2:ℕ)^w≤GridPinArena.slab w := mono (show w≤16*w by omega)
  have twoSmall : (2:ℕ)^(2*w)≤GridPinArena.slab w := mono (show 2*w≤16*w by omega)
  have sideEq : l.sideMinusOne+1=side a := Nat.sub_add_cancel (Nat.two_pow_pos _)
  have ticks : T≤2^w := by
    dsimp only [T];rw [sideEq];exact (tcnt v.copies v.copies_le).trans cut
  have textFit : text≤w^2 := by
    have both := (GridDescription.room (w:=w) (p:=GridDescription.capacity w)
      (k:=GridDescription.capacity w) (p':=GridDescription.capacity w)
      (k':=GridDescription.capacity w) (by omega) le_rfl le_rfl le_rfl le_rfl).room
    change text+text+0≤w^2 at both
    omega
  have header : 2*w^2+2+(args+1)*(64*w)+GridReceiverHeader.count w*(64*w) ≤
      (1500+64*c)*(w+1)^16 :=
    GridReceiverHeader.structural_words w c 14 args I.parameters_le
  obtain ⟨frontRoom,textOnly⟩ := election_front_room textFit (header.trans (headPoly.trans little))
  have smallWord : (2:ℕ)^w<2^(64*w) := (mono (by omega : w≤3*w)).trans_lt narrow
  refine ⟨pos,Nat.mul_pos (Nat.pow_pos (Nat.succ_pos _)) v.copies_pos,
    matrix.trans twoSmall,steps.trans small,roots.trans small,types.trans small,time.trans_lt narrow,
    width.trans_lt smallWord,ticks.trans_lt smallWord,frontRoom.trans (mono (show w≤32*w by omega)),?_⟩
  exact election_banks (by omega) (receiverAge_chart w (by omega)) textOnly roots scan

end Hierarchy.GridReceiverDirectory

end OAI
