import OAI.Hierarchy.DescentEarlyReelScale
import OAI.Hierarchy.DescentExteriorLateReel

namespace OAI
/-! The two seventeen-column relocations and their separate matrix flights at the calibrated height. -/
namespace Hierarchy.DescentExteriorMatrixUpdate.Calendar
open DescentCompiler DescentExteriorShelf DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

def postProgram (plan : Reel) (dim age j r t e w compact takeOff : ℕ) : Procedure w :=
  (relocate j r t e w compact takeOff).seq (plan.program j r t e w dim age takeOff)

def postClock (age j r t e : ℕ) :=
  (4+18*(17*span j r t e))+(10+((4+58*age)+(4+16*e)))

theorem post_names (plan : Reel) (dim age j r t e w compact takeOff : ℕ) :
    names (postProgram plan dim age j r t e w compact takeOff)=108+111*age := by
  unfold postProgram
  rw [names_seq,relocate,names_scan,Reel.program,names_seq,names_scan,publish,names_seq,dated_names,names_scan]
  change (11+4*7)+((11+4*1)+(19+111*age+(11+4*6)))=_
  omega

theorem post_clock_le (S : AtomSchedule) (k tail j r t e : ℕ) :
    postClock S.length j r t e≤earlyClock S k tail j r t e := by
  unfold postClock earlyClock
  omega

end
end Hierarchy.DescentExteriorMatrixUpdate.Calendar

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentExteriorMatrixUpdate
open DescentExteriorShelf DescentStaticWordColumn Catalyst Filter
open scoped Topology
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)
variable (rounds f g reset τ B : ℕ)
local notation "κ" => 1+(hostRate rounds reset+capRate G rounds g)*(rounds+1)+8+cutRate rounds f g
local notation "bits" => fun J => groupBits rounds J (hostRate rounds reset) (capRate G rounds g) (cutRate rounds f g)
local notation "sched" => fun J M => stageNumbers G rounds J f g reset M (tail τ J)

theorem stage_both_native_reels (large : 20≤B) (reserve : 2*localSocketRate G rounds g≤τ)
    (budget : 2*(localSocketRate G rounds g+(τ+κ+4))+Nat.clog 2 G.b*(rounds+1)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M w factor base lo compact lateStart takeOff : ℕ, let S:=sched J M
        let j:=Nat.clog 2 (NativeBranch.localLimit G S)
        let dim:=S.groupWidth (bits J) (tail τ J) 0+bits J
        let r:=dim-2*j
        let split:=NativeBranch.binLimit (k:=bits J) S
        let U:=G.b^(rounds*J)*G.b
        let p:=split*(h/(16*((2^j*U)*split)))
        let s:=S.firstWidth G.b p
        ∀ {cp P : ℕ} (X : Approximation F cp P) (tag : ℕ→Bool) (rot loc : ℕ→ℕ) (plan : Reel),
          let n:=(Chronology.countDates 0 (Chronology.kindCalendar S.rounds S.height)).length
          let E:=Fintype.card (Port P X.width)
          let code:=SeedNamed.Branch.historyCountReel X S base tag rot loc lo compact
            (bits J) (tail τ J) j r s w
          2^h≤2*(M*S.copies) → w≤factor*h →
          ((4+11*n+Calendar.earlyClock S (bits J) (tail τ J) j r s E+7*names code)+
            (Calendar.postClock S.length j r s E+
              7*names (Calendar.postProgram (plan.late lateStart) dim S.length j r s E w compact takeOff)))*(w+1)*2^J≤
            (524288*(factor+1))*((S.copies*s)*(M+2^J*E)) := by
  filter_upwards [stage_early_native_price G rounds f g reset τ B large reserve budget] with h fee
  intro J M w factor base lo compact lateStart takeOff S j dim r split U p s cp P X tag rot loc plan n E code support arch
  let T:=2^J
  let early:=4+11*n+Calendar.earlyClock S (bits J) (tail τ J) j r s E+7*names code
  let late:=Calendar.postClock S.length j r s E+
    7*names (Calendar.postProgram (plan.late lateStart) dim S.length j r s E w compact takeOff)
  let purchased:=(S.copies*s)*(M+T*E)
  have first_ : early*(w+1)*T ≤ (262144*(factor+1))*purchased :=
    fee M w factor base lo compact X tag rot loc support arch
  have clock_:=Calendar.post_clock_le S (bits J) (tail τ J) j r s E
  have text_ : names (Calendar.postProgram (plan.late lateStart) dim S.length j r s E w compact takeOff) ≤ names code := by
    dsimp only [code]
    rw [Calendar.post_names,SeedNamed.Branch.counted_names]
    omega
  have later : late ≤ early :=
    Nat.add_le_add (clock_.trans (Nat.le_add_left ..)) (Nat.mul_le_mul_left 7 text_)
  have second_ := (Nat.mul_le_mul_right T (Nat.mul_le_mul_right (w+1) later)).trans first_
  change (early+late)*(w+1)*T ≤ (524288*(factor+1))*purchased
  calc
    _ = early*(w+1)*T+late*(w+1)*T := by ring
    _ ≤ (262144*(factor+1))*purchased+(262144*(factor+1))*purchased := Nat.add_le_add first_ second_
    _ = _ := by ring

end
end Hierarchy.DescentSixParty

end OAI
