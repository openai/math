import OAI.Hierarchy.DescentLocalWalshBits
import OAI.Hierarchy.DescentWalshPrecision
import OAI.Hierarchy.DescentResetIssuedWords

namespace OAI
/-! # Original reset-load and gain precision from the installed census -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentIntegerScale DescentMeasuredWeights
open DescentWalshPrecision DescentBaseVariance
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type}
  [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule) {i m : ℕ}
local notation "full" => A.wire*(A.z*G.b)*A.cap

theorem original_calibration {grainAge : ℕ} (digits : Block m≃J×Block k) (ready : A.StateBounds S i)
    (p f K : ℕ) (positive : 0<S.height) (age : i≤S.length) (grain : A.z=S.grainAt G.b p grainAge)
    (old : A.wire=S.epochPower^S.priceExponent) (base : G.b≤2^S.capGain) (depth : V→ℕ) :
    let u:=S.censusBits p
    let b:=S.localWalshBits p m f K
    let g:=gainBits m f K u
    let levels:=inputLevels (k:=m) depth
    let C:=Contacts A.mutual
    let x:=load levels (fun v (z : Bits m)=>A.resetLoad digits v (DescentColonies.address m z))
      (fun (v : C) (z : Bits m)=>A.resetFlow digits v.1 v.2.val (DescentColonies.address m z))
    (∀v j,A.resetLoad digits v j≤full) ∧
      (∀v w j,A.resetFlow digits v w j≤full) ∧
      2^(3*m)*full^2<2^b ∧ g≤b ∧
      (∀t : Item levels C,gain levels f full K t<2^g) ∧
      (∀t z,x t z≤full) ∧ (∀t z,gain levels f full K t*natCorrelation (x t) z<2^b) := by
  let u:=S.censusBits p
  let levels:=inputLevels (k:=m) depth
  let C:=Contacts A.mutual
  have fits:full≤2^u:=(A.census_caps_at S ready positive age grain old base).2.le
  have measured:=A.reset_words_at S ready digits
  have rate_ := gain_room (C:=C) m f K u full levels (fun v=>by unfold levels inputLevels;omega) fits
  let x:=load levels (fun v (z : Bits m)=>A.resetLoad digits v (DescentColonies.address m z))
    (fun (c : C) (z : Bits m)=>A.resetFlow digits c.1 c.2.val (DescentColonies.address m z))
  have bounds (t : Item levels C) (z : Bits m) : x t z≤full := by
    cases t with
    | inl a=>exact (measured a.1 a.1 _).2
    | inr c=>exact (measured c.1 c.2.val _).1.trans (measured c.1 c.2.val _).2
  exact ⟨fun v j=>(measured v v j).2,fun v w j=>(measured v w j).1.trans (measured v w j).2,
    numerator_room m f K u full fits,gain_le ..,rate_,bounds,
    fun t z=>correlation_room (x t) full _ z fits (bounds t) (rate_ t)⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
