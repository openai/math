import OAI.Hierarchy.DescentResetPublicDepth
import OAI.Hierarchy.DescentResetSuccessor
import OAI.Hierarchy.DescentResetDigits
import OAI.Hierarchy.DescentFixedMenu

namespace OAI
/-! # An actual reset and ordinal for every reached group state -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler DescentGL DescentColonies DescentBaseProfile DescentResetInvoice DescentFineTerminals
open DescentMixedRouter DescentRotor DescentHostDegree StarKeys
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {q ε : ℝ} {G : PoweredGadget F}
    (S : AtomSchedule) {i : ℕ} (A : GroupStage W G q ε (Fin (S.groupCount i)) V k)

local notation "grain" => A.z*G.b
local notation "full" => A.wire*grain*A.cap
variable (valid : A.StateBounds S i)
local notation "granular" => W.granular A.grainCount grain (A.grainCount_fit S valid)

theorem epoch_reset {n h C bitsR f g cut K tail : ℕ} (board : Graph n h)
    (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (vertex : V↪ℕ)
    (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut)
    (positive : 0<S.height) (age : i<S.length)
    (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (fcut : f≤cut) (gk : g≤k) (gainDef : g=reserveGain h C f)
    (hostGain : ResetInput.resetHostGain h (2^n) (depthBound A.degree n f g)≤S.hostGain)
    (capGain : g≤S.capGain) (fineGain : g≤S.capGain-(G.b+3)) (startCut : packExponent 20 3≤cut)
    (quota : A.degree*2^decayExponent A.degree≤K) (ports : 4*K≤2^n) (hK : 0<K)
    (positiveRotor : 0<bitsR) (rows : (2^n)^2*bitsR≤2^f)
    (menu : ∀p : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR p)
    (tailBound : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops A.degree (2^n):ℝ))
    (old : A.hist≤full) :
    ∃(Z : ResetInput granular (q*A.wire) ε h C (depthBound A.degree n f g)) (T : Z.Terminals),
      let key := DescentOrderedReset.grains W A.grainCount order
      Z.placement.OrderedTickets key ∧ ∃used : T.commonDepth=S.groupWidth k tail i, Z.k=S.groupWidth k tail i+k ∧ Z.unit=grain ∧ Z.n=n ∧ Z.width=bitsR ∧ HEq Z.graph board ∧
      ∃next : GroupStage (Z.orderedOrdinary T key) G q ε (Fin (S.groupCount (i+1))) ↥(Z.commonNames T) k,
        next.StateBounds S (i+1) ∧ next.z=A.z ∧ next.wire=A.wire ∧ next.hist=A.hist ∧ next.degree=3 ∧ next.cap=2^g*A.cap ∧
          next.pos=Z.groupPosition T (S.resetOutputDigits base radix age used) ∧
          next.block=Z.groupBlock T (S.resetOutputDigits base radix age used) ∧ next.hub=Z.commonTag T ∧
          ∃frame : Z.SourceFrame T (fun u=>(A.pos u).2) (filled W.graph A.pos A.block
            (S.resetInputDigits base radix i)) A.hub g,
            ResetInput.SourceFrame.Roster Z T (fun u=>(A.pos u).2)
              (filled W.graph A.pos A.block (S.resetInputDigits base radix i)) A.hub g frame vertex A.mutual n f full A.wire K (fun v w j=>
              (pairLoad (W.countWorld A.grainCount) (fun u=>(A.pos u).2)
                (filled W.graph A.pos A.block (S.resetInputDigits base radix i))
                (A.wire*grain) v w j:ℝ)) A.degree (A.resetLoad (S.resetInputDigits base radix i)) := by
  let depth := S.groupWidth k tail i
  let digits := S.resetInputDigits base radix i
  have pop : 2^(depth+k-k)=S.groupCount i := by simpa [depth] using S.group_power base radix i
  have reserve := reset_allocations h C f full A.hist old
  rw [←gainDef] at reserve
  obtain ⟨Z,T,bill,zk,depthEq,zn,count,unit,width,boardEq,⟨frame,roster⟩,tickets⟩ :=
    A.issued_reset_with_rosters S board order vertex valid age.le digits pop radix fixed budget
      fcut reserve.1 gk (by omega : k≤depth+k) quota ports hK positiveRotor rows menu tailBound
  have used : T.commonDepth=depth := by simpa using depthEq
  have range : Z.k-T.commonDepth≤k := by rw [zk,used];omega
  let code := S.resetOutputDigits base radix age used
  let key:=DescentOrderedReset.grains W A.grainCount order
  obtain ⟨next,status,z',w',h',d',cap',site,block,hub⟩ := A.reset_successor S valid Z T key code budget positive age
    radix fixed count unit frame.originalHub bill
    (by simpa only [Nat.cast_mul] using reserve.2.1)
    (by simpa only [Nat.cast_mul] using reserve.2.2.1)
    (by simpa only [Nat.cast_mul] using reserve.2.2.2) range
    (by simpa [zn,depthBound] using hostGain) capGain fineGain startCut
  exact ⟨Z,T,tickets,used,zk,unit,zn,width,boardEq,next,status,z',w',h',d',cap',site,block,hub,frame,roster⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
