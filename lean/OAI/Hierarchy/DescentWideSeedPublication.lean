import OAI.Hierarchy.DescentSeedWideBundleRead
import OAI.Hierarchy.DescentWideSeedRoleCode

import OAI.Hierarchy.DescentWideSeedHeader
import OAI.Hierarchy.DescentSeedCensusScan
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Mounted census role tables for short seed lanes on a wide machine -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSIMDLookup DescentPackedColony.Phase.Arena Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {k p R s : ℕ} (X : Approximation F k p) (h bw : ℕ)
local notation "H" => Fintype.card (Old X)
local notation "d" => digitsNeeded s
local notation "M" => pieces h s
local notation "n" => H*chunks R M
local notation "T" => fun start=>tape start H R M s (publicWords X)

theorem wide_stamp (start : ℕ) (mem : Memory bw) (space : endAddr start H R M s<2^bw) :
    ((wideLiteral (s:=s) (R:=R) X h bw start).output mem)=Spaced.stamp (laneCount:=M) (s:=s) (R:=R) X start mem := by
  let sheet:=wideLiteral (s:=s) (R:=R) X h bw start
  have fits : sheet.low+sheet.length<2^bw :=by
    change start+(endAddr start H R M s-start)<_
    unfold endAddr at space ⊢;omega
  obtain ⟨_,inside,outside⟩:=sheet.issue mem fits
  funext j
  by_cases near : start≤j∧j<endAddr start H R M s
  · rw [inside j near.1 near.2]
    have high:=near.2
    unfold endAddr at high
    change Spaced.stamp (laneCount:=M) (s:=s) (R:=R) X start (fun _=>0) j=_
    unfold Spaced.stamp shelf
    split_ifs <;> first | rfl | omega
  · rw [outside j (by change j<start ∨ endAddr start H R M s≤j;omega)]
    unfold endAddr at near
    unfold Spaced.stamp shelf
    split_ifs <;> first | rfl | omega

theorem wide_publish (start out : ℕ) (sel : Select X R s→Bool) (mem : Memory bw)
    (earlier : publicWords X+n≤ start) (placed : endAddr start H R M s≤out)
    (source : ∀p : Row H R M,mem (publicWords X+(row H R M p).val)=((data (bundles X sel) p).val:Word bw))
    (room : Room (T start) out (d*8) (roleBits s) M H R s bw) :
    let prog:=wideProgram (s:=s) (R:=R) X h bw start out
    let dst:=wideImage (s:=s) (R:=R) X h bw start out mem
    prog.Exec mem dst (wideTime (s:=s) (R:=R) X h start) ∧ CheapCode prog ∧
      (∀p : Row H R M,dst (out+(row H R M p).val)=
        ((data (fun v j=>entry s (sitePlan X v) (bundles X sel v j)) p).val:Word bw)) ∧
      ∀j,j<start ∨ out+n≤j→dst j=mem j := by
  let sheet:=wideLiteral (s:=s) (R:=R) X h bw start
  have high:=room.output
  have top : endAddr start H R M s<2^bw:=by omega
  have lower : start≤endAddr start H R M s:=by unfold endAddr;omega
  have slots : sheet.low+sheet.length<2^bw :=by
    change start+(endAddr start H R M s-start)<_;omega
  obtain ⟨mount,_,frame⟩:=sheet.issue mem slots
  have same:=wide_stamp X h bw start mem top
  obtain ⟨ran,values,_,tiny⟩:=Spaced.native X start out sel mem earlier source room
  rw [←same] at ran values
  have litCheap : CheapCode sheet.program := sheet.hardware.1
  refine ⟨?_,@cheap_seq bw _ _ (@litCheap) (@tiny),values,?_⟩
  · intro np nk nr machine pc reg slot exit code advice cfg ini located sameMem
    exact Procedure.Exec.then mount ran machine pc reg slot exit code advice cfg ini located sameMem
  · intro j hj
    have off : j<out ∨ out+n≤j:=by omega
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ j off).trans (frame j (by
      change j<start ∨ endAddr start H R M s≤j;omega))

end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
