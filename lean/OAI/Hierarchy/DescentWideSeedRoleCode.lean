import OAI.Hierarchy.DescentSeedCensusStamp
import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # The original literal and native program for publishing packed seed roles -/
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

def wideLiteral (start : ℕ) : Image bw :=
  ⟨start,endAddr start H R M s,Spaced.stamp (laneCount:=M) (s:=s) (R:=R) X start (fun _=>0)⟩

def wideProgram (start out : ℕ) : Procedure bw :=
  (wideLiteral (s:=s) (R:=R) X h bw start).program.seq (scan bw out n (spread (T start)))

def wideImage (start out : ℕ) (mem : Memory bw) : Memory bw :=
  image out n (spread (T start)) ((wideLiteral (s:=s) (R:=R) X h bw start).output mem)

def wideTime (start : ℕ) := (4+10*(endAddr start H R M s-start))+(4+60*n)

private theorem fittedSpread (banks : Tape) (bits out : ℕ)
    (allFit : ∀ bank∈[banks.source,banks.mask,banks.classes,banks.dict],bank.Fits bits out) :
    (spread banks).Fits bits out :=
  ⟨⟨allFit _ (by simp),⟨⟨allFit _ (by simp),trivial⟩,⟨allFit _ (by simp),trivial⟩⟩⟩,
    ⟨allFit _ (by simp),trivial⟩⟩

/-- The instruction tape also evaluates arbitrary machine inputs within the same public cost. -/
theorem wide_any (start out : ℕ) (mem : Memory bw) (placed : endAddr start H R M s≤out)
    (room : Room (T start) out (d*8) (roleBits s) M H R s bw) :
    let prog:=wideProgram (s:=s) (R:=R) X h bw start out
    let dst:=wideImage (s:=s) (R:=R) X h bw start out mem
    prog.Exec mem dst (wideTime (s:=s) (R:=R) X h start) ∧ CheapCode prog ∧
      ∀j,j<start ∨ out+n≤j→dst j=mem j := by
  let sheet:=wideLiteral (s:=s) (R:=R) X h bw start
  have high:=room.output
  have order : start≤endAddr start H R M s := by unfold endAddr;omega
  have capacity : sheet.low+sheet.length<2^bw := by
    change start+(endAddr start H R M s-start)<_;omega
  obtain ⟨mount,_,frame⟩:=sheet.issue mem capacity
  have fits := fittedSpread (T start) bw out room.fits
  have scanRun : (scan bw out n (spread (T start))).Exec (sheet.output mem)
      (image out n (spread (T start)) (sheet.output mem)) (4+60*n) := by
    have cost : 4+n*(2*(spread (T start)).work+4)=4+60*n := by rw [work]; ring
    rw [←cost]
    exact @scan_exec bw out n (spread (T start)) (sheet.output mem) fits room.output
  have litCheap : CheapCode sheet.program := sheet.hardware.1
  refine ⟨?_,@cheap_seq bw _ _ (@litCheap) (scan_cheap bw out n (spread (T start))),?_⟩
  · intro np nk nr machine pc reg slot exit code advice cfg ini located same
    exact Procedure.Exec.then mount scanRun machine pc reg slot exit code advice cfg ini located same
  · intro j hj
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ j (by omega)).trans
      (frame j (by change j<start ∨ endAddr start H R M s≤j;omega))

theorem wide_names (start out : ℕ) :
    DescentStaticWordColumn.names (wideProgram (s:=s) (R:=R) X h bw start out)=
      15*((endAddr start H R M s-start)+1)+(11+4*28) := by
  rw [wideProgram,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan,((wideLiteral (s:=s) (R:=R) X h bw start).hardware).2,work]; rfl

end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
