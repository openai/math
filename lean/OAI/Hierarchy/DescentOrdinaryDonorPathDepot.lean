import OAI.Hierarchy.DescentOrdinaryDonorPathStage
import OAI.Hierarchy.DescentDonorRetainedRegister
import OAI.Hierarchy.DescentMaskedLookupBook

namespace OAI
/-! # The signed path compiler reads the actual private-donor gather register in place -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentPacking.PackedMatch.Local
open DescentSixParty ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (s : Shape) {w H J M : ℕ}

def pathWidth := (ParentIncidence.pathBits s.degree*11)*(s.blocks*s.cap)

def pathSheet (profile b slots : ℕ) (side : Bool) (v : Parts s) : Cell (pathWidth s) :=
  let total:=chip s s.cap profile b slots v
  let issued:=(encode (bundleBits 3 s.names s.widths) (s.blocks*s.cap)).symm total
  let wires:=(encode (DescentSignedCableCodec.width s.degree s.cap) (s.blocks*(2*s.cap))).symm v.cables
  encode _ (s.blocks*s.cap) (fun t=>
    let pos : Fin s.blocks × Fin s.cap:=finProdFinEquiv.symm t
    let wire:=wires (finProdFinEquiv (pos.1,pos.2.castLE (by omega : s.cap≤2*s.cap)))
    ParentIncidence.paths profile pos.1 pos.2 side v.terrain v.owners wire
      (ParentIncidence.liveGate (unpackDonor (issued t))))

def pathRule (profile b slots : ℕ) (side : Bool) (old : Cell (totalBits s)) : Cell (pathWidth s) :=
  pathSheet s profile b slots side (separate s old)

@[simp] theorem pathRule_read (profile b slots : ℕ) (side : Bool) (v : Parts s) :
    pathRule s profile b slots side (combine s v)=pathSheet s profile b slots side v :=by simp [pathRule]

def pathProgram (profile b slots : ℕ) (side : Bool) (H J M w base out : ℕ) (src : Bank) :=
  let law:=pathRule s profile b slots side
  (DescentSIMDLookup.Book.install law H J M w base).seq
    (DescentSIMDLookup.program (DescentSIMDLookup.Book.banks base (totalBits s) H J M src) out H J M w)

theorem paths_run (profile b slots : ℕ) (side : Bool) (base out : ℕ) (src : Bank) (m : Memory w) (x : Fin H→Fin J→Parts s)
    (old : Reads src (fun h j=>combine s (x h j)) M m)
    (lower : src.base+H*chunks J M≤base)
    (upper : base+DescentSIMDLookup.Book.words (totalBits s) H J M≤out)
    (fit : DescentSIMDLookup.Fits (DescentSIMDLookup.Book.banks base (totalBits s) H J M src)
      (totalBits s) (pathWidth s) M H J w out) :
    let law:=pathRule s profile b slots side
    let n:=H*chunks J M
    let table:=DescentSIMDLookup.Book.image law H J M base m
    let banks:=DescentSIMDLookup.Book.banks base (totalBits s) H J M src
    let after:=image out n (lookup banks) table
    (pathProgram s profile b slots side H J M w base out src).Exec m after
      ((4+10*DescentSIMDLookup.Book.words (totalBits s) H J M)+(4+44*n)) ∧
      (∀p : Row H J M,after (out+(row H J M p).val)=((data (fun h j=>pathSheet s profile b slots side (x h j)) p).val:Word w)) ∧
      (∀v,v<base ∨ out+n≤v→after v=m v) ∧ CheapCode (pathProgram s profile b slots side H J M w base out src) :=by
  intro law n tab banks later
  have space:=upper.trans_lt ((Nat.le_add_right ..).trans_lt fit.output)
  obtain ⟨loaded,fixed,frame,cheap⟩:=DescentSIMDLookup.Book.mount law H J M base src m space
  have pins : PinFrame (M:=M) banks law (fun h j=>combine s (x h j)) tab:=by
    refine ⟨fun p bit=>congrArg (fun w':Word w=>Computability.VPVNP.RAMSerialization.wordBits w w' bit) (fixed p),?_⟩
    intro p
    exact (frame _ (.inl ((Nat.add_lt_add_left (row H J M p).isLt _).trans_le lower))).trans (old p)
  have cpu : (DescentSIMDLookup.program banks out H J M w).Exec tab later (4+44*n) :=by
    rw [show 4+44*n=4+n*(2*(lookup banks).work+4) from by rw [lookup_work]; omega]
    exact scan_exec out n (lookup banks) tab
      (show (lookup banks).Fits w out from ⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩) fit.output
  refine ⟨loaded.then cpu,?_,?_,cheap_seq cheap (@scan_cheap _ _ _ _)⟩
  · intro p
    simpa only [law,pathRule_read] using (PackedCensus.col_read banks out fit law (fun h j=>combine s (x h j)) tab pins p)
  · rintro v (h|h)
    · have pre : base≤out := (Nat.le_add_right ..).trans upper
      simpa [later,image,fillSegment,Nat.not_le.mpr (h.trans_le pre)] using frame v (.inl h)
    · simpa [later,image,fillSegment,Nat.not_lt.mpr h] using frame v (.inr (upper.trans ((Nat.le_add_right ..).trans h)))

end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
