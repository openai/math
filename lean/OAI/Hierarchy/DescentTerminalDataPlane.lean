import OAI.Hierarchy.DescentTerminalShapeData
import OAI.Hierarchy.DescentTerminalExteriorFlags
import OAI.Hierarchy.DescentTerminalPublicWordRAM
import OAI.Hierarchy.DescentTerminalRawJoin
import OAI.Hierarchy.DescentTerminalHeaderAny

namespace OAI
/-! # One common terminal program up through authentic width-prefix publication -/
namespace Hierarchy.DescentTerminalDataPlane
open Computability.VPVNP.BurstRAM PrivateRAM DescentExteriorShelf ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ}



structure Layout where
  exterior : ℕ
  output : Bank
  «public» : DescentTerminalPublicWordRAM.Tapes
  candidate : Bank
  raw : Bank
  header : DescentTerminalDenseHeaderRAM.Layout

variable (S : Shape) (L : Layout)
local notation "E" => S.exteriors*2^(S.headBits+S.restBits)
local notation "H" => span S.headBits S.restBits S.bitLanes S.exteriors
local notation "ext" => flagged w S.exteriors S.headBits S.restBits S.bitLanes L.exterior
local notation "pub" => DescentTerminalPublicWordRAM.program w L.output.base S.publicRows L.public
local notation "gather" => DescentTerminalRawJoin.program w S.rawRows S.publicRows L.candidate L.output L.raw
local notation "headers" => DescentTerminalDenseHeaderRAM.program w S.headerRows L.header

def program := (((ext).seq pub).seq gather).seq headers
def time := ((84+492*E+(4+(S.publicRows+2)*(2*53+4)))+
  (4+L.raw.size*(2*(DescentTerminalRawJoin.load S.rawRows S.publicRows L.candidate L.output).work+4)))+
  DescentTerminalDenseHeaderRAM.cost S.headerRows L.header
def exterior (m : Memory w) := flaggedMem (e:=S.exteriors) (j:=S.headBits) (r:=S.restBits)
  (t:=S.bitLanes) L.exterior m
def exteriorRows (m : Memory w) := image L.output.base (S.publicRows+2)
  (DescentTerminalPublicWordRAM.row L.public S.publicRows) (exterior S L m)
def file (m : Memory w) := DescentTerminalRawJoin.output S.rawRows S.publicRows L.candidate L.output L.raw (exteriorRows S L m)
def finalMem (m : Memory w) := DescentTerminalDenseHeaderRAM.finalMem L.header S.headerRows (file S L m)

structure Room (w : ℕ) : Prop where
  frame : L.exterior+24*H<2^w
  publicFit : DescentTerminalPublicWordRAM.Fits L.public w L.output.base
  publicRoom : L.output.base+(S.publicRows+2)<2^w
  candidate : L.candidate.Fits w L.raw.base
  published : L.output.Fits w L.raw.base
  rawRoom : L.raw.base+L.raw.size<2^w
  widths : DescentTerminalDenseHeaderRAM.Fits L.header w S.headerRows

attribute [local irreducible] Procedure.Exec CheapCode

theorem exec_all (fits : Room S L w) (m : Memory w) :
    (program (w:=w) S L).Exec m (finalMem S L m) (time S L) ∧ CheapCode (program (w:=w) S L) := by
  have e:=flagged_exec (e:=S.exteriors) (j:=S.headBits) (r:=S.restBits) (t:=S.bitLanes)
    L.exterior m fits.frame
  have f:=fits.publicFit
  have expr : (DescentTerminalPublicWordRAM.row L.public S.publicRows).Fits w L.output.base := by
    simp only [DescentTerminalPublicWordRAM.row,Expr.Fits,
      f L.public.portAt (by simp [DescentTerminalPublicWordRAM.all]),
      f L.public.lowAt (by simp [DescentTerminalPublicWordRAM.all]),
      f L.public.slab (by simp [DescentTerminalPublicWordRAM.all]),
      f L.public.high (by simp [DescentTerminalPublicWordRAM.all]),
      f L.public.slabBase (by simp [DescentTerminalPublicWordRAM.all]),
      f L.public.highBase (by simp [DescentTerminalPublicWordRAM.all]),
      f L.public.phase (by simp [DescentTerminalPublicWordRAM.all]),and_self]
  have v : (pub).Exec (exterior S L m) (exteriorRows S L m) (4+(S.publicRows+2)*(2*53+4)) ∧
      CheapCode (pub) :=
    ⟨@scan_exec w L.output.base (S.publicRows+2) (DescentTerminalPublicWordRAM.row L.public S.publicRows)
      (exterior S L m) expr fits.publicRoom,
      @DescentTerminalPublicWordRAM.cheap w L.output.base S.publicRows L.public⟩
  have g:=DescentTerminalRawJoin.run (rows:=S.rawRows) (publicRows:=S.publicRows)
    L.candidate L.output L.raw (exteriorRows S L m) fits.candidate fits.published fits.rawRoom
  have h:=DescentTerminalDenseHeaderRAM.exec_any L.header (file S L m) fits.widths
  unfold program time finalMem
  exact exec_cheap_seq (exec_cheap_seq (exec_cheap_seq e v) g) h

theorem clock :
    time S L≤400+500*E+110*S.publicRows+84*L.raw.size+300*S.headerRows := by
  have shapeWork : (DescentTerminalRawJoin.load S.rawRows S.publicRows L.candidate L.output).work=30:=rfl
  have h:=DescentTerminalDenseHeaderRAM.linear_cost S.headerRows L.header
  have g:=Nat.mul_le_mul_left L.raw.size (show 2*(DescentTerminalRawJoin.load S.rawRows S.publicRows L.candidate L.output).work+4≤84 by omega)
  unfold time
  omega

end
end Hierarchy.DescentTerminalDataPlane

end OAI
