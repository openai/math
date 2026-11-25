import OAI.Hierarchy.DescentTerminalPublicCountRAM
import OAI.Hierarchy.DescentTerminalGrainStreams
import OAI.Hierarchy.DescentTerminalDenseHeaderBoot

namespace OAI
/-! # Reached public grain counts issue the entire padded exterior-width bank -/
namespace Hierarchy.DescentTerminalPublicWidthTape
open DescentTerminalDenseHeader DescentTerminalDenseWindow DescentTerminalHeaderGroups
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalPorts DescentTerminalCableOrder
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section

section Geometry
variable {D H p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)
  (home : N.Site→Fin H) (native : N.Edge ↪ Fin (Fintype.card N.Edge)) (ext : P ↪ ℕ)
  (nodes : N.Site ↪ ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v ↪ ℕ)
  (hp:0<p) (edges:∀e,p∣N.width e) (ports:∀z,p∣bits z) (q:ℕ) (hq:0<q)
  (c:Fin H→ℕ) (given:∀i,c i=DescentTerminalExteriorHeaders.siteMass N home i/p)
local notation "stream" => DescentTerminalExteriorHeaders.stream (q:=q) (p:=p) N home native ext nodes ops
include hp edges ports hq given in
theorem passed_eq (k:ℕ) (bound:k≤H) : DescentTerminalWidthRowsRAM.passed q p c k=stream k := by
  induction k with
  | zero=>rfl
  | succ k ih=>
    have live : k < H := by omega
    let i : Fin H := ⟨k,live⟩
    rw [DescentTerminalWidthRowsRAM.passed_add q p c i, ih (by omega)]
    simp only [DescentTerminalExteriorHeaders.stream, dite_eq_left live, given i]
    exact congrArg (fun cells => stream k ++ cells)
      (DescentTerminalGrainProfiles.public_rows N home native ext nodes ops hp edges ports q hq i).symm

include hp edges ports hq given in
theorem tape_eq : DescentTerminalWidthRowsRAM.tape q p c=stream H := by
  simpa only [DescentTerminalWidthRowsRAM.passed_all] using
    passed_eq N home native ext nodes ops hp edges ports q hq c given H le_rfl
end Geometry

structure Shape where
  base : ℕ
  maxCohorts : ℕ
  H : ℕ
  rows : ℕ
  rate : ℕ
  old : Bank

namespace Shape
variable (S : Shape)
def scaleOut := DescentTerminalPublicCountRAM.output S.base S.maxCohorts S.H
def widthLayout : DescentTerminalWidthRowsRAM.Layout :=
  ⟨DescentTerminalPublicCountRAM.stop S.base S.maxCohorts S.H,S.H,S.rows,S.maxCohorts*S.rate,S.scaleOut⟩
def program (w q p : ℕ) :=
  (DescentTerminalPublicCountRAM.program S.base S.maxCohorts S.H S.old S.rate w).seq (S.widthLayout.program q p w)
def clocks (q p : ℕ) := DescentTerminalPublicCountRAM.clocks S.base S.maxCohorts S.H S.old+S.widthLayout.clocks q p
def scaled {w : ℕ} (m : Memory w) := DescentTerminalPublicCountRAM.finalMem S.base S.maxCohorts S.H S.old S.rate m
def lastMem (q p : ℕ) {w : ℕ} (m : Memory w) := S.widthLayout.finalMem q p w (S.scaled m)
theorem names (q p w : ℕ) : DescentStaticWordColumn.names (S.program w q p) =
    15*((DescentTerminalPublicCountRAM.lut S.base S.maxCohorts).size+1)+59+
      DescentStaticWordColumn.names (S.widthLayout.program q p w) := by
  rw [program,DescentStaticWordColumn.names_seq,DescentTerminalPublicCountRAM.names]
variable {w : ℕ} (q p : ℕ) (m : Memory w) (src:S.old.Fits w S.base) (room:S.widthLayout.stop<2^w)
include room in
theorem scale_space : S.widthLayout.origin<2^w := by
  change S.widthLayout.origin+S.widthLayout.entries+S.widthLayout.prefix.size+S.widthLayout.output.size+1+S.widthLayout.groups+S.widthLayout.groups<2^w at room
  omega
include src room in
theorem any : (S.program w q p).Exec m (S.lastMem q p m) (S.clocks q p) ∧ CheapCode (S.program w q p) := by
  have small:=S.scale_space room
  have ok:=DescentTerminalPublicCountRAM.bank_fits S.base S.maxCohorts S.H small
  have a:=DescentTerminalPublicCountRAM.any S.base S.maxCohorts S.H S.old S.rate m src small
  have b:=S.widthLayout.exec_any q p w (S.scaled m) ok room
  let countProgram := DescentTerminalPublicCountRAM.program S.base S.maxCohorts S.H S.old S.rate w
  let widthProgram := S.widthLayout.program q p w
  exact ⟨@Procedure.Exec.then w countProgram widthProgram m (S.scaled m) (S.lastMem q p m)
      _ _ (@a.1) (@b.1), @cheap_seq w countProgram widthProgram (@a.2) (@b.2)⟩

variable (counts : Fin S.H→ℕ) (cap : ∀i,counts i≤S.maxCohorts)
    (oldRoom:S.H≤S.old.size) (oldRead:∀i:Fin S.H,m (S.old.base+i.val)=(counts i:Word w))
local notation "flat" => DescentTerminalWidthRowsRAM.tape q p (fun i=>counts i*S.rate)

include src room cap oldRoom oldRead in
theorem widths (nFixed:(DescentTerminalWidthRowsRAM.tape q p (fun i => counts i*S.rate)).length≤S.rows) :
    ∀i : Fin S.rows,S.widthLayout.output.read (S.lastMem q p m) (i.val:Word w)=
      ((encode q p (padded flat i)).val:Word w) := by
  have small:=S.scale_space room
  have ok:=DescentTerminalPublicCountRAM.bank_fits S.base S.maxCohorts S.H small
  have got:=DescentTerminalPublicCountRAM.count_read S.base S.maxCohorts S.H S.old S.rate m src small counts cap oldRoom oldRead
  exact (DescentTerminalWidthRowsRAM.run S.widthLayout q p (fun i=>counts i*S.rate) (S.scaled m)
    (fun i=>Nat.mul_le_mul_right _ (cap i)) nFixed ok (Nat.le_pow_clog (by decide) _) room got).2.2.1

include room in
theorem before (j : ℕ) (early : j<S.base) :
    S.lastMem q p m j=m j := by
  have small:=S.scale_space room
  have ok:=DescentTerminalPublicCountRAM.bank_fits S.base S.maxCohorts S.H small
  have lo:S.base≤S.widthLayout.origin:=by
    change S.base≤S.base+(DescentTerminalPublicCountRAM.lut S.base S.maxCohorts).size+S.scaleOut.size
    omega
  exact (S.widthLayout.frame_any q p w _ ok room j (.inl (early.trans_le lo))).trans
    (DescentTerminalPublicCountRAM.frame S.base S.maxCohorts S.H S.old S.rate m j (.inl early))

include src room cap oldRoom oldRead in
theorem exterior (nFixed:(DescentTerminalWidthRowsRAM.tape q p (fun i => counts i*S.rate)).length≤S.rows) (pos:0<q*p)
    (rom : ℕ) (rem whole index control : Bank)
    (lower:rom+DescentTerminalDenseHeaderBoot.extent q p≤S.base)
    (kept:∀j<DescentTerminalDenseHeaderBoot.extent q p,m (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j) :
    DescentTerminalDenseHeaderRAM.Reads
      (DescentTerminalDenseHeaderBoot.layout q p rom S.widthLayout.output rem whole index control)
      (padded (n:=S.rows) flat) (S.lastMem q p m) := by
  have lo:S.base≤S.widthLayout.origin:=by
    change S.base≤S.base+(DescentTerminalPublicCountRAM.lut S.base S.maxCohorts).size+S.scaleOut.size
    omega
  exact DescentTerminalDenseHeaderBoot.reads rom _ _ _ _ _ _ _ pos (lower.trans_lt (lo.trans_lt (S.scale_space room)))
    (S.widths q p m src room counts cap oldRoom oldRead nFixed)
    (fun j hj=>(S.before q p m room _ (by omega)).trans (kept j hj))

end Shape
end
end Hierarchy.DescentTerminalPublicWidthTape

end OAI
