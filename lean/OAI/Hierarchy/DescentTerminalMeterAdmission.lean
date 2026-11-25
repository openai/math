import OAI.Hierarchy.DescentTerminalMeterSuffix
import OAI.Hierarchy.DescentTerminalHomeAllocation

namespace OAI
/-! # Terminal acceptance using the reached native private counter and directory -/
namespace Hierarchy.DescentTerminalCompiledPrefix.Suffix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentExterior DescentExteriorShelf DescentTerminalEmitter DescentTerminalVertexFields
open scoped Classical
noncomputable section
variable {w blocks : ℕ} (S : Shape) (L : Layout) (F : MaskedShelf blocks)
section Exterior
set_option quotPrecheck false
local notation "j" => S.terminal.plane.headBits
local notation "r" => S.terminal.plane.restBits
local notation "e" => S.terminal.plane.exteriors
local notation "t" => S.terminal.plane.bitLanes
local notation "origin" => L.emit.plane.exterior
local notation "flag" => flagAt («j»:=j) («r»:=r) («t»:=t) («e»:=e) origin

structure Early (a : ℕ) : Prop where
  original : Frozen L a
  slot : a < slotBase S L
  page : a < L.directory.texture.base

/-- Look through the actual native suffix and any earlier physical computation
that preserves the seed bit and the seventeen loaded exterior columns. -/
theorem admitted_after {A T : Type} (before m : Memory w) (room : Fits S L F w)
    (positive : 0 < w) (bitsFit : 2^j*t ≤ w) (seed : ℕ) (keep : Early S L seed)
    (lo : BeforeKey S.terminal L.emit seed) (hi : AfterFlights S.terminal L.emit seed)
    (tail : AfterFlights S.terminal L.emit flag)
    (x : Fin e→ Plane j r→ Fin t→ Bool) (layouts : T→ Fin e→ DescentGL.Layout (j+(j+r)))
    (decode : (A→ Bool)→ Option T) (z : A⊕Hidden e j r t→ Bool)
    (seedHeld : m seed=before seed) (first : before seed=0 ↔ ∃c,decode (z∘Sum.inl)=some c)
    (loaded : ∀c,decode (z∘Sum.inl)=some c→ Loaded origin (layouts c) x (z∘Sum.inr) before)
    (banks : ∀(col : Fin 17) (i : Fin (DescentExteriorShelf.span j r t e)),let a:=(bank j r t e origin col.val).base+i.val
      Early S L a ∧ m a=before a) :
    (output S L F m seed=0 ∧ output S L F m flag=0) ↔ ∃c,proposed decode layouts x z=some c := by
  apply DescentTerminalEmitter.accepted S.terminal L.emit (events S L F m) room.issuer positive bitsFit seed lo hi tail x layouts decode z
  · rw [early S L F m room keep.original keep.slot keep.page,seedHeld];exact first
  · intro c good col i live
    obtain ⟨protected_,frame⟩:=banks col ⟨i,live⟩
    exact (early S L F m room protected_.original protected_.slot protected_.page).trans
      (frame.trans (loaded c good col i live))
end Exterior

section Private
variable {Q T H N A p groups homeBlocks homes : ℕ}
local notation "capacity" => cohortSize (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (w:=p) (groups:=groups) (blocks:=homeBlocks)

/-- A separately executed pre-meter block may modify arbitrary workspace. Its
saved words remain in the real output of the subsequent home counter. -/
theorem meter_low {Q T H N A p groups homeBlocks homes : ℕ} (B : PrivateCounter.Banks (blocks:=homeBlocks))
    (header : ℕ) (before reached : Memory w) {a : ℕ} (retained : reached a=before a) (low : a < B.base) :
    let meterSize:=DescentTerminalVertexFields.cohortSize (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (w:=p)
      (groups:=groups) (blocks:=homeBlocks)
    PrivateCounter.final (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes)
      B (PrivateCounter.registers B header homes meterSize) reached a=before a :=
  (PrivateCounter.final_low (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes)
    B header reached a low).trans retained

theorem meter_registers {Q T H N A p groups homeBlocks homes : ℕ} (B : PrivateCounter.Banks (blocks:=homeBlocks))
    (O : DescentPrivateExponentRAM.Banks) (before reached : Memory w) {a : ℕ}
    (retained : reached a=before a) (low : a < B.base) (tmp : a≠O.usedBits) (dst : a≠O.deadBits) :
    PrivateCounter.final (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes)
      B O reached a=before a :=
  (PrivateCounter.final_frame (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes)
    B O reached a (.inl low) tmp dst).trans retained

/-- Concatenate the earlier native setup with the real private meter. The final
low-bank transfer applies on every candidate, regardless of source validity. -/
theorem private_prefix
    (B : PrivateCounter.Banks (blocks:=homeBlocks)) (header : ℕ) (before reached : Memory w)
    (prep : Procedure w) (fee : ℕ) (run_ : prep.Exec before reached fee) (cheap : CheapCode prep)
    (space : PrivateCounter.Room (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) B w)
    (shift : PrivateCounter.Shift (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) B.layout reached)
    (headLow : header < B.base) (enough : B.base+capacity+homes+homes+3 < 2^w) :
    let O:=PrivateCounter.registers B header homes capacity
    let pc:=PrivateCounter.machine (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) (bw:=w) B O
    let last:=PrivateCounter.final (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes) B O reached
    (prep.seq pc).Exec before last (fee+(PrivateCounter.prefixTicks homes homeBlocks capacity+(56+4*ProtocolRAMPortScale.bitWidth p))) ∧
    CheapCode (prep.seq pc) ∧ ∀a,a < B.base→ reached a=before a→ last a=before a := by
  let O:=PrivateCounter.registers B header homes capacity
  let pc:=PrivateCounter.machine (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
    (homes:=homes) (bw:=w) B O
  let last:=PrivateCounter.final (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups)
    (homes:=homes) B O reached
  let ticks:=PrivateCounter.prefixTicks homes homeBlocks capacity+(56+4*ProtocolRAMPortScale.bitWidth p)
  have run:=PrivateCounter.any (q:=Q) (t:=T) (H:=H) (N:=N) (A:=A) (p:=p) (groups:=groups) (homes:=homes)
    B O reached space shift (by omega) (PrivateCounter.registers_room (q:=Q) (t:=T) (H:=H) (N:=N)
      (A:=A) (p:=p) (groups:=groups) (homes:=homes) (bw:=w) B header headLow enough) rfl
  have pair := @ProtocolRAM.exec_cheap_seq w fee ticks prep pc before reached last ⟨@run_,@cheap⟩ run
  exact ⟨pair.1,pair.2,fun a low eqn=>meter_low (Q:=Q) (T:=T) (H:=H) (N:=N) (A:=A) (p:=p)
    (groups:=groups) (homeBlocks:=homeBlocks) (homes:=homes) B header before reached (a:=a) eqn low⟩
end Private

end
end Hierarchy.DescentTerminalCompiledPrefix.Suffix

end OAI
