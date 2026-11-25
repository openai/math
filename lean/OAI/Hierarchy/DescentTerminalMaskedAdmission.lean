import OAI.Hierarchy.DescentTerminalMaskFrames
import OAI.Hierarchy.DescentTerminalEmittedCutoff

namespace OAI
/-! # Both acceptance words, field census and dead exponent survive sparse terminal issuance -/
namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentExterior DescentExteriorShelf DescentTerminalEmitter DescentTerminalVertexFields
open scoped Classical
noncomputable section
variable {w blocks:ℕ} (S:Shape) (L:Layout) (F:MaskedShelf blocks)
set_option quotPrecheck false
local notation "j" => S.terminal.plane.headBits
local notation "r" => S.terminal.plane.restBits
local notation "e" => S.terminal.plane.exteriors
local notation "t" => S.terminal.plane.bitLanes
local notation "origin" => L.emit.plane.exterior
local notation "flag" => flagAt («j»:=j) («r»:=r) («t»:=t) («e»:=e) origin

structure MaskProtected (a:ℕ) : Prop where
  «prefix» : Protected L a
  slots : a<slotBase S L
  pages : a<L.directory.texture.base

theorem mask_field (m:Memory w) (ok:Room S L w) (a:ℕ) (p:MaskProtected S L a)
    (lo:BeforeKey S.terminal L.emit a) (hi:AfterFlights S.terminal L.emit a) :
    maskResult S L F m a=m a := by
  rw [maskResult,printed_before _ _ _ ok.emit lo hi,maskEvents_original S L F m ok p.prefix p.slots p.pages]

theorem mask_dead (m:Memory w) (ok:Room S L w) (a:ℕ) (raw:Frozen L a)
    (slots:a<slotBase S L) (pages:a<L.directory.texture.base)
    (lo:BeforeKey S.terminal L.emit a) (hi:AfterFlights S.terminal L.emit a) :
    maskResult S L F m a=counted S L m a := by
  rw [maskResult,printed_before _ _ _ ok.emit lo hi,maskEvents_counted S L F m ok raw slots pages]

theorem mask_admission {A T:Type} (m:Memory w) (ok:Room S L w) (positive:0<w) (bitsFit:2^j*t≤w)
    (seed:ℕ) (keep:MaskProtected S L seed) (early:BeforeKey S.terminal L.emit seed)
    (late:AfterFlights S.terminal L.emit seed) (tail:AfterFlights S.terminal L.emit flag)
    (x:Fin e→Plane j r→Fin t→Bool) (layouts:T→Fin e→DescentGL.Layout (j+(j+r)))
    (decode:(A→Bool)→Option T) (z:A⊕Hidden e j r t→Bool)
    (first:m seed=0 ↔ ∃c,decode (z∘Sum.inl)=some c)
    (original:∀c,decode (z∘Sum.inl)=some c→Loaded origin (layouts c) x (z∘Sum.inr) m)
    («protected»:∀(col:Fin 17) (i:Fin (span j r t e)),MaskProtected S L ((bank j r t e origin col.val).base+i.val)) :
    (maskResult S L F m seed=0 ∧ maskResult S L F m flag=0) ↔ ∃c,proposed decode layouts x z=some c := by
  apply accepted S.terminal L.emit (maskEvents S L F m) ok.emit positive bitsFit seed early late tail x layouts decode z
  · rw [maskEvents_original S L F m ok keep.prefix keep.slots keep.pages];exact first
  · intro c good col i live
    let safe:=«protected» col ⟨i,live⟩
    rw [maskEvents_original S L F m ok safe.prefix safe.slots safe.pages]
    exact original c good col i live

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
