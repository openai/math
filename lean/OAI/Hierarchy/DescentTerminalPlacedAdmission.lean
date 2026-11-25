import OAI.Hierarchy.DescentTerminalPlacedFrames

namespace OAI
/-! # Seed and exterior admission in the compact high-flight layout -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentTerminalVertexFields DescentTerminalRowArena DescentExteriorShelf DescentExterior DescentGL
noncomputable section
set_option quotPrecheck false
variable {w blocks:ℕ} (S:Shape) (I:Input) (base:ℕ) (F:MaskedShelf blocks) (O:DescentPrivateExponentRAM.Banks)
local notation "A" => rowArena S I base
local notation "L" => layout S I base O
local notation "E" => S.terminal
local notation "P" => S.terminal.plane
local notation "orig" => takeOff S I base
local notation "body" => bodyPlane S I base
local notation "ext" => publicHeader S I base
local notation "stop_" => DescentTerminalDataPlane.Arena.finish P orig
local notation "j" => (P).headBits
local notation "r" => (P).restBits
local notation "t" => (P).bitLanes
local notation "e" => (P).exteriors
local notation "fl" => flagAt («j»:=j) («r»:=r) («t»:=t) («e»:=e) orig

theorem after_start {a:ℕ} (lo:a<DescentTerminalDataPlane.Arena.post P orig) :
    DescentTerminalEmitter.AfterFlights E (L).emit a := by
  have rawLo:a<(body).raw.base:=by change a<DescentTerminalDataPlane.Arena.post P orig+_;omega
  have headLo:a<DescentTerminalDataPlane.Arena.headerBase P orig:=by change a<(body).raw.base+_;omega
  have remLo:a<(body).header.rem.base:=by change a<DescentTerminalDataPlane.Arena.headerBase P orig+0*_;simpa using headLo
  have later_:a<DescentTerminalDataPlane.Arena.second P orig:=by change a<DescentTerminalDataPlane.Arena.headerBase P orig+_;omega
  have other:a<(ext).rem.base:=by change a<DescentTerminalDataPlane.Arena.second P orig+0*_;simpa using later_
  have stopLo:a<stop_:=by change a<DescentTerminalDataPlane.Arena.second P orig+_;omega
  exact ⟨lo,rawLo,remLo,DescentTerminalEmitter.Allocation.«protected» E I.indexEvents I.formatEvents stop_
    (inputs S I base) body ext I.blank stopLo other⟩

theorem actual_flags {K T:Type} (m:Memory w) (early:Earlier S I base F w)
    (space:endAddress S I base<2^w) (pos:0<w) (bits:2^j*t≤w)
    (seed:ℕ) (low:seed<(A).start) (x:Fin e→Plane j r→Fin t→Bool)
    (mix:T→Fin e→DescentGL.Layout (j+(j+r))) (decode:(K→Bool)→Option T) (z:K⊕Hidden e j r t→Bool)
    (good:m seed=0 ↔ ∃c,decode (z∘Sum.inl)=some c)
    (bank_:∀c,decode (z∘Sum.inl)=some c→Loaded orig (mix c) x (z∘Sum.inr) m) :
    (tailImage S I base F O m seed=0 ∧ tailImage S I base F O m fl=0) ↔
      ∃c,proposed decode mix x z=some c := by
  obtain ⟨p0,p1,p2,p3,p4⟩:=stages S I base
  have past:seed<orig:=low.trans_le (((A).start_le 22).trans (p0.trans p1))
  have earlySeed:=before S I base O seed (by omega)
  have rooms:=suffix_room S I base F O early space
  have previous : Suffix.events S L F ((A).mount m) seed=m seed :=
    (Suffix.early S L F ((A).mount m) rooms earlySeed.original earlySeed.slot earlySeed.page).trans ((A).mount_before m low)
  have spanPos:0<DescentExteriorShelf.span j r t e:=Nat.two_pow_pos _
  have rows:=DescentExteriorShelf.row_room j r t e
  change e*2^(j+r)≤ DescentExteriorShelf.span j r t e at rows
  have flRoom:fl<DescentTerminalDataPlane.Arena.post P orig:=by
    change orig+21*(DescentExteriorShelf.span j r t e)+2*(e*2^(j+r))<orig+24*(DescentExteriorShelf.span j r t e);omega
  have frame:=after_start S I base O (a:=fl) flRoom
  have frame0:=after_start S I base O (a:=seed) (by change seed<orig+_;omega)
  have keyBefore:DescentTerminalEmitter.BeforeKey E (L).emit seed:=by
    constructor <;> first | (change seed<orig+_;omega)
  apply DescentTerminalEmitter.accepted E (L).emit (Suffix.events S L F ((A).mount m)) rooms.issuer pos bits
    seed keyBefore frame0 frame x mix decode z
  · rw [previous];exact good
  · intro c h col addr bounded
    have above : pageEnd S I base≤(bank j r t e orig col.val).base+addr:=by
      change _≤orig+_+_;omega
    change Suffix.events S L F ((A).mount m) ((bank j r t e orig col.val).base+addr) =
      columnWords (mix c) x (z∘Sum.inr) col addr
    rw [events_after S I base F O m early space above]
    exact bank_ c h col addr bounded

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
