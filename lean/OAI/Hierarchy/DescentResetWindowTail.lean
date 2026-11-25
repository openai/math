import OAI.Hierarchy.DescentResetFieldReceipt

namespace OAI
/-! # Shared reset-field formatting and complete signed-panel publication at a fixed numeric date -/
namespace Hierarchy.DescentResetWindowTail
open DescentSIMDLookup DescentPackedColony DescentNextSignedWindow DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {X K H G b M w : ℕ}

def next (base b M : ℕ):=DescentResetFieldAssembler.endAddress base b M
def endAddress (base X cap b M H G : ℕ):=Native.All.endAddress (next base b M) X cap b M H G
def «fields» (base b M cap : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr)
    (x : Fin X) (_ : Fin (2*cap)):=DescentResetFieldAssembler.fields base b M header rank x
def program (base X D cap b M H G w : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) :=
  (DescentResetFieldAssembler.program base b M w).seq
    (Native.All.program (next base b M) X D cap b M H G w (DescentResetWindowTail.fields base b M cap header rank))
def memory (base X D cap b M H G : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) (m : Memory w) :=
  Native.All.memory (next base b M) X D cap b M H G (DescentResetWindowTail.fields base b M cap header rank) (DescentResetFieldAssembler.memory base b M m)
def time (base X D cap b M H G : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) :=
  4+10*(32*2^(DescentResetFieldAssembler.width b M))+Native.All.time (next base b M) X D cap b M H G (DescentResetWindowTail.fields base b M cap header rank)
def page (base X cap b M H G : ℕ) (x : Fin X) (j : Fin (2*cap)):=Native.All.page (next base b M) X cap b M H G x j

theorem lower (base X cap b M H G : ℕ) : next base b M≤endAddress base X cap b M H G:=by
  unfold endAddress Native.All.endAddress
  omega

theorem any (base X D cap b M H G : ℕ) (header : Fin X→Fin K→Expr) (rank : Fin X→Fin 3→Fin K→Expr) (m : Memory w)
    (early : ∀x j,(header x j).Fits w base) (prior : ∀x p j,(rank x p j).Fits w base)
    (space : endAddress base X cap b M H G<2^w) :
    let done:=memory base X D cap b M H G header rank m
    (program base X D cap b M H G w header rank).Exec m done (time base X D cap b M H G header rank) ∧
    (∀a,a<base ∨ endAddress base X cap b M H G≤a→done a=m a) ∧
    CheapCode (program base X D cap b M H G w header rank) := by
  intro done
  have top:=lower base X cap b M H G
  obtain ⟨first,held,low,cheapFirst⟩:=DescentResetFieldAssembler.any base header rank m early prior (top.trans_lt space)
  obtain ⟨second,high,cheapSecond⟩:=Native.All.any (next base b M) (D:=D)
    (DescentResetWindowTail.fields base b M cap header rank) (DescentResetFieldAssembler.memory base b M m) (fun x _=>held x) space
  refine ⟨Procedure.Exec.then first second,?_,?_⟩
  · intro a ha
    rcases ha with left|right
    · exact (high a (.inl (left.trans_le (Nat.le_add_right ..)))).trans (low a (.inl left))
    · exact (high a (.inr right)).trans (low a (.inr (top.trans right)))
  · apply ProtocolRAM.cheap_seq
    · exact @cheapFirst
    · exact @cheapSecond


end
end Hierarchy.DescentResetWindowTail

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt DescentNextSignedWindow
open DescentPackedColony DescentSIMDLookup DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) {H M b bitsW : ℕ}
local notation "X" => 2^k
local notation "N" => totalLocal B
local notation "gg" => S.groupCount (i+1)
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
open DescentResetWindowTail

theorem tail_run (rack : Fin H→Option B.next.V) (base : ℕ) (header : Fin X→Fin N→Expr)
    (rank : Fin X→Fin 3→Fin N→Expr) (m : Memory bitsW)
    (early : ∀x j,(header x j).Fits bitsW base) (prior : ∀x p j,(rank x p j).Fits bitsW base)
    (source : ∀x j,Source (header x j) (fun v g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j v g)) M m)
    (offset : ∀x p j,Source (rank x p j) (actualOffset (b:=b) B rack x p j) M m)
    (small : ∀x j v g t,DescentResetFieldAssembler.digits (actualMeta B rack x j v g) t<2^b)
    (digits : max ((A).degree+1) ((A).cap+1)<2^b) (space : endAddress base X (A).cap b M H gg<2^bitsW) :
    let done:=memory base X (A).degree (A).cap b M H gg header rank m
    (program base X (A).degree (A).cap b M H gg bitsW header rank).Exec m done (time base X (A).degree (A).cap b M H gg header rank) ∧
    (∀x j,Reads (page base X (A).cap b M H gg x j) (fun v g=>DescentSignedCableCodec.encode
      ((rack v).bind (fun r=>Stage.signedPanel A ord S B.next.valid (fieldNames B) ((g,r),x) j))) M done) ∧
    (∀a,a<base ∨ endAddress base X (A).cap b M H gg≤a→done a=m a) ∧
    CheapCode (program base X (A).degree (A).cap b M H gg bitsW header rank) := by
  intro done
  let mid:=DescentResetFieldAssembler.memory base b M m
  obtain ⟨first,fits,read,low,cheapFirst⟩:=render_source B rack base header rank m early prior source offset small
    ((lower base X (A).cap b M H gg).trans_lt space)
  obtain ⟨second,found,high,cheapSecond⟩:=native_all B (fieldNames B) rack (DescentResetWindowTail.next base b M) mid
    (DescentResetFieldAssembler.fields base b M header rank) fits read digits space
  refine ⟨Procedure.Exec.then first second,found,fun a ha=>?_,?_⟩
  · have inc : base≤DescentResetWindowTail.next base b M:=Nat.le_add_right ..
    have far:=lower base X (A).cap b M H gg
    rcases ha with left|right
    · exact (high a (.inl (left.trans_le inc))).trans (low a (.inl left))
    · exact (high a (.inr right)).trans (low a (.inr (far.trans right)))
  · apply ProtocolRAM.cheap_seq
    · exact @cheapFirst
    · exact @cheapSecond

/-- After all signed panels have been printed, each sparse mixed-parent
window is still available to the individual recipe operands. -/
theorem tail_fields (rack : Fin H→Option B.next.V) (base : ℕ) (header : Fin X→Fin N→Expr)
    (rank : Fin X→Fin 3→Fin N→Expr) (m : Memory bitsW)
    (early : ∀x j,(header x j).Fits bitsW base) (prior : ∀x p j,(rank x p j).Fits bitsW base)
    (source : ∀x j,Source (header x j) (fun v g=>DescentResetFieldAssembler.raw b (actualMeta B rack x j v g)) M m)
    (offset : ∀x p j,Source (rank x p j) (actualOffset (b:=b) B rack x p j) M m)
    (small : ∀x j v g t,DescentResetFieldAssembler.digits (actualMeta B rack x j v g) t<2^b)
    (space : endAddress base X (A).cap b M H gg<2^bitsW) (x : Fin X) (j : Fin (2*N)) (f : Fin 8) :
    let expr:=DescentResetFieldAssembler.fields base b M header rank x j f
    let done:=memory base X (A).degree (A).cap b M H gg header rank m
    expr.Fits bitsW (endAddress base X (A).cap b M H gg) ∧ Source expr (fun v g=>
      (Native.fields ((rack v).bind (fun r=>candidateRows B (fieldNames B) ((g,r),x) j)) f:Cell b)) M done := by
  intro expr done
  have top:=lower base X (A).cap b M H gg
  obtain ⟨_,fits,live,_,_⟩:=render_source B rack base header rank m early prior source offset small (top.trans_lt space)
  have late:=Native.All.any (DescentResetWindowTail.next base b M) (D:=(A).degree) (DescentResetWindowTail.fields base b M (A).cap header rank)
    (DescentResetFieldAssembler.memory base b M m) (fun x _=>fits x) space
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono _ top (fits x j f),fun r=>?_⟩
  exact (ProtocolRAM.eval_below expr _ _ done (fits x j f) (fun a ha=>late.2.1 a (.inl ha))).trans (live x j f r)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
