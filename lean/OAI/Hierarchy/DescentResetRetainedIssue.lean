import OAI.Hierarchy.DescentResetRetainedRead
import OAI.Hierarchy.DescentResetRetainedNames

namespace OAI
/-! # Reset operand source closure from the seven previous fields and primitive node records -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.PackedFlow.Channels
open DescentGL DescentColonies Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (v : DescentResetRetainedSetup.Layout)

/-- Runtime origin of every returned value. All four packed memories are the
fixed predecessor books, the saved elected basis, the single reset image,
and the same image read with the consuming slot's required lane count. -/
theorem issued (base : ℕ) (old : Fin v.sources→Bank) (saved : Bank) (mem : Memory w)
    (prior : ∀i,(old i).Fits w base) (key : saved.Fits w base) (room : v.endAddress base<2^w)
    (size : 2^(v.high+v.low)=v.groups*v.blocks) (batch : 2^v.low=v.gatherLanes*v.blocks)
    (hg : 0<v.gatherLanes) (hb : 0<v.blocks) (hp : 0<v.previousLanes)
    (cut : v.cut≤v.high+v.low) (pitch : v.matrixLanes*v.donors=2^v.low) (active : 0<v.matrixLanes)
    (pos : 0<v.decodedLanes) (L : DescentGL.Layout (v.high+v.low))
    (chosen : mem saved.base=((DescentExterior.matrixCode L).val:Word w))
    (x : v.Values) (capacity : ∀i,v.hosts*chunks v.groups v.previousLanes≤(old i).size)
    (read : ∀i,Reads (old i) (x i) v.previousLanes mem) (i : Fin v.outputs) :
    let words:=v.site (fun j=>blockValues cut (v.before size x j) L)
    Source (.lookup (v.bank base i) .row) (fun h g=>v.function i (words h g))
      v.emitLanes (v.image base old saved mem) :=by
  intro words
  obtain ⟨_,_,_,_,_,a,b,c,d⟩:=v.order base
  have end_:=a.trans (b.trans (c.trans d))
  have incoming:=v.moved_reads base old saved mem prior key (end_.trans_lt room) size batch hg hb hp cut pitch
      active L chosen x capacity read
  have physical:=v.reads base old saved mem room pos _ incoming i
  obtain ⟨fit,space⟩:=v.returned base i room
  exact source_column _ _ fit _ _ space physical

/-- At any physical recipient lane, indexing the decoded local site word by
donor, primitive and node reads exactly that original chronological bank. -/
theorem prior_digit (x : v.Values) (size : 2^(v.high+v.low)=v.groups*v.blocks)
    (cut : v.cut≤v.high+v.low) (L : DescentGL.Layout (v.high+v.low)) (h : Fin v.hosts)
    (hi : Block v.cut) (d : Fin v.donors) (n : Fin v.previousNodes) (f : Fin v.fields) :
    let z:=(rearrange L).symm (DescentIssuedFallbackPanel.join cut hi d)
    let ix:=(finProdFinEquiv.symm (Fin.cast size z) : Fin v.groups×Fin v.blocks)
    let y:=v.site (fun j=>blockValues cut (v.before size x j) L) h hi
    v.entry y d n f=DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=v.bits) n
      (x (v.sourceID f ix.2) h ix.1) :=by
  let ch : Fin v.channels := finProdFinEquiv (f,n)
  let channels : Fin v.channels → Cell v.stripWord := fun j => blockValues cut (v.before size x j) L h hi
  let donors : Fin v.donors → Cell v.bits := fun d' =>
    v.before size x ch h ((rearrange L).symm (DescentIssuedFallbackPanel.join cut hi d'))
  have first := congrFun ((encode v.stripWord v.channels).symm_apply_apply channels) ch
  have second := congrFun ((encode v.bits v.donors).symm_apply_apply donors) d
  refine (congrArg (fun w => (encode v.bits v.donors).symm w d) first).trans (second.trans ?_)
  exact congrArg (fun p : Fin v.fields × Fin v.previousNodes =>
    DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=v.bits) p.2
      (x (v.sourceID p.1 _) h _)) (finProdFinEquiv.symm_apply_apply (f,n))

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
