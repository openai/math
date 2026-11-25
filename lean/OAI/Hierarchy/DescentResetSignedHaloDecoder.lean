import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentStaticUnary

namespace OAI
/-! # One immutable small ROM projects a previous direction to its old source slot -/
namespace Hierarchy.DescentResetSignedHaloMatrix
open DescentSharedCableNames.Stage DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def slot {D cap : ℕ} (r : Live D cap) : Fin (D+1):=if r.target then r.neighbor.castSucc else Fin.last D
def askedField (D cap b a : ℕ) (v : Cell b) (_ : Cell 0) : Cell a:=((DescentSignedCableCodec.decode D cap (v.val:Cell (DescentSignedCableCodec.width D cap))).elim 0 (fun r=>(slot r).val+1):ℕ)
def decoder (D cap b a M root : ℕ) : Tables :=joined (binary (askedField D cap b a) M) (b*M) root id
def query (D cap b a M root : ℕ) (e : Expr) :=(decoder D cap b a M root).read e (.lit 0)

theorem decoder_run {H G M w : ℕ} (D cap b a root : ℕ) (m : Memory w) (room : root+2*2^(b*M)<2^w) :
    let law:=askedField D cap b a
    let P:=binary law M
    let dst:=after P (b*M) root m
    let top:=root+2*2^(b*M)
    (mount P (b*M) w root).Exec m dst (4+10*(2*2^(b*M))) ∧
      (∀src : Expr,∀v : Fin H→Fin G→Cell b,src.Fits w root→Source src v M m→
        (query D cap b a M root src).Fits w top ∧ Source (query D cap b a M root src) (fun h g=>law (v h g) 0) M dst) ∧
      (∀u,u<root ∨ top≤u→dst u=m u) ∧ CheapCode (mount P (b*M) w root):=by
  have empty : askedField D cap b a 0 0=0:=by
    have zero : DescentSignedCableCodec.decode D cap 0=none:=by
      rw [←DescentSignedCableCodec.empty]
      exact DescentSignedCableCodec.decode_encode none
    simp [askedField,zero]
  exact DescentStaticUnary.read (askedField D cap b a) empty root m room

end
end Hierarchy.DescentResetSignedHaloMatrix

end OAI
