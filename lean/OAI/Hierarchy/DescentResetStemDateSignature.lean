import OAI.Hierarchy.DescentResetStemProjected

namespace OAI
/-! # Comparing the public native stem programs at two presentations of a date -/
namespace Hierarchy.DescentResetStemDateSignature
open DescentResetStemPackedIssue.Mixed DescentResetStemIncidence DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

/-- All dimensions, public code, and physical sources of the projected issuer.
Its two initial addresses can be chosen after the job has been assembled. -/
structure StemJob where
  D : ℕ
  f : ℕ
  b : ℕ
  K : ℕ
  prev : ℕ
  H : ℕ
  groups : ℕ
  blocks : ℕ
  M₀ : ℕ
  M : ℕ
  Q : ℕ
  parse : DescentResetStemKey.Decoder D f
  side : Fin Q → Bool
  src : Fin Q → Fin (D+2) → Expr
  ports : Ports (2*K)

namespace StemJob

def program (s : StemJob) (base ptr w : ℕ) :=
  Projected.program (K:=s.K) base ptr s.b s.prev s.H s.groups s.blocks s.M₀ s.M s.parse s.side s.src s.ports w

def ticks (s : StemJob) (base ptr w : ℕ) :=
  Projected.ticks (K:=s.K) base ptr s.b s.prev s.H s.groups s.blocks s.M₀ s.M s.parse s.side s.src s.ports w

def image {w : ℕ} (s : StemJob) (base ptr : ℕ) (m : Memory w) :=
  Projected.image (K:=s.K) base ptr s.b s.prev s.H s.groups s.blocks s.M₀ s.M s.parse s.side s.src s.ports m

def extent (s : StemJob) (base ptr : ℕ) :=
  Projected.extent base ptr s.D s.f s.b s.K s.prev s.H s.groups s.blocks s.M₀ s.M s.Q

def outputBase (s : StemJob) (base ptr : ℕ) :=
  let cut:=Projected.splitAt base s.Q s.D s.prev s.groups s.blocks s.f s.M₀ s.M
  (plan cut ptr s.K s.H).out s.D s.f (s.b*7) s.K s.M s.prev s.H s.groups (s.blocks*s.Q)

def wordAddress (s : StemJob) (base ptr : ℕ) (x : Fin s.blocks) (q : Fin s.Q) (p : Row s.H s.groups s.M) :=
  s.outputBase base ptr+(finProdFinEquiv (x,q)).val*(s.H*chunks s.groups s.M)+(row s.H s.groups s.M p).val

theorem eq_of_fields (s t : StemJob) (degree : s.D=t.D) (field : s.f=t.f) (bits : s.b=t.b)
    (keys : s.K=t.K) (old : s.prev=t.prev) (hosts : s.H=t.H) (groups : s.groups=t.groups)
    (blocks : s.blocks=t.blocks) (prevPitch : s.M₀=t.M₀) (pitch : s.M=t.M) (columns : s.Q=t.Q)
    (parser : HEq s.parse t.parse) (sign : HEq s.side t.side) (source : HEq s.src t.src)
    (port : HEq s.ports t.ports) : s=t := by
  cases s
  cases t
  cases degree
  cases field
  cases bits
  cases keys
  cases old
  cases hosts
  cases groups
  cases blocks
  cases prevPitch
  cases pitch
  cases columns
  cases eq_of_heq parser
  cases eq_of_heq sign
  cases eq_of_heq source
  cases eq_of_heq port
  rfl

theorem wordAddress_eq {s t : StemJob} (same : s=t) (base ptr : ℕ)
    {x : Fin s.blocks} {y : Fin t.blocks} {j : Fin s.Q} {k : Fin t.Q}
    {p : Row s.H s.groups s.M} {r : Row t.H t.groups t.M}
    (block : x.val=y.val) (col : j.val=k.val)
    (offset : (row s.H s.groups s.M p).val=(row t.H t.groups t.M r).val) :
    s.wordAddress base ptr x j p=t.wordAddress base ptr y k r := by
  cases same
  unfold wordAddress
  rw [Fin.ext block,Fin.ext col,offset]

end StemJob
end
end Hierarchy.DescentResetStemDateSignature

end OAI
