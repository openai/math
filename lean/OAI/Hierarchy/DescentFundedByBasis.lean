import OAI.Hierarchy.DescentFundedIssuedValues
import OAI.Hierarchy.DescentFundedMixerReturn

namespace OAI
/-! # Reindexing the actual pre-reset paid and signed channels by their retained basis -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentGL DescentColonies DescentPaidResidentCount DescentPaidResidentCount.Reset
open DescentDenseHostOrder DescentSIMDLookup DescentPackedZip DescentFundedCensus
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames DescentPlainTerminal.Suffix DescentIssuedFallbackPanel
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {cap:Reached W G q ε S k i z D wire hist} (B:ClosedReset cap ctl)
  {b H M w fBits header field wide : ℕ} (oldRoom:Fintype.card cap.V≤H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => cap.placement
local notation "host" => cap.vertex.trans (Fin.castLEEmb oldRoom)
local notation "cc" => (T).commonDepth
local notation "dep" => GroupStage.depthBound D n f g
local notation "relative" => ((Z).k-cc)
local notation "dim" => (S.groupWidth k tail i+k)
local notation "small" => (dim-cc)
local notation "pool" => DescentDenseHostOrder.roster (Z).graph relative dep
local notation "L" => 2^small
local notation "digits" => S.resetInputDigits ctl.base ctl.radix i
local notation "fit" => B.frame.enough.trans (Nat.sub_le ..)
local notation "sig" => DescentSignedCableCodec.width (A).degree (A).cap
local notation "vv" => AtlasValues (Z).n relative (pool).card H (2^cc) b (A).degree (A).cap field header
local notation "v₀" t => B.frame.host.symm (((T).code t).1)
local notation "hi₀" t => (Z).rootBlock T (.inr t)
local notation "lit" => Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom)
local notation "price" => Census.count A (Equiv.refl _) host b
local notation "pKey" => DescentResetHostSize.Code relative×Option (Fin (2^(Z).n))
local notation "rootWidth" => field*DescentFallbackPeriod.inputCount (A).degree (2^relative) (A).cap (Z).n relative

/-- The same paid row has two equivalent descriptions. One splits the
actual saved pre-permutation address into a public group and block, the
other applies the exact resetInputDigits from the reached schedule. -/
def oldByBasis {d₀ : ℕ} (eqn : 2^d₀=S.groupCount i*2^k) (lo : cc≤d₀)
    (μ : DescentGL.Layout d₀) (v : Fin H) (hi : Block cc) : Cell (b*2^(d₀-cc)) :=
  encode b _ fun l=>let addr:=Fin.cast eqn ((rearrange μ).symm (join lo hi l))
    let ix : Fin (S.groupCount i)×Block k:=finProdFinEquiv.symm addr
    price v ix.1 ix.2

theorem oldByBasis_eq {d₀ : ℕ} (eqn : 2^d₀=S.groupCount i*2^k) (lo : cc≤d₀)
    (μ : DescentGL.Layout d₀) (dimension : d₀=dim) (basis : HEq μ B.frame.basis)
    (v : Fin H) (hi : Block cc) :
    HEq (oldByBasis (b:=b) B oldRoom eqn lo μ v hi) (ownOld (b:=b) B oldRoom v hi) :=by
  subst d₀
  cases eq_of_heq basis
  rfl

theorem source_equivalent {H₀ G₀ a a' : ℕ} (e : Expr) (m : Memory w)
    (eqw : a=a') (x : Fin H₀→Fin G₀→Cell a) (y : Fin H₀→Fin G₀→Cell a')
    (read : ∀h j,HEq (x h j) (y h j)) (origin : Source e x M m) : Source e y M m :=by
  subst a'
  have same:x=y:=funext fun h=>funext fun j=>eq_of_heq (read h j)
  rwa [←same]

variable (high low oldLanes gatherLanes : ℕ)
local notation "s" => (⟨H,S.groupCount i,2^k,oldLanes,gatherLanes,b,high,low,cc,(A).degree,(A).cap,M⟩:Setup)

theorem primary_return (e : Expr) (m : Memory w) (μ : DescentGL.Layout (high+low))
    (axes : 2^(high+low)=S.groupCount i*2^k) (short : cc≤high+low) (dimEq : high+low=dim)
    (basis : HEq μ B.frame.basis)
    (input : Source e ((s).lowData (fun x v g=>price v g x) axes short μ) M m) :
    Source e (ownOld (b:=b) B oldRoom) M m :=
  source_equivalent e m (by rw [dimEq]) _ _
    (oldByBasis_eq B oldRoom axes short μ dimEq basis) input

/-- Signed arrivals use the identical low index as the saved funded cube.
The equality casts only the actual low index before reading a chip. -/
theorem relay_return (e : Expr) (m : Memory w) {d₀ : ℕ} (dimEq : d₀=dim)
    (chips : Fin (2*(A).cap)→Fin H→Block cc→Fin (2^(d₀-cc))→Cell sig)
    (real : Fin (2*(A).cap)→Fin H→Block cc→Fin L→Cell sig)
    (agree : ∀j h g l,chips j h g l=real j h g (Fin.cast (by rw [dimEq]) l))
    (input : Source e (fun h g=>encode b (2^(d₀-cc)) (fun l=>(Arrivals.count chips h g l:ℕ))) M m) :
    Source e (ownArrivals (b:=b) B real) M m :=by
  subst d₀
  have eqn:chips=real:=funext fun j=>funext fun h=>funext fun g=>funext fun l=>agree j h g l
  subst real
  exact input

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
