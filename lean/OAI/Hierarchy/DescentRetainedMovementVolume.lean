import OAI.Hierarchy.DescentRetainedMoveTariff
import OAI.Hierarchy.DescentOrdinaryOverlapReserve

namespace OAI
/-! # The retained reset shuffle pays for packed rows and one half-word table allowance -/
namespace Hierarchy.DescentResetRetainedSetup.Layout
open DescentSIMDLookup DescentSIMDLookup.Overlap DescentGLNielsen DescentGLControlCode DescentGLPacked.BankImage
noncomputable section
variable (v : Layout)

def halfLiteral (h : ℕ) := 2*(h+1)^2*2^(h/2)

/-- Four actual packed rasters, old and new pitch on either side of the matrix, and
the native shuffle rows. The host-free high slice also bounds the printed switches. -/
def movementMass (h : ℕ) := 1+halfLiteral h+2^v.high+v.rowCount+
    Overlap.rows v.hosts v.groups v.previousLanes+Overlap.rows v.hosts v.groups v.gatherLanes+
    Overlap.rows v.hosts v.grouped v.matrixLanes+Overlap.rows v.hosts v.grouped v.decodedLanes

structure MovementAperture (h : ℕ) : Prop where
  previous : v.wholeWord*v.previousLanes≤h/2
  gather : v.wholeWord*v.gatherLanes≤h/2
  joined : SignedFields.joinWidth v.bits v.blocks*v.gatherLanes≤h/2
  matrix : (v.bits+v.bits)*2^v.low≤h/2
  control : (v.high+v.low)*(v.high+v.low)≤h/2
  strip : v.stripWord*v.matrixLanes≤h/2
  oldPitch : v.previousLanes≤h
  gatherPitch : v.gatherLanes≤h
  matPitch : v.matrixLanes≤h
  newPitch : v.decodedLanes≤h

/-- Linear in the four volume variables. All multiplicative coefficients are local
dimensions or the number of elementary row operations. -/
def literalLinear (n d channels root high data one : ℕ) :=
  4*((1+n)*root+n*one+d*high+one)+2*(channels*data+one)+n*one+
    (7*n+1)*(2*(channels*data+one)+root)

def computeLinear (n channels cost printed data one : ℕ) :=
  (8*one+10*printed)+((4*one+channels*(4*one+data*(2*cost+4)))+
    ((4*one+n*(2*19+4)*one)+(4*one+n*(4*one+channels*data*(2*110+4)))))+
  7*(15*(printed+2*one)+((15*one+channels*(11+4*cost)*one)+
    ((11+4*19)*one+(15*one+n*(11+4*110)*one))))

def glUnits :=
  let d:=v.high+v.low
  let n:=(schedule d).length
  computeLinear n v.channels v.retainedFieldWork (literalLinear n d v.channels 1 1 1 1) 1 1

theorem gl_volume (floor w h : ℕ) (ap : v.MovementAperture h) :
    v.glCost floor w≤v.glUnits*v.movementMass h :=by
  let d:=v.high+v.low
  let n:=(schedule d).length
  let mass:=v.movementMass h
  have highPos : 0 < (2:ℕ)^v.high := Nat.two_pow_pos _
  let lits:=literalLinear n d v.channels 1 1 1 1
  have one : 1≤ mass:=by dsimp [mass,movementMass];omega
  have pow : 2^(h/2)≤halfLiteral h:=Nat.le_mul_of_pos_left _ (by positivity)
  have root : 2^(h/2)≤ mass:=by dsimp [mass,movementMass];omega
  have hi : 2^v.high≤ mass:=by dsimp [mass,movementMass];omega
  have data : v.rowCount≤ mass:=by dsimp [mass,movementMass];omega
  have bound := Dated.paid_extent (v.matrix floor) (v.channels*v.hosts) v.high v.low v.bits h ap.matrix ap.control
  have last : v.mixed floor≤v.matrix floor+literalLinear n d v.channels (2^(h/2)) (2^v.high) v.rowCount 1:=by
    simpa only [mixed,SignedFields.stop,literalLinear,Count,n,d,rowCount,Nat.mul_one,Nat.mul_assoc,Nat.add_assoc] using bound
  have printed : v.literalCount floor w≤lits*mass:=calc
    _ ≤ v.mixed floor-v.matrix floor :=v.literalCount_le floor w
    _ ≤ literalLinear n d v.channels (2^(h/2)) (2^v.high) v.rowCount 1 :=by omega
    _ ≤ literalLinear n d v.channels mass mass mass mass :=by unfold literalLinear;gcongr
    _ = lits*mass :=by dsimp [lits,literalLinear];ring
  calc
    v.glCost floor w=computeLinear n v.channels v.retainedFieldWork (v.literalCount floor w) v.rowCount 1:=by
      simp only [glCost,computeLinear,d,n,rowCount,Nat.mul_one,Nat.mul_assoc]
    _ ≤ computeLinear n v.channels v.retainedFieldWork (lits*mass) mass mass:=by unfold computeLinear;gcongr
    _ = v.glUnits*mass:=by dsimp [computeLinear,glUnits,lits,d,n];ring

private theorem scaled_mount {q units mass : ℕ} (pages : q≤units*mass) (one : 1≤ mass) :
    mountFee q≤ mountFee units*mass:=calc
  _ ≤ 4*mass+10*(units*mass)+7*(15*(units*mass+mass)):=by
    unfold mountFee
    have four : 4≤4*mass:=Nat.le_mul_of_pos_right _ one
    gcongr
  _ = _ :=by unfold mountFee;ring

private theorem scaled_strip {H G A B bits h mass : ℕ} (old : A≤h) (new_ : B≤h) (bitsFit : bits*A≤h/2)
    (oldRows : Overlap.rows H G A≤ mass) (newRows : Overlap.rows H G B≤ mass) (tabs : halfLiteral h≤ mass) (one : 1≤ mass) :
    stripCharge H G A B bits≤8192*mass:=by
  have paid:=(half_pages h G A B bits old new_ bitsFit).trans tabs
  unfold stripCharge
  omega

def movementUnits:=109+v.sources*8192+mountFee v.previousNodes+mountFee (2*v.blocks)+
  v.glUnits+(109+v.channels*8192)

theorem movement_volume (floor w h : ℕ) (ap : v.MovementAperture h) :
    v.movementFee floor w≤v.movementUnits*v.movementMass h :=by
  let mass:=v.movementMass h
  have highPos : 0 < (2:ℕ)^v.high := Nat.two_pow_pos _
  have one : 1≤ mass:=by dsimp [mass,movementMass];omega
  have unit : 109≤109*mass:=Nat.le_mul_of_pos_right _ one
  have tables : halfLiteral h≤ mass:=by dsimp [mass,movementMass];omega
  have root : 2^(h/2)≤ mass:=((Nat.le_mul_of_pos_left _ (by positivity) :
    2^(h/2)≤2*(h+1)^2*2^(h/2))).trans tables
  have digits : mountFee (v.previousNodes*2^(v.wholeWord*v.gatherLanes))≤ mountFee v.previousNodes*mass:=
    scaled_mount (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) ap.gather).trans root)) one
  have joint : mountFee (v.blocks*(2*2^(SignedFields.joinWidth v.bits v.blocks*v.gatherLanes)))≤ mountFee (2*v.blocks)*mass:=by
    apply scaled_mount _ one
    calc _ ≤ v.blocks*(2*mass):=by gcongr;exact (Nat.pow_le_pow_right (by decide) ap.joined).trans root
         _ = _ :=by ring
  have pre:=scaled_strip (H:=v.hosts) (G:=v.groups) ap.oldPitch ap.gatherPitch ap.previous
    (mass:=mass) (by dsimp [mass,movementMass];omega) (by dsimp [mass,movementMass];omega) tables one
  have post:=scaled_strip (H:=v.hosts) (G:=v.grouped) ap.matPitch ap.newPitch ap.strip
    (mass:=mass) (by dsimp [mass,movementMass];omega) (by dsimp [mass,movementMass];omega) tables one
  have gl:=v.gl_volume floor w h ap
  calc
    _ ≤ (109*mass+v.sources*(8192*mass))+mountFee v.previousNodes*mass+mountFee (2*v.blocks)*mass+
        v.glUnits*mass+(109*mass+v.channels*(8192*mass)):=by unfold movementFee;gcongr
    _ = _ :=by unfold movementUnits;ring

end
end Hierarchy.DescentResetRetainedSetup.Layout

end OAI
