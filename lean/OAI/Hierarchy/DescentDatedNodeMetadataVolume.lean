import OAI.Hierarchy.DescentDatedNodeMetadataTariff

namespace OAI
/-! # Bit-level section 4.2 invoice for the funded node-metadata compiler -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
open DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentStaticWordColumn ProtocolRAM
noncomputable section
variable {K : ℕ} (v : DescentDatedNodeMetadata.Chart)

def loopUnits (R U : ℕ) :=(4+v.jobs*(4+R*(2*U+4)))+
  (4+10*(v.nodes+1)+(4+v.names*(4+R*(2*(1+18*v.nodes)+4))))
def labelUnits (U : ℕ) :=15+v.jobs*(11+4*U)+(15*(v.nodes+2)+(15+v.names*(11+4*(1+18*v.nodes))))
def inputClock :=4+10*((v.nodes+1)*2)
def inputNames :=15*((v.nodes+1)*2+1)

theorem wordInvoices (U h a b work R : ℕ) (unit : 1≤U) (lut : 2^(h/2)≤U)
    (nodeBits : (v.bits*v.nodes+v.bits)*v.lanes≤h/2)
    (countBits : max a (b+v.bits)*v.lanes≤h/2) (physical : v.rows≤R*U) :
    (4+10*v.setupWords a b+v.bodyClock work≤(v.inputClock+v.loopUnits R work)*U) ∧
    (15*(v.setupWords a b+1)+v.bodyNames work≤(v.inputNames+v.labelUnits work)*U) :=by
  have up (k : ℕ) : k≤k*U:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k unit
  have table : v.dictionary≤(v.nodes+1)*U:=Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) nodeBits).trans lut)
  have total : v.setupWords a b≤((v.nodes+1)*2)*U:=by
    change (v.nodes+1)*(2*2^(max a (b+v.bits)*v.lanes))≤_
    rw [Nat.mul_assoc (v.nodes+1) 2 U]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) countBits).trans lut))
  have body : v.bodyClock work≤v.loopUnits R work*U:=calc
    _ ≤ (4*U+v.jobs*(4*U+(R*U)*(2*work+4)))+
      (4*U+10*((v.nodes+1)*U)+(4*U+v.names*(4*U+(R*U)*(2*(1+18*v.nodes)+4)))) :=by
      unfold bodyClock;gcongr <;> first | exact up _
    _ = _:=by unfold loopUnits;ring
  have names : v.bodyNames work≤v.labelUnits work*U:=calc
    _ ≤ ((15*U)+v.jobs*((11+4*work)*U))+
      (15*((v.nodes+1)*U+1*U)+(15*U+v.names*((11+4*(1+18*v.nodes))*U))) :=by
      unfold bodyNames;gcongr <;> first | exact up _
    _ = _:=by unfold labelUnits;ring
  constructor
  · calc
      _ ≤ 4*U+10*(((v.nodes+1)*2)*U)+v.loopUnits R work*U:=by gcongr; first | exact up _
      _ = _:=by unfold inputClock;ring
  · calc
      _ ≤ 15*(((v.nodes+1)*2)*U+1*U)+v.labelUnits work*U:=by gcongr; first | exact up _
      _ = _:=by unfold inputNames;ring

private theorem charge {H G h u w ratio t n C B : ℕ} (positive : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h)
    (ticks : t≤C*Stage.DateBill.words H G h u) (labels : n≤B*Stage.DateBill.words H G h u) :
    w*t+7*n≤(2*((ratio+7)*(C+B)))*Stage.DateBill.volumeBits H G h u :=by
  let U:=Stage.DateBill.words H G h u
  have positiveH : 1≤h:=by omega
  have names : n≤B*U*h:=labels.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (B*U) positiveH)
  calc
    _ ≤ ratio*h*(C*U)+7*(B*U*h):=Nat.add_le_add (Nat.mul_le_mul bus ticks) (Nat.mul_le_mul_left 7 names)
    _ = (ratio*C+7*B)*(U*h):=by ring
    _ ≤ (ratio+7)*(C+B)*(U*h):=by apply Nat.mul_le_mul_right;simp only [Nat.add_mul,Nat.mul_add];omega
    _ ≤ (ratio+7)*(C+B)*(2*Stage.DateBill.volumeBits H G h u):=Nat.mul_le_mul_left _ (Stage.DateBill.words_bits H G h u positive wide)
    _ = _:=by ring

theorem metadataVolume (floor a b w h u q ratio R : ℕ) (paid : v.Counts) (f6 : v.Spans K)
    (positive : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h) (nodeBits : (v.bits*v.nodes+v.bits)*v.lanes≤h/2)
    (countBits : max a (b+v.bits)*v.lanes≤h/2) (physical : v.rows≤R*Stage.DateBill.words v.hosts v.groups h u)
    (cheap : ∀x,(paid x).work≤q) (cost : ∀x n j,(f6 x n j).work≤q) :
    let work:=tallyWork K q
    w*v.metadataTime floor a b paid f6+7*DescentStaticWordColumn.names (v.metadataProgram floor a b w paid f6)≤
      (2*((ratio+7)*((v.inputClock+v.loopUnits R work)+(v.inputNames+v.labelUnits work))))*Stage.DateBill.volumeBits v.hosts v.groups h u :=by
  intro work
  let U:=Stage.DateBill.words v.hosts v.groups h u
  have dir : 2^(h/2)≤U:=by dsimp [U,Stage.DateBill.words];omega
  have goal_:=v.wordInvoices U h a b work R ((Nat.two_pow_pos _).trans_le dir) dir nodeBits countBits physical
  have bill:=v.metadataPrice floor a b w q paid f6 cheap cost
  exact charge positive wide bus (bill.1.trans goal_.1) (bill.2.trans goal_.2)

theorem ordinaryVolume (floor a b w h u q ratio R : ℕ) (paid : v.Counts) (src : v.Vectors K)
    (positive : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h) (nodeBits : (v.bits*v.nodes+v.bits)*v.lanes≤h/2)
    (countBits : max a (b+v.bits)*v.lanes≤h/2) (priorBits : (b*v.nodes)*v.lanes≤h/2)
    (physical : v.rows≤R*Stage.DateBill.words v.hosts v.groups h u) (cheap : ∀x,(paid x).work≤q) :
    let work:=tallyWork K (max q 16)
    w*v.ordinaryTime floor a b paid src+7*DescentStaticWordColumn.names (v.ordinaryProgram floor a b w paid src)≤
      (2*((ratio+7)*(((4+10*v.nodes)+(v.inputClock+v.loopUnits R work))+
        (15*(v.nodes+1)+(v.inputNames+v.labelUnits work)))))*Stage.DateBill.volumeBits v.hosts v.groups h u :=by
  intro work
  let U:=Stage.DateBill.words v.hosts v.groups h u
  have dir : 2^(h/2)≤U:=by dsimp [U,Stage.DateBill.words];omega
  have pos : 1≤U:=(Nat.two_pow_pos _).trans_le dir
  have goal_:=v.wordInvoices U h a b work R pos dir nodeBits countBits physical
  have initial : v.digitWords b≤v.nodes*U:=Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) priorBits).trans dir)
  have bill:=v.ordinaryPrice floor a b w q paid src cheap
  apply charge positive wide bus
  · apply bill.1.trans
    rw [Nat.add_mul]
    apply Nat.add_le_add _ goal_.1
    calc
      _ ≤ 4*U+10*(v.nodes*U):=Nat.add_le_add (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 4 pos) (Nat.mul_le_mul_left _ initial)
      _ = _:=by ring
  · apply bill.2.trans
    rw [Nat.add_mul]
    apply Nat.add_le_add _ goal_.2
    calc
      _ ≤ 15*(v.nodes*U+U):=Nat.mul_le_mul_left _ (Nat.add_le_add initial pos)
      _ = _:=by ring

end
end Hierarchy.DescentDatedNodeMetadata.Chart

end OAI
