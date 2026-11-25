import OAI.ThreeFlat.Diagonal.BoundaryAddress
import OAI.ThreeFlat.Diagonal.ApproximateNetwork

namespace OAI
/-! # Word addresses for every field of one approximating block -/

namespace ThreeFlat.Diagonal.ApproximateAddress

open ApproximatePort BoundaryWire RAM.BitLayout

variable {chunks a t n d : ℕ}

/-- Numeric address of one endpoint bit. A public endpoint is adjacent to the
advice prefix, and an internal endpoint occupies its unique hidden-state slot. -/
def endpoint (chunks a t d : ℕ) (right : Bool) (i bit : ℕ) : ℕ :=
  if right then
    if i = t then 2+d+stateWidth chunks a+bit
    else hiddenBase (pinWidth chunks a d) + i*stateWidth chunks a+bit
  else
    if i = 0 then 2+d+bit
    else hiddenBase (pinWidth chunks a d)+(i-1)*stateWidth chunks a+bit

def interior (chunks a t n d : ℕ) (i k bit : ℕ) :=
  hiddenBase (pinWidth chunks a d) + t*stateWidth chunks a + i*(n*a) + k*a + bit

def chunk (chunks a : ℕ) (half : Bool) (slot bit : ℕ) : ℕ :=
  (if half then chunks*a else 0) + slot*a + bit

/-- Address of a collapse pin after its port tag and operands have been decoded. -/
def physical (slot : Fin (n+1) → Fin chunks) (active : Bool) (i : Fin (t+1)) :
    ApproximatePort (Fin chunks) d n a → ℕ
  | .publicBit j => 2+j.val
  | .literal b => b.toNat
  | .leftChunk k j => endpoint chunks a t d false i.val (chunk chunks a active (slot k).val j.val)
  | .rightChunk k j => endpoint chunks a t d true i.val (chunk chunks a active (slot k).val j.val)
  | .leftAux k j =>
    if k.val = 0 then endpoint chunks a t d false i.val (chunks*a+chunks*a+j.val)
    else interior chunks a t n d i.val (k.val-1) j.val
  | .rightAux k j =>
    if k.val = n then endpoint chunks a t d true i.val (chunks*a+chunks*a+j.val)
    else interior chunks a t n d i.val k.val j.val
  | .leftCatalyst k j => endpoint chunks a t d false i.val (chunk chunks a (!active) k.val j.val)
  | .rightCatalyst k j => endpoint chunks a t d true i.val (chunk chunks a (!active) k.val j.val)

variable {q : ℕ}

theorem input_addr (select : Fin (t+1) → Fin q → ApproximatePort (Fin chunks) d n a)
    (slot : Fin (t+1) → Fin (n+1) → Fin chunks) (active : Fin (t+1) → Bool)
    (i : Fin (t+1)) (j : Fin q) :
    sourceAddress (ApproximateNetwork.input select slot active i j) =
      physical (slot i) (active i) i (select i j) := by
  unfold ApproximateNetwork.input
  cases h : select i j with
  | publicBit j => exact publicSource_addr j
  | literal b => rfl
  | leftChunk k b | rightChunk k b | leftCatalyst k b | rightCatalyst k b =>
    simp [route, physical, ApproximateNetwork.stateWires, oldSource_addr, newSource_addr,
      chunkSite_val, chunk, endpoint]
  | leftAux k b =>
    refine Fin.cases ?_ (fun s => ?_) k
    · simp [route, physical, ApproximateNetwork.stateWires, oldSource_addr, auxSite_val, endpoint]
    · simp [route, physical, interiorSource_addr, interior]
  | rightAux k b =>
    refine Fin.lastCases ?_ (fun s => ?_) k
    · simp [route, physical, ApproximateNetwork.stateWires, newSource_addr, auxSite_val, endpoint]
    · simp [route, physical, interiorSource_addr, interior, Nat.ne_of_lt s.isLt]

end ThreeFlat.Diagonal.ApproximateAddress

end OAI
