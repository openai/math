import OAI.Hierarchy.DescentTerminalPrimitiveArena
import OAI.Hierarchy.DescentTerminalActorRepack
import OAI.Hierarchy.DescentTerminalPopulationPage
import OAI.Hierarchy.DescentTerminalFrozenCountBank

namespace OAI
/-! # Population and actor fields immediately after the terminal frozen roster -/
namespace Hierarchy.DescentTerminalPriorArena
open DescentSIMDLookup DescentTerminalPrimitiveArena DescentTerminalPointerDigits ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- End of all tally writes, including the vacant-host bin. -/
def afterRoster {w n H : ℕ} (shelf : DescentCensusRAM.Banks w n (H+1)) := shelf.bins + H + 1

theorem roster_histogram {w n H : ℕ} (shelf : DescentCensusRAM.Banks w n (H+1)) (base : ℕ)
    (earlier : base+H ≤ shelf.first) :
    base + pad H ≤ afterRoster shelf := by
  have a := shelf.scratch
  have b := shelf.beforeTape
  have c := shelf.beforeBins
  have d := pad_le H
  unfold afterRoster
  omega

variable (s : Shape) (groups mPaid mAct paidBits extBits actBits origin : ℕ)
local notation "popFee" => DescentTerminalPopulation.RAM.lease s.shops groups mPaid paidBits extBits origin
def pop := origin + popFee
local notation "p0" => pop s groups mPaid paidBits extBits origin
def actStart := p0 + s.rows + s.guard
local notation "o1" => actStart s groups mPaid paidBits extBits origin
local notation "actFee" => DescentTerminalActorRepack.count s.shops groups mAct actBits s.blocks o1
def actor := o1 + actFee
local notation "a1" => actor s groups mPaid mAct paidBits extBits actBits origin
def start := a1 + s.rows + pad s.shops
local notation "next" => start s groups mPaid mAct paidBits extBits actBits origin
local notation "occupied" => s.subrow a1

theorem population_at (x : Fin s.blocks) :
    DescentTerminalPopulation.RAM.population s.shops groups mPaid paidBits extBits origin x =
      s.subrow p0 x := rfl

theorem actor_at (x : Fin s.blocks) :
    DescentTerminalActorRepack.bank (a:=actBits) s.shops groups mAct o1 x = occupied x := rfl

theorem prior : s.Prior next p0 occupied := by
  refine ⟨?_, ?_, ?_⟩
  · change p0 + s.rows + s.guard ≤ o1 + actFee + s.rows + pad s.shops
    change o1 ≤ o1 + actFee + s.rows + pad s.shops
    omega
  · intro x
    change a1 + x.val*s.shops + pad s.shops ≤ a1 + s.rows + pad s.shops
    have bound := s.bounds x
    omega
  · intro x
    exact covered s.shops

theorem space :
    next ≤ origin + popFee + actFee + 4*s.rows + 4*s.shops + 3 := by
  have smallH := pad_le s.shops
  have smallN := pad_le s.rows
  unfold start actor actStart pop Shape.guard
  omega

/-- A co-copy with the same group packing needs only its attained single
bank per block. No actor dictionary or extra actor pass is purchased. -/
theorem prior_packed (original : Fin s.blocks → Bank)
    (early : ∀ x, (original x).base+(original x).size≤origin)
    (capacity : ∀ x, s.shops≤(original x).size) :
    s.Prior o1 p0 original :=
  ⟨le_rfl,fun x=>(early x).trans (by unfold actStart pop;omega),capacity⟩

variable {wb : ℕ} (paid actorSrc : Fin s.blocks → Bank) (ext : Bank)
local notation "blockRows" => s.rows
local notation "paidRows" => s.shops * chunks groups mPaid
local notation "actRows" => s.shops * chunks groups mAct
structure Earlier : Prop where
  paidEnd : ∀ x, (paid x).base + (paid x).size ≤ origin
  paidSize : ∀ x, paidRows ≤ (paid x).size
  extEnd : ext.base + ext.size ≤ origin
  extSize : s.shops ≤ ext.size
  acEnd : ∀ x, (actorSrc x).base + (actorSrc x).size ≤ origin
  acSize : ∀ x, actRows ≤ (actorSrc x).size

variable (early : Earlier s groups mPaid mAct origin paid actorSrc ext)
    (room : start s groups mPaid mAct paidBits extBits actBits origin < 2^wb)
include early room in
theorem paid_fit (x : Fin s.blocks) :
    DescentTerminalPopulation.RAM.Fit s.shops groups mPaid paidBits extBits origin (paid x) ext p0 wb := by
  have bound : p0<2^wb := by
    unfold start actor actStart at room
    omega
  have fits (b : Bank) (e : b.base+b.size≤origin) : b.Fits wb origin := by
    have z : origin ≤ p0 := Nat.le_add_right ..
    exact ⟨Nat.two_pow_pos _, (Nat.le_add_left ..).trans_lt (e.trans_lt (z.trans_lt bound)), e⟩
  exact ⟨fits _ (early.paidEnd x), fits _ early.extEnd, early.paidSize x, early.extSize, le_rfl, bound⟩

variable (nodeBits : ℕ) (pick : Fin s.blocks → Cell actBits → Cell 1)
local notation "popProc" => DescentTerminalPopulation.RAM.issue s.shops groups mPaid paidBits nodeBits extBits origin paid ext wb
local notation "actorProc" => DescentTerminalActorRepack.program pick s.shops groups mAct o1 actorSrc wb
local notation "pCost" => DescentTerminalPopulation.RAM.ticks s.shops groups mPaid paidBits extBits origin paid ext
local notation "aCost" => DescentTerminalActorRepack.ticks (a:=actBits) s.shops groups mAct o1 actorSrc
def program := (popProc).seq actorProc
def final (m : Memory wb) := DescentTerminalActorRepack.final pick s.shops groups mAct o1 actorSrc
  (DescentTerminalPopulation.RAM.done s.shops groups mPaid paidBits nodeBits extBits origin paid ext m)

include early room in
/-- Both words in the normalized channel chart come from actual earlier raster/census
rows, in the same final memory. Both cells remain readable over rounded views. -/
theorem issued (m : Memory wb) (positive : 0< mAct) (zero : ∀b,pick b 0=0)
    (charges : Fin s.blocks → Fin s.shops → Fin groups → Cell paidBits) (hist : Fin s.shops → Cell extBits)
    (actors : Fin s.blocks → Fin s.shops → Fin groups → Cell actBits)
    (countRead : ∀ x, ∀ j : Row s.shops groups mPaid, m ((paid x).base+(row s.shops groups mPaid j).val) =
      ((data (charges x) j).val : Word wb))
    (extRead : ∀h : Fin s.shops, m (ext.base+h.val) = ((hist h).val : Word wb))
    (actRead : ∀x, ∀j : Row s.shops groups mAct, m ((actorSrc x).base+(row s.shops groups mAct j).val) =
      ((data (actors x) j).val : Word wb)) :
    let out := final (s:=s) (groups:=groups) (mPaid:=mPaid) (mAct:=mAct) (paidBits:=paidBits)
      (extBits:=extBits) (actBits:=actBits) (origin:=origin) (paid:=paid) (actorSrc:=actorSrc) (ext:=ext)
      (nodeBits:=nodeBits) (pick:=pick) m
    ((popProc).seq actorProc).Exec m out (pCost+aCost) ∧ CheapCode ((popProc).seq actorProc) ∧
    (∀ (x : Fin s.blocks) (h : Fin s.shops), out ((s.subrow p0 x).base+h.val) =
      (DescentTerminalPopulation.words (M:=mPaid) nodeBits (charges x) (fun h=>(hist h).val) h : Word wb)) ∧
    (∀ x (h:Fin s.shops), out ((occupied x).base+h.val) =
      ((encode 1 groups (fun g=>pick x (actors x h g))).val : Word wb)) ∧
    ∀ j,j<origin → out j=m j := by
  dsimp only
  have full : p0 + blockRows < 2^wb := by
    unfold start actor actStart at room
    omega
  have prior_ : origin ≤ o1 := by unfold actStart pop; omega
  have actual : a1 + blockRows < 2^wb := by unfold start at room;omega
  have fit := paid_fit s groups mPaid mAct paidBits extBits actBits origin paid actorSrc ext early room
  let mid := DescentTerminalPopulation.RAM.done s.shops groups mPaid paidBits nodeBits extBits origin paid ext m
  obtain ⟨exec, good, saved⟩ := DescentTerminalPopulation.RAM.run s.shops groups mPaid paidBits nodeBits extBits origin paid ext m fit full
  have actorsFit (x) : (actorSrc x).Fits wb o1 := by
    have e := early.acEnd x
    have end_ : o1<2^wb := by unfold actor at actual;omega
    exact ⟨Nat.two_pow_pos _, (Nat.le_add_left ..).trans_lt ((e.trans prior_).trans_lt end_),e.trans prior_⟩
  have archived (x) (j : Row s.shops groups mAct) : mid ((actorSrc x).base+(row s.shops groups mAct j).val) =
      ((data (actors x) j).val:Word wb) := by
    have before := early.acEnd x
    have pos := (row s.shops groups mAct j).isLt.trans_le (early.acSize x)
    exact (saved _ (.inl (by omega))).trans (actRead x j)
  obtain ⟨move, cheap, live, hold⟩ := DescentTerminalActorRepack.issued pick s.shops groups mAct o1 actorSrc mid
    actorsFit early.acSize actual zero positive actors archived
  refine ⟨exec.then move,cheap_seq good cheap,?_,live,?_⟩
  · intro x h
    have at_ := DescentTerminalPopulation.RAM.read s.shops groups mPaid paidBits nodeBits extBits origin
      paid ext m fit full charges hist countRead extRead x h
    have within := s.bounds x
    have lt := h.isLt
    have same := hold ((s.subrow p0 x).base+h.val) (.inl (by
      change p0+x.val*s.shops+h.val < p0+s.rows+s.guard
      omega))
    exact same.trans at_
  · intro j small
    exact (hold j (.inl (small.trans_le prior_))).trans (saved j (.inl small))


end
end Hierarchy.DescentTerminalPriorArena

end OAI
