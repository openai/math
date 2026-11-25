import OAI.Hierarchy.DescentOrdinaryPriorRetile
import OAI.Hierarchy.DescentOrdinaryHostPad

namespace OAI
/-! # Crop or extend all seven physically retiled prior operand families -/
namespace Hierarchy.DescentOrdinaryPriorPad
open DescentSIMDLookup DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony
open DescentSixParty.Chronology ProtocolRAM DescentPackedZip
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (l : Layout)
abbrev pages := DescentOrdinaryPriorRetile.pages l
def start (lanes base : ℕ) := DescentOrdinaryPriorRetile.roof l lanes base
def rows (currentH lanes : ℕ) := currentH*chunks l.groups lanes
def kept (currentH lanes : ℕ) := min (l.hosts*chunks l.groups lanes) (rows l currentH lanes)
def total (currentH lanes : ℕ) := (pages l+1)*rows l currentH lanes
def roof (currentH lanes base : ℕ) := start l lanes base+total l currentH lanes+2^Nat.clog 2 (rows l currentH lanes+1)
def placedBank (currentH lanes base page : ℕ) : Bank :=
  ⟨start l lanes base+page*rows l currentH lanes,Nat.clog 2 (rows l currentH lanes+1)⟩
def bank (currentH lanes base : ℕ) (x : Fin l.blocks) (p : Pages l.operands) :=
  placedBank l currentH lanes base ((DescentOrdinaryPriorRetile.number l) (p,x)).val
def zero (currentH lanes base : ℕ) :=placedBank l currentH lanes base (pages l)

abbrev extend {H G bits : ℕ} (currentH : ℕ) (value : Fin H→Fin G→Cell bits) :=
  DescentOrdinaryHostPad.extend currentH value

def rect (currentH lanes : ℕ) : DescentOrdinaryHostPad.Rect :=
  ⟨l.hosts,currentH,l.groups,pages l,lanes⟩

def inputs (lanes base : ℕ) (i : Fin (pages l)) : Bank :=
  let pair:=(DescentOrdinaryPriorRetile.number l).symm i
  DescentOrdinaryPriorRetile.bank l lanes base pair.2 pair.1

def column (lanes base j : ℕ) : Expr :=
  if live : j<pages l then
    let pair:=(DescentOrdinaryPriorRetile.number l).symm ⟨j,live⟩
    .lookup (DescentOrdinaryPriorRetile.bank l lanes base pair.2 pair.1) .row
  else .lit 0

def copies (currentH lanes base : ℕ) :=
  DescentPackedFlowBatch.passes (start l lanes base) (kept l currentH lanes) (rows l currentH lanes)
    (column l lanes base) 0 (pages l)

def extension (currentH lanes base w : ℕ) : NativePhase w :=
  (rect l currentH lanes).phase (start l lanes base) (inputs l lanes base) w

def phase (currentH lanes base prior w : ℕ) :=
  (DescentOrdinaryPriorRetile.phase l lanes base prior w).seq (extension l currentH lanes base w)

def program (currentH lanes base prior w : ℕ) := (phase l currentH lanes base prior w).program

variable (currentH lanes base prior : ℕ)
local notation "at₀" => start l lanes base
local notation "R₀" => rows l currentH lanes
local notation "K₀" => kept l currentH lanes
local notation "T₀" => total l currentH lanes
local notation "N₀" => pages l
local notation "cs₀" => copies l currentH lanes base
local notation "zbank" => zero l currentH lanes base
local notation "roof₀" => roof l currentH lanes base

theorem translated : roof₀=base+roof l currentH lanes 0 :=by
  simp only [roof,start,DescentOrdinaryPriorRetile.translated l lanes base,Nat.add_assoc]

theorem base_le : base≤roof₀ :=
  (DescentOrdinaryPriorRetile.base_le l lanes base).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

private theorem prior_room {w} (room : roof₀<2^w) : at₀<2^w :=
  ((rect l currentH lanes).base_le at₀).trans_lt room

theorem placed {w} (room : roof₀<2^w) (x : Fin l.blocks) (p : Pages l.operands) :
    (bank l currentH lanes base x p).Fits w roof₀ ∧ R₀≤(bank l currentH lanes base x p).size :=
  (rect l currentH lanes).placed at₀ room ((DescentOrdinaryPriorRetile.number l) (p,x))

theorem zero_placed {w} (room : roof₀<2^w) : (zbank).Fits w roof₀ ∧ R₀≤(zbank).size :=
  (rect l currentH lanes).zero_placed at₀ room

variable {w : ℕ} (m : Memory w)
  (old : ∀(x : Fin l.blocks) (p : Pages l.operands),(previousBank l prior x p).Fits w base)
  (room : roof l currentH lanes base < 2^w)
local notation "mid" => NativePhase.image (DescentOrdinaryPriorRetile.phase l lanes base prior w) m

include room in
private theorem retiled_fits (pg : Fin (pages l)) : (inputs l lanes base pg).Fits w at₀ :=
  (DescentOrdinaryPriorRetile.placed l lanes base (prior_room l currentH lanes base room) _ _).1

include old room in
theorem any : (phase l currentH lanes base prior w).Runs m ∧
    ∀i, i < base ∨ roof₀ ≤ i → (phase l currentH lanes base prior w).image m i=m i :=by
  have before:=DescentOrdinaryPriorRetile.any l lanes base prior m old (prior_room l currentH lanes base room)
  have after:=(rect l currentH lanes).any at₀ (inputs l lanes base) mid (retiled_fits l currentH lanes base room) room
  refine ⟨NativePhase.seq_runs _ _ m before.1 after.1,?_⟩
  intro i outside
  rcases outside with lo|hi
  · exact (after.2 i (.inl (lo.trans_le (DescentOrdinaryPriorRetile.base_le l lanes base)))).trans (before.2 i (.inl lo))
  · exact (after.2 i (.inr hi)).trans (before.2 i (.inr (((rect l currentH lanes).base_le at₀).trans hi)))

include old room in
theorem reads (x : Fin l.blocks) (p : Pages l.operands)
    (value : Fin l.hosts→Fin l.groups→Cell (DescentOrdinaryPriorRetile.digits l))
    (live : 0<l.lanes) (read : Reads (previousBank l prior x p) value l.lanes m) :
    Reads (bank l currentH lanes base x p) (DescentOrdinaryHostPad.extend currentH value) lanes
      ((phase l currentH lanes base prior w).image m) :=by
  let pg:=(DescentOrdinaryPriorRetile.number l) (p,x)
  have src : inputs l lanes base pg=DescentOrdinaryPriorRetile.bank l lanes base x p:=by simp [inputs,pg]
  have first:=DescentOrdinaryPriorRetile.reads l lanes base prior m old (prior_room l currentH lanes base room) x p value live read
  have layout:=DescentOrdinaryPriorRetile.placed l lanes base (prior_room l currentH lanes base room) x p
  exact (rect l currentH lanes).reads at₀ (inputs l lanes base) mid (retiled_fits l currentH lanes base room) room
    pg value (by rw [src];exact layout.2) (by rw [src];exact first)

theorem zero_reads {bits : ℕ} : Reads zbank (fun (_:Fin currentH) (_:Fin l.groups)=>(0:Cell bits)) lanes
    ((phase l currentH lanes base prior w).image m) :=
  (rect l currentH lanes).zero_reads at₀ (inputs l lanes base) mid


end
end Hierarchy.DescentOrdinaryPriorPad

end OAI
