import OAI.Computability.VPVNP.PairSimulationLeafCapacity
import OAI.Computability.VPVNP.PairSimulationLeafCachedSources
import OAI.Computability.VPVNP.PairSimulationLeafIncidentReady

/-! # The linked native rows for the complete cursor-zero leaf startup -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafBoot

open BurstRAM PrivateRAM RAMTape LeafStartup StackMachine LeafRegisterBank
open scoped Fin.CommRing

set_option synthInstance.maxSize 10000

/-- Register names for the scalar initializer together with 30 additional slots used by the
cursor-zero startup. -/
abbrev Reg := ScalarReg ⊕ Fin 30
/-- The incident-bit stack port of the concrete validator with 52 registers and 34 public
operands. -/
abbrev incident := LeafLoadedBank.incidentPort 52 34

variable {w p r k : ℕ}

/-- Embed the scalar initializer's register bank into the physical startup registers. -/
def scalar (reg : Reg ↪ Fin r) : ScalarReg ↪ Fin r := ⟨fun j => reg (.inl j), fun _ _ h => Sum.inl.inj (reg.injective h)⟩

/-- Place the scalar initializer's source words, including the 34 public operands, in their
physical startup registers. -/
def sources (reg : Reg ↪ Fin r) : Source 34 ↪ Fin r :=
  ⟨fun j => reg (.inl (.inr j)), fun _ _ h => Sum.inr.inj (Sum.inl.inj (reg.injective h))⟩

/-- Assign the incident loader's 30 register indices to startup registers, sharing the
dimension, site address, bucket, word width and incident stack pointers with the scalar
initializer. -/
def geometryName (i : Fin 30) : Reg :=
  if i = 11 then .inl (.inr .d) else if i = 13 then .inl (.inr .address) else
  if i = 20 then .inl (.inr .bucket) else if i = 21 then .inl (.inr .width) else
  if i = 23 then .inl (.inl (.pointers (.stack (.base incident)))) else
  if i = 24 then .inl (.inl (.pointers (.stack (.top incident)))) else .inr i

private theorem geometry_injective : Function.Injective geometryName := by
  let back : Reg → Fin 30 := fun
    | .inr i => i
    | .inl (.inr .d) => 11
    | .inl (.inr .address) => 13
    | .inl (.inr .bucket) => 20
    | .inl (.inr .width) => 21
    | .inl (.inl (.pointers (.stack (.base _)))) => 23
    | .inl (.inl (.pointers (.stack (.top _)))) => 24
    | _ => 0
  apply Function.LeftInverse.injective (g := back)
  intro i; fin_cases i <;> rfl

/-- The injective placement of the incident loader's geometry registers in the host machine. -/
def geometry (reg : Reg ↪ Fin r) : Fin 30 ↪ Fin r := ⟨fun i => reg (geometryName i),reg.injective.comp geometry_injective⟩

/-- Physical placement of the stack interpreter's named registers during cursor-zero
initialization. -/
abbrev stack (reg : Reg ↪ Fin r) := LeafRegisterBank.stack (scalar reg)
/-- Physical placement of the allocation cursor, stride and stack registers used to assign the
validator's private stack intervals. -/
abbrev pointer (reg : Reg ↪ Fin r) := LeafFill.pointers (load (scalar reg))

@[simp] theorem scalar_at (reg : Reg ↪ Fin r) (j : ScalarReg) : scalar reg j = reg (.inl j) := rfl
@[simp] theorem source_at (reg : Reg ↪ Fin r) (j : Source 34) : sources reg j = reg (.inl (.inr j)) := rfl
@[simp] theorem geometry_at (reg : Reg ↪ Fin r) (j : Fin 30) : geometry reg j = reg (geometryName j) := rfl

/-- Startup register holding the private address of the first cached operand. -/
def cacheBase (reg : Reg ↪ Fin r) := reg (.inr 0)
/-- Startup register holding the base of the current node's private argument frame. -/
def nodeBase (reg : Reg ↪ Fin r) := reg (.inr 22)
/-- Temporary register used while calculating the stack capacity. -/
def tmp (reg : Reg ↪ Fin r) := reg (.inr 1)

theorem wiring (reg : Reg ↪ Fin r) :
    LeafSourceLoad.Wiring (sources reg) (sources reg .header) (cacheBase reg)
      (pointer reg .cursor) (stack reg .one) := by
  constructor <;> simp [cacheBase,stack,pointer]

theorem protect (reg : Reg ↪ Fin r) (j : Register ScalarPort) (_ht : j ≠ .tmp) (hj : j ≠ .top incident) :
    ∀ i ∈ LeafIncidentMachine.changed, stack reg j ≠ geometry reg i := by
  intro i hi
  have hb : i ≠ 23 := fun e => (show (23 : Fin 30) ∉ LeafIncidentMachine.changed by decide) (e ▸ hi)
  by_cases he : i = 24
  · subst i
    change stack reg j ≠ stack reg (.top incident)
    exact (stack reg).injective.ne hj
  · simp [stack,geometryName,hb,he]; split_ifs <;> simp

/-- Program labels for the startup prelude, the 38 cache reads and increments, the capacity
calculation, and the scalar and incident loaders. -/
inductive Label where
  | pre (i : Fin 5) | read (i : Fin 38) | increment (i : Fin 38)
  | capacity (i : Fin 8) | scalar (j : ScalarLabel) | incident (j : LeafIncidentMachine.Stage)
  deriving DecidableEq

noncomputable instance : Fintype Label := derive_fintype% _

variable (pc : Label → Fin p) (reg : Reg ↪ Fin r) (nPub : Fin k) (done : Fin p)

/-- Jump to the cache read at the given index, or to the first capacity instruction when all 38
words have been consumed. -/
def readPC (i : Fin ((LeafSourceLoad.slots 34).length+1)) : Fin p :=
  if h : i.val < 38 then pc (.read ⟨i.val,h⟩) else pc (.capacity 0)

/-- Entry label for allocating the first scalar port's stack, with the allocation finalizer as
the empty-list continuation. -/
noncomputable def scalarEntry :=
  LeafPointers.next scalarRows (fun a i => pc (.scalar (.pointer a i))) (pc (.scalar (.finish 0)))

/-- The startup instruction at a leaf-boot label, linking the cache scan and capacity
calculation to scalar initialization and the incident copy. -/
noncomputable def instruction : Label → Instr w p r k
  | .pre i => LeafSourceLoad.prelude (sources reg) (sources reg .address) (sources reg .header) (cacheBase reg)
      (pointer reg .cursor) (stack reg .one) (pc ∘ Label.pre) (pc (.read 0)) i
  | .read i => LeafSourceLoad.readInstr (sources reg) (pointer reg .cursor) (pc (.increment i))
      ((LeafSourceLoad.slots 34)[i.val]'(by simpa only [LeafSourceLoad.length_slots] using i.isLt))
  | .increment i => LeafSourceLoad.incInstr (pointer reg .cursor) (stack reg .one)
      (readPC pc ((i.cast (by rw [LeafSourceLoad.length_slots])).succ))
  | .capacity i => LeafCapacity.instruction (pc ∘ Label.capacity) (pointer reg .stride) (tmp reg) nPub (scalarEntry pc) i
  | .scalar j => LeafPortTable.instruction field (pc ∘ Label.scalar) (scalar reg) (pc (.incident (.inl 0))) scalarRows j
  | .incident j => LeafIncidentMachine.instruction (pc ∘ Label.incident) (geometry reg) done j

private theorem resize_twice (i : Instr 1 p r k) : (i.resize 5).resize w = i.resize w := by
  cases i <;> try rfl
  case constant dst v next => simp only [Instr.resize,resize_literal (by decide : 1≤5)]

theorem resize_instruction (j : Label) :
    (instruction (w := 5) pc reg nPub done j).resize w = instruction pc reg nPub done j := by
  cases j with
  | pre i => simp only [instruction]; rw [← LeafSourceLoad.prelude_resize (w := 5),resize_twice,LeafSourceLoad.prelude_resize]
  | read i | increment i => rfl
  | capacity i => simp only [instruction]; rw [← LeafCapacity.resize_instruction (w := 5),resize_twice,LeafCapacity.resize_instruction]
  | scalar j => simp only [instruction]; rw [← LeafPortTable.resize_instruction (w := 5),resize_twice,LeafPortTable.resize_instruction]
  | incident j => exact LeafIncidentMachine.resize_instruction ..

/-- Every startup label in the host machine executes its prescribed instruction with the
designated length operand and return label. -/
def Linked (M : Machine w p r k) : Prop := ∀ j, M.code (pc j) = instruction pc reg nPub done j

end PairSimulation.LeafBoot

end VPVNP
end Computability
end OAI
