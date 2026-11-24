import OAI.Computability.VPVNP.PairRefreshHalfDecoder
import OAI.Computability.VPVNP.PairShrinkRoleStages

/-!
# A typed parser for the refresh hook

The parent is reconstructed from its private packet, and the old half is the
single prefix consumed from the branch tape. The local map receives the scratch
after the packet write. A success records both halves, the exact chronological
trace and the complete resulting scratch.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook

open NetworkKernel BurstRAM BurstRAM.PrivateRAM DFS Compression NodeArguments NodeArguments.ChildScan ShrinkRole
open scoped Fin.CommRing

variable {bits endAddr a b g l pcs regs : ℕ}
  (X : State a g) (oldSite : X.network.Site) (Y : State b l) (newSite : Y.network.Site)
  (A : Arena) (child parent : ℕ)

local notation "Old" => Network.Half (State.network X) oldSite
local notation "New" => Network.Half (State.network Y) newSite
local notation "S₀" => Scratch bits endAddr

variable (front : Word bits → X.network.Half oldSite → List (Event bits))
  (action : X.network.Half oldSite → Y.network.Half newSite → Scratch bits endAddr → Option (List (Event bits) × Scratch bits endAddr))

/-- Form the old child's argument packet from its DFS row address and its packed half-wire
bits. -/
noncomputable def packet (x : Old) : Packet := ⟨child,packed X oldSite x⟩

/-- Decode the resident parent and the guessed old child, store the child packet, and invoke
the refresh action on the two assignments. -/
noncomputable def reader : Reader bits endAddr (Old × New) := fun node s bs =>
  match RefreshHalfDecoder.parent Y newSite A parent s, (RefreshHalfDecoder.reader X oldSite).read bs with
  | some newer, some (older,tail) =>
    match action older newer ((packet X oldSite child older).write A s) with
    | some (es,out) => some (⟨(older,newer),front node older ++ es,out⟩,tail)
    | none => none
  | _, _ => none


local notation "read" => reader X oldSite Y newSite A child parent front action

theorem read_some_iff (node : Word bits) (s : S₀) (bs : List Bool)
    (out : Outcome bits endAddr (Old × New)) (tail : List Bool) :
    read node s bs = some (out,tail) ↔
      RefreshHalfDecoder.parent Y newSite A parent s = some out.value.2 ∧
      bs = packed X oldSite out.value.1 ++ tail ∧
      ∃ es, action out.value.1 out.value.2 ((packet X oldSite child out.value.1).write A s) =
          some (es,out.updated) ∧ out.trace = front node out.value.1 ++ es := by
  constructor
  · intro h
    cases hp : RefreshHalfDecoder.parent Y newSite A parent s with
    | none => simp [reader,hp] at h
    | some z =>
      cases hx : (RefreshHalfDecoder.reader X oldSite).read bs with
      | none => simp [reader,hp,hx] at h
      | some pair =>
        obtain ⟨x,rest⟩ := pair
        cases ha : action x z ((packet X oldSite child x).write A s) with
        | none => simp [reader,hp,hx,ha] at h
        | some value =>
          obtain ⟨es,next⟩ := value
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj (by simpa only [reader,hp,hx,ha] using h))
          exact ⟨rfl,(RefreshHalfDecoder.read_iff X oldSite bs x rest).mp hx,es,ha,rfl⟩
  · rintro ⟨hp,bsEq,es,ha,trace⟩
    have hx := (RefreshHalfDecoder.read_iff X oldSite bs out.value.1 tail).mpr bsEq
    cases out with | mk pair tr updated =>
      cases pair with | mk x z =>
        change tr = front node x ++ es at trace
        subst tr
        simp only [reader,hp,hx,ha]

variable (frontChoices : ∀ node x, choiceBits (front node x) = packed X oldSite x)
  (quiet : ∀ x z s es next, action x z s = some (es,next) → choiceBits es = [])

include frontChoices quiet in
theorem splits : Splits read := by
  intro node s bs out tail h
  obtain ⟨_,tape,es,ha,path⟩ := (read_some_iff X oldSite Y newSite A child parent front action node s bs out tail).mp h
  rw [path,PrimedInputRAM.Flow.choiceBits_append,frontChoices,quiet _ _ _ _ _ ha,List.append_nil]
  exact tape

variable (M : Machine bits pcs regs 11) (m : Memory bits) (dfs : Fin 9 ↪ Fin regs)
  (pre : Word bits → Config bits pcs regs → Prop) (done : Fin pcs)

include frontChoices quiet in
/-- A packet parser with a genuine successful native prefix and both native
rejection cases realizes the DFS hook on all complete and truncated tapes. -/
theorem realizes
    (parentReady : ∀ node c, pre node c → ∃ z, RefreshHalfDecoder.parent Y newSite A parent (scratch endAddr c.privateMem) = some z)
    (short : ∀ node c bs, pre node c → bs.length < RefreshHalfDecoder.width X oldSite → ¬ Returns M c m bs)
    (reject : ∀ node c x z tail, pre node c →
      RefreshHalfDecoder.parent Y newSite A parent (scratch endAddr c.privateMem) = some z →
      action x z ((packet X oldSite child x).write A (scratch endAddr c.privateMem)) = none →
      ¬ Returns M c m (packed X oldSite x ++ tail))
    (success : ∀ node c x z es next, pre node c →
      RefreshHalfDecoder.parent Y newSite A parent (scratch endAddr c.privateMem) = some z →
      action x z ((packet X oldSite child x).write A (scratch endAddr c.privateMem)) = some (es,next) →
      ∃ out, out.pc = done ∧ ShrinkRole.Frame dfs endAddr c out ∧ scratch endAddr out.privateMem = next ∧
        ChildScan.Prefix M m c out (packed X oldSite x) (front node x ++ es)) :
    Realizes read M m dfs pre (fun _ _ d => d.pc = done) := by
  constructor
  · intro node c bs out tail hc got
    obtain ⟨hp,tape,es,actionEq,trace⟩ := (read_some_iff X oldSite Y newSite A child parent front action _ _ _ _ _).mp got
    obtain ⟨endState,pc,frame,updated,path⟩ := success _ _ _ _ _ _ hc hp actionEq
    have bitsEq : choiceBits out.trace = packed X oldSite out.value.1 := by
      rw [trace,PrimedInputRAM.Flow.choiceBits_append,frontChoices,quiet _ _ _ _ _ actionEq,List.append_nil]
    exact ⟨bitsEq ▸ tape,endState,pc,frame,updated,by rwa [bitsEq,trace]⟩
  · intro node c bs hc refused
    obtain ⟨z,hz⟩ := parentReady _ _ hc
    cases parsed : (RefreshHalfDecoder.reader X oldSite).read bs with
    | none => exact short _ _ _ hc ((RefreshHalfDecoder.none_iff X oldSite bs).mp parsed)
    | some pair =>
      obtain ⟨x,tail⟩ := pair
      have bsEq := (RefreshHalfDecoder.read_iff X oldSite bs x tail).mp parsed
      have ha : action x z ((packet X oldSite child x).write A (scratch endAddr c.privateMem)) = none := by
        cases h : action x z ((packet X oldSite child x).write A (scratch endAddr c.privateMem)) with
        | none => rfl
        | some pair =>
          obtain ⟨es,next⟩ := pair
          simp [reader,hz,parsed,h] at refused
      exact bsEq ▸ reject _ _ _ _ _ hc hz ha

end PairSimulation.RefreshHook

end VPVNP
end Computability
end OAI
