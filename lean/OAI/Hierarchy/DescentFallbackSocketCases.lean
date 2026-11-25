import OAI.Hierarchy.DescentCalendarBankEndpoint
import OAI.Hierarchy.DescentCalendarTreeRootSocket
import OAI.Hierarchy.DescentCalendarTreeLeafSocket
import OAI.Hierarchy.DescentCalendarTreeArcSocket

namespace OAI
/-! Both ordered formal operands and all p-words of a reached exception-tree gate. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open Computability.BorderVNP.Crossing DescentKernelHistory DescentLaneGates DescentBundleHistory DescentChosenRouter
open DescentContactTree DescentRouterSlots DescentTreePrefixIntervals DescentCompiler DescentResetGates
open DescentResetLocalRoster DescentResetCableSlots DescentColonies
open DescentLaneGates DescentBundleHistory DescentFallbackItemSelect DescentTreeLaneProgram
open DescentTreeLaneProgram DescentFallbackOperandBranch
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000

variable {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => (Z).placement
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "ht" => GroupStage.depthBound D n f g
variable {p split : ℕ} (hp : 0 < p) (unitFit : B.reset.unit=split*p)
  (s : Bool) (t : B.reset.Fallback)
  (e : Item B.reset.placement.contact B.reset.placement.owner s (.inr t))
  (b : Fin split)
local notation "bk" => (placement).fallbackBook s t
local notation "linkAt" => link (placement).contact (placement).owner s (.inr t)
local notation "code" => DescentFixedNamedContact.code (bk).codes linkAt
local notation "leaf" => (bk).codes (linkAt e)

local notation:max "node" l:arg => (⟨l,prefixAt code (l).val e⟩ : Physical.Site (bk).height)
local notation:max "venue" l:arg => (⟨(s,.inr t),node l⟩ : (Z).bank.Site)
local notation:max "gate" l:arg => installedTreeGate (K:=F) (C₀:=C) (n:=B.reset.n) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth
  d split p hp unitFit s t (node l) ⟨e,rfl⟩ b
local notation "raw" => DescentFixedExceptionalRouter.device d (placement).contact (placement).input
  (placement).site (placement).owner (fun _=>split*p) s (.inr t) (bk).codes
local notation:max "op" l:arg => (DescentTreeLaneProgram.program d (placement).contact (placement).input (placement).site
  (placement).owner (placement).align split p hp s (.inr t) (bk).codes birth (2^(Z).n) (node l)).op (⟨e,rfl⟩,b)
local notation:max "rawUnits" l:arg => (fun a=>boundaryWidth raw (node l) a/p)
local notation:max "ln" l:arg f:arg => (op l).arg (f : Fin 2)
local notation:max "cnt" l:arg f:arg => (ln l f).count (rawUnits l)
local notation "h₀" => (bk).height
local notation "last_" => Fin.last h₀
local notation "root" => ((Z).fallLabel T t,((T).code t).2.2)
variable {field query lanes nodes args : ℕ}
local notation "cfg" => flatConfig B field query lanes split split nodes args
variable (xs : Fin (flatConfig B field query lanes split split nodes args).count→DescentFallbackItemSelect.Item)
local notation:max "reply" l:arg slot:arg => (cfg).physicalReply s input.placement.cap h₀ (List.ofFn (prefixAt code (l).val e))
  root xs (start ht leaf) (ln l 0) (ln l 1) slot
local notation:max "shape" l:arg => (Z).laneShape birth split p hp unitFit (venue l)
local notation:max "full" l:arg => cnt l 0 + cnt l 1

/-- The tuple at a live word, the actual reference at that very program index,
and the selected incidence of the installed wire. -/
def TreeSocketWord (l : Fin (h₀+1)) (slot : ℕ) : Prop :=
  ∃number word size mark, ∃socket : PublicSocket B (treeReceiver B (venue l)) split word mark number,
    ∃ref : BlockRef p (boundaryWidth (Z).bank (venue l)),
      reply l slot=some (number,word,size,mark) ∧
      (((shape l).keys (gate l))[slot]?)=some (.inl ref) ∧
      deviceRoute B hp (venue l) ref=(socket.face.val.1,word)

private theorem first_lane_count {α : Type} (ports : Fin 2 → α) (weight : α → ℕ) :
    (((List.ofFn ports).take 1).map weight).sum = weight (ports 0) := by
  rw [List.ofFn_succ]
  simp

private theorem routed_reference {α β γ : Type*} {entry : Option (α ⊕ β)} {r : α}
    {keyFn : α → γ} {value : γ} (row : entry = some (.inl r)) (path : keyFn r = value) :
    ∃ x, entry = some (.inl x) ∧ keyFn x = value := ⟨r,row,path⟩

local notation:max "issued" l:arg slot:arg => TreeSocketWord B hp unitFit s t e b xs l slot
variable (rootRows : RootRows (field:=field) (query:=query) (lanes:=lanes) (batches:=split)
  (nodes:=nodes) (args:=args) B s (B.reset.placement.input s e.val) xs)

include rootRows in
private theorem root_socket_words (j : Fin (cnt (0:Fin (h₀+1)) 0)) : issued (0:Fin (h₀+1)) j.val := by
    obtain ⟨number,socket,word,keys,route⟩:=tree_root_keyed_socket (field:=field) (query:=query) (lanes:=lanes)
      (nodes:=nodes) (args:=args) B hp unitFit s t e b xs rootRows j
    obtain ⟨ref,keys,route⟩ := routed_reference keys route
    exact ⟨number,_,_,false,socket,ref,word,keys,route⟩

private theorem move_public_socket {a y} {units index number : ℕ} {mark : Bool}
    (same : a = y) (socket : PublicSocket B a units index mark number) :
    ∃ picked : PublicSocket B y units index mark number, picked.face.val.1 = socket.face.val.1 := by
  subst y
  exact ⟨socket,rfl⟩

private theorem leaf_socket_words (j : Fin (cnt last_ 1)) : issued last_ (cnt last_ 0+j.val) := by
    obtain ⟨socket,word,keys,route,face⟩:=tree_leaf_keyed_socket (field:=field) (query:=query) (lanes:=lanes)
      (nodes:=nodes) (args:=args) (grain:=1) B hp unitFit s t e b xs j
    obtain ⟨ref,keys,route⟩ := routed_reference keys route
    have ends:=installed_leaf_end (K:=F) (C₀:=C) (k:=B.reset.k) (n:=B.reset.n) (h:=h) (bits:=B.reset.width) (u:=B.reset.unit) (N:=∑ x,B.count x) placement (Z).graph (Z).positive (Z).pay (Z).circuit birth
      d split p hp unitFit s t e b
    have atHost:=bank_end_follows B (.inl ((placement).contact e.val)) s (venue last_) ends
    obtain ⟨picked,same⟩ := move_public_socket B atHost socket
    refine ⟨_,_,_,true,picked,ref,word,keys,?_⟩
    exact route.trans (congrArg (fun a => (a,_)) same.symm)


private theorem previous_arc_socket_words (d₀ : Fin (bk).height) (j : Fin (cnt d₀.succ 0)) :
    issued d₀.succ j.val := by
    obtain ⟨socket,keys,route,face⟩:=tree_arc_keyed_socket B hp unitFit s t e b d₀ true field query lanes split nodes args j
    obtain ⟨ref,keys,route⟩ := routed_reference keys route
    have atHost:=tree_arc_receiver B s t e d₀ true
    change (blocks B).dst _ = treeReceiver B (venue d₀.succ) at atHost
    unfold TreeSocketWord
    rw [←atHost]
    refine ⟨_,_,cnt d₀.succ 0,true,socket,ref,?_,?_,?_⟩
    · simp [Config.physicalReply,treeArcLevel,treeArcPin]
    · exact (congrArg (fun u : ℕ => ((shape d₀.succ).keys (gate d₀.succ))[u]?)
        (Nat.zero_add j.val).symm).trans keys
    · rw [face]
      exact route

private theorem following_arc_socket_words (d₀ : Fin (bk).height) (j : Fin (cnt d₀.castSucc 1)) :
    issued d₀.castSucc (cnt d₀.castSucc 0+j.val) := by
    obtain ⟨socket,keys,route,face⟩:=tree_arc_keyed_socket B hp unitFit s t e b d₀ false field query lanes split nodes args j
    obtain ⟨ref,keys,route⟩ := routed_reference keys route
    have atHost:=tree_arc_receiver B s t e d₀ false
    change (blocks B).src _ = treeReceiver B (venue d₀.castSucc) at atHost
    unfold TreeSocketWord
    rw [←atHost]
    refine ⟨_,_,cnt d₀.castSucc 1,true,socket,ref,?_,?_,?_⟩
    · simp [Config.physicalReply,treeArcLevel,treeArcPin,Nat.ne_of_lt d₀.isLt]
    · have before := first_lane_count (op d₀.castSucc).arg (fun lane => lane.count (rawUnits d₀.castSucc))
      exact (congrArg (fun u : ℕ => ((shape d₀.castSucc).keys (gate d₀.castSucc))[u+j.val]?)
        before.symm).trans keys
    · rw [face]
      exact route

include rootRows in
/-- The first formal operand at each level opens the registered old stem or
uses the preceding private arc. This includes the second covered p-word. -/
theorem previous_socket_words (l : Fin (h₀+1)) :
    ∀ j : Fin (cnt l 0), issued l j.val := by
  refine Fin.cases ?_ (fun d₀ => ?_) l
  · exact root_socket_words B hp unitFit s t e b xs rootRows
  · exact previous_arc_socket_words B hp unitFit s t e b xs d₀

/-- The last formal operand uses the next private arc, or the direct incident
contact at the leaf, with its own word in the contact fibre. -/
theorem following_socket_words (l : Fin (h₀+1)) :
    ∀ j : Fin (cnt l 1), issued l (cnt l 0+j.val) := by
  refine Fin.lastCases ?_ (fun d₀ => ?_) l
  · exact leaf_socket_words B hp unitFit s t e b xs
  · exact following_arc_socket_words B hp unitFit s t e b xs d₀

include rootRows in
theorem tree_socket_words (l : Fin (h₀+1)) (slot : ℕ) :
    (slot<full l → issued l slot) ∧ (full l≤ slot → reply l slot=none) :=by
  constructor
  · intro live
    by_cases incoming : slot<cnt l 0
    · exact previous_socket_words B hp unitFit s t e b xs rootRows l ⟨slot,incoming⟩
    · let j : Fin (cnt l 1):=⟨slot-cnt l 0,by omega⟩
      have index : cnt l 0+j.val=slot:=by dsimp [j];omega
      rw [←index]
      exact following_socket_words B hp unitFit s t e b xs l j
  · intro late
    have noLeft : ¬slot<cnt l 0:=by omega
    have noRight : ¬slot-cnt l 0<cnt l 1:=by omega
    simp [Config.physicalReply,noLeft,noRight]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
