import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentSeedSharedCountBank
import OAI.Hierarchy.DescentSeedNativeCells
import OAI.Hierarchy.DescentSeedSiteIndex

namespace OAI
/-! # The original host roster, occupancy and history-count words -/
namespace Hierarchy.DescentSeedInitialTable
set_option Elab.async false
open DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentInitialHost DescentInitialHost.PackedSeed DescentSeedRoot Catalyst
open scoped Classical Fin.CommRing
noncomputable section

variable {F : Type} [Field F] {k p H G M w : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph
variable (host : Site X.network.copyGraph ↪ Fin H)

/-- The ranks here are exactly the original cable header's `seedPeer` ranks.
They count earlier names among distinct neighboring hosts, including neighbors
whose current wire carries zero grains. -/
def neighbors (v : Site N) (i : Fin 3) : Option (Site N) :=
  if h : ∃u∈near N v,((near N v).filter (fun t=>index t< index u)).card=i.val then some h.choose else none

def roster (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (h : Fin H) (i : Fin 3) : Option (Fin H) :=
  (rack X host h).bind (fun v => (neighbors X v i).map (fun u => host u))

def atHost {T : Type*} (fallback : T) (val : Fin H→ T) (n : ℕ) : T :=
  if h:n< H then val ⟨n,h⟩ else fallback

def atPacked {T : Type*} (fallback : T) (val : Row H G M→ T) (n : ℕ) : T :=
  if h:n< H*chunks G M then val ((row H G M).symm ⟨n,h⟩) else fallback

theorem atPacked_row {T : Type*} (zero : T) (val : Row H G M→ T) (p : Row H G M) :
    atPacked zero val ((row H G M) p).val=val p := by
  simp only [atPacked,dite_eq_left (row H G M p).isLt,Fin.eta,Equiv.symm_apply_apply]

def peerWord (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (n : ℕ) : ℕ :=
  if h:n< H*3 then
    let p : Fin H×Fin 3:=finProdFinEquiv.symm ⟨n,h⟩
    DescentPackedColony.target (roster X host p.1 p.2)
  else H

omit [Field F] in
theorem peerWord_at (X : Approximation F k p)
    (host : Site X.network.copyGraph ↪ Fin H) (h : Fin H) (i : Fin 3) :
    peerWord X host (h.val*3+i.val)=DescentPackedColony.target (roster X host h i) := by
  let u : Fin (H*3):=finProdFinEquiv (h,i)
  have key : h.val*3+i.val=u.val := by change _=i.val+3*h.val;omega
  rw [key]
  rw [peerWord,dite_eq_left u.isLt]
  simp only [u,Fin.eta,Equiv.symm_apply_apply]

/-- One genuine seed record is attached to an original ordinary site and
none to an exterior hub. Every realized group and original block has the
same number; padding has neither records nor a hub bit. -/
def records (v : Site N) : ℕ := if hubFlag N v then 0 else 1

def fields (X : Approximation F k p) (host : Site X.network.copyGraph ↪ Fin H)
    (d G M wire hist s b : ℕ) (col n : ℕ) : ℕ :=
  match col with
  | 0 => peerWord X host n
  | 1 => chunks G M*n
  | 2 => atPacked (H:=H) (G:=G) (M:=M) 0 (fun p=>p.2.val) n
  | 3 => atPacked 0 (fun r : Row H G M=>
      (data (fun h (_ : Fin G)=>actorRow X host d h) r).val) n
  | 4 => atHost (if n=H then Fintype.card (Site X.network.copyGraph) else 0) (fun h=>(rack X host h).elim 0 (fun v=>if hubFlag X.network.copyGraph v then 1 else 0)) n
  | 5 => atPacked 0 (fun r : Row H G M=>(data
      (fun h (_ : Fin G)=>(((rack X host h).elim (0 : ℕ) (records X) : ℕ) : Cell b)) r).val) n
  | 6 => atPacked 0 (fun r : Row H G M=>(data
      (fun h (_ : Fin G)=>fixedRow X host false wire hist s b d h) r).val) n
  | 7 => atPacked 0 (fun r : Row H G M=>(data
      (fun h (_ : Fin G)=>fixedRow X host true wire hist s b d h) r).val) n
  | j+8 => atPacked (H:=H) (G:=G) (M:=M) 0 (fun p=>p.1.val*3+j) n

variable (base d wire hist s b : ℕ) (m : Memory w)
local notation "P" => ports base H G M 3
local notation "vals" => fields X host d G M wire hist s b
local notation "final" => image base H G M 3 vals m

theorem shared_host_count :
    (sharedHostCountBank base H G M).read final 0=(Fintype.card (Site N):Word w) :=by
  have word_:=read (H:=H) (G:=G) (M:=M) (D:=3) base vals m (c:=4) (by decide)
    (shared_host_slot H G M)
  simp only [sharedHostCountBank, Bank.read, Fin.val_zero, Nat.zero_mod, Nat.add_zero]
  refine word_.trans (congrArg (fun n : ℕ => (n : Word w)) ?_)
  simp only [fields, atHost, dite_eq_right (Nat.lt_irrefl H), ite_eq_left True.intro]

theorem shared_host_number (space : endAddress base H G M 3<2^w) :
    ((sharedHostCountBank base H G M).read final 0).val=Fintype.card (Site N) :=by
  have room_:=shared_host_fits base H G M w space
  have cap:=Fintype.card_le_of_injective host host.injective
  rw [Fintype.card_fin] at cap
  rw [shared_host_count]
  apply Fin.val_cast_of_lt
  have guard : (bank base H G M 3 4).base+H+1≤endAddress base H G M 3 :=room_.2.2
  omega

theorem mounted : Mounted P (roster X host) final G M := by
  obtain ⟨hcap,pcap,rcap⟩:=capacities H G M 3
  constructor
  · intro p i
    have key := read (H:=H) (G:=G) (M:=M) (D:=3) base vals m
      (c:=8+i.val) (by omega) ((row H G M p).isLt.trans_le rcap)
    refine key.trans (congrArg (fun n : ℕ => (n : Word w)) ?_)
    rw [Nat.add_comm 8 i.val]
    exact atPacked_row 0 (fun t : Row H G M => t.1.val * 3 + i.val) p
  · intro v i
    let u : Fin (H*3):=finProdFinEquiv (v,i)
    have lo : v.val*3+i.val< H*3 := by have := u.isLt; change i.val+3*v.val< H*3 at this;omega
    exact (read (H:=H) (G:=G) (M:=M) (D:=3) base vals m (c:=0) (by decide) (lo.trans_le pcap)).trans (congrArg (fun n : ℕ=>(n:Word w)) (peerWord_at X host v i))
  · intro v
    exact read (H:=H) (G:=G) (M:=M) (D:=3) base vals m (c:=1) (by decide) (v.isLt.trans_le hcap)
  · intro p
    exact (read (H:=H) (G:=G) (M:=M) (D:=3) base vals m (c:=2) (by decide) ((row H G M p).isLt.trans_le rcap)).trans
      (congrArg (fun n : ℕ=>(n:Word w)) (atPacked_row 0 (fun t : Row H G M=>t.2.val) p))

theorem actors : Reads (bank base H G M 3 3) (fun h (_ : Fin G)=>actorRow X host d h) M final := by
  intro p
  have cell:=read (H:=H) (G:=G) (M:=M) (D:=3) base vals m (c:=3) (by decide) ((row H G M p).isLt.trans_le (capacities H G M 3).2.2)
  let packed : Row H G M → ℕ := fun r =>
    (data (fun h (_ : Fin G) => actorRow X host d h) r).val
  exact cell.trans (congrArg (fun n : ℕ => (n : Word w)) (atPacked_row 0 packed p))

theorem hubs (h : Fin H) :
    final ((bank base H G M 3 4).base+h.val)=
      ((rack X host h).elim 0 (fun v=>if hubFlag N v then 1 else 0):Word w) := by
  have cell:=read (H:=H) (G:=G) (M:=M) (D:=3) base vals m (c:=4) (by decide) (h.isLt.trans_le (capacities H G M 3).1)
  rw [cell]
  simp [fields,atHost,h.isLt,Option.elim]
  all_goals split <;> simp_all

theorem atoms : Reads (bank base H G M 3 5)
    (fun h (_ : Fin G)=>(((rack X host h).elim (0 : ℕ) (records X) : ℕ) : Cell b)) M final := by
  intro p
  let packed : Row H G M → ℕ := fun r => (data (fun h (_ : Fin G) =>
    (((rack X host h).elim (0 : ℕ) (records X) : ℕ) : Cell b)) r).val
  exact (read (H:=H) (G:=G) (M:=M) (D:=3) base vals m (c:=5) (by decide) ((row H G M p).isLt.trans_le (capacities H G M 3).2.2)).trans
    (congrArg (fun n : ℕ=>(n:Word w)) (atPacked_row 0 packed p))

end
end Hierarchy.DescentSeedInitialTable

end OAI
