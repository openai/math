import OAI.Hierarchy.ProtocolRAMCalendarStockBanks
import OAI.Hierarchy.ProtocolRAMCalendarPrevious
import OAI.Hierarchy.ProtocolRAMPurchaseInventory
import OAI.Hierarchy.ProtocolRAMCalendarSegments
import OAI.Hierarchy.ProtocolRAMCalendarMarketFrame

namespace OAI
/-! # Induction over the physical active and saved stock words of the calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockBound
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe
open scoped Classical Fin.CommRing
variable {w q goods z N k : ℕ}

/-- Each commodity is read at its native lane and row in the specified bank. -/
def Bounded (z N k base ceiling : ℕ) (m : Memory w) : Prop :=
  ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock base m i≤ ceiling

def Banks.receipts (b : Banks) (c : Mesh) (z N k ceiling j : ℕ) (m : Memory w) : Prop :=
  Bounded z N k b.initial ceiling m ∧ Bounded z N k b.zeroReserve ceiling m ∧
    ∀u : Fin (events c).length,u.val< j→∀base∈b.publications ((events c)[u.val]),Bounded z N k base ceiling m

theorem parent_before (c : Mesh) (e : Event) (a : Attempt) (live : e∈events c) (source : parent e=some a) :
    Event.attempt a∈events c ∧ position c (.attempt a)< position c e := by
  obtain ⟨p,hp,occ⟩ := List.mem_flatMap.mp live
  rcases List.mem_append.mp occ with trials|close
  · obtain ⟨t,ht,occ⟩ := List.mem_flatMap.mp trials
    have head : Event.attempt (.outer p t)∈events c := List.mem_flatMap.mpr ⟨p,hp,List.mem_append_left _
      (List.mem_flatMap.mpr ⟨t,ht,List.mem_cons_self ..⟩)⟩
    rcases List.mem_cons.mp occ with rfl|inside
    · simp [parent] at source
    obtain ⟨j,_,site⟩ := List.mem_flatMap.mp inside
    rcases List.mem_append.mp site with repair|feed
    · obtain ⟨r,_,rfl⟩ := List.mem_map.mp repair
      have eq : Attempt.outer p t=a := Option.some.inj source
      subst a
      exact ⟨head,by simp only [position,sliceBase];omega⟩
    · have eq := List.mem_singleton.mp feed
      subst e
      have eq : Attempt.outer p t=a := Option.some.inj source
      subst a
      exact ⟨head,by simp only [position,sliceBase];omega⟩
  · have eq := List.mem_singleton.mp close
    subst e
    simp [parent] at source

theorem Banks.previous_at (b : Banks) (c : Mesh) {j ceiling : ℕ} {m : Memory w}
    (e : Event) (atCursor : position c e=j) (known : b.receipts c z N k ceiling j m) :
    Bounded z N k (b.previous c e) ceiling m := by
  subst j
  by_cases h : 0<position c e ∧ position c e≤(events c).length
  · simp only [Banks.previous,previousStock,dite_eq_left h]
    let i : Fin (events c).length := ⟨position c e-1,by omega⟩
    apply known.2.2 i (by dsimp [i];omega) _
    change b.active ((events c)[i.val])∈b.publications ((events c)[i.val])
    cases (events c)[i.val] <;> simp [Banks.publications]
  · simpa only [Banks.previous,previousStock,dite_eq_right h] using known.1

theorem Banks.inputs (b : Banks) (c : Mesh) {ceiling : ℕ} (u : Fin (events c).length) {m : Memory w}
    (known : b.receipts c z N k ceiling u.val m) :
    let e := (events c)[u.val]
    Bounded z N k (b.previous c e) ceiling m ∧ Bounded z N k (b.reserve e) ceiling m := by
  let e := (events c)[u.val]
  have index : position c e=u.val := position_at c u.isLt
  constructor
  · exact b.previous_at c e index known
  · change Bounded z N k ((parent e).elim b.zeroReserve b.saved) ceiling m
    cases hp : parent e with
    | none => exact known.2.1
    | some a =>
      obtain ⟨mem,prec⟩ := parent_before c e a (List.getElem_mem _) hp
      obtain ⟨v,hv,eq⟩ := List.getElem_of_mem mem
      have earlier := position_at c hv
      rw [eq] at earlier
      have hlt : v< u.val := by omega
      have live : b.saved a∈b.publications ((events c)[v]) := by rw [eq];simp [Banks.publications]
      exact known.2.2 ⟨v,hv⟩ hlt _ live

def state (C : Chart w q goods) (start : Memory w) (j : ℕ) := run C ((events C.mesh).take j) start

theorem state_succ (C : Chart w q goods) (start : Memory w) (j : ℕ) (ok : j< (events C.mesh).length) :
    state C start (j+1)=after C ((events C.mesh)[j]) (state C start j) := by
  rw [state,List.take_succ_eq_append_getElem ok,run_append]
  rfl

def Run (C : Chart w q goods) (b : Banks) (start : Memory w) (z N k ceiling : ℕ) : Prop :=
  ∀j≤(events C.mesh).length,mounted C ((events C.mesh).take j) start ∧ b.receipts C.mesh z N k ceiling j (state C start j)

/-- Local readiness may use the *proved* frozen active and held bounds. Each
archive lives in its issuing arena slab, so all later events preserve it. -/
theorem chronological (C : Chart w q goods) (arena : Arena) (b : Banks) (start : Memory w) (z N k ceiling : ℕ)
    (initial : ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock b.initial start i=0)
    (vacant : ∀i : Commodity (Fin (2^z)) N k,PurchaseInventory.stock b.zeroReserve start i=0)
    (initialSpan : b.initial+PurchaseInventory.footprint z N k≤ arena.first)
    (reserveSpan : b.zeroReserve+PurchaseInventory.footprint z N k≤ arena.first)
    (span : ∀e∈events C.mesh,∀base∈b.publications e,base+PurchaseInventory.footprint z N k≤ arena.base C.mesh e+arena.stride)
    (outsideLow : ∀e∈events C.mesh,∀x< arena.base C.mesh e,outside C x e)
    (advance : ∀u : Fin (events C.mesh).length,
      let e := (events C.mesh)[u.val]
      let m := state C start u.val
      mounted C ((events C.mesh).take u.val) start →
      Bounded z N k (b.previous C.mesh e) ceiling m → Bounded z N k (b.reserve e) ceiling m →
      ready C e m ∧ ∀base∈b.publications e,Bounded z N k base ceiling (after C e m)) :
    ∀j≤ (events C.mesh).length,mounted C ((events C.mesh).take j) start ∧ b.receipts C.mesh z N k ceiling j (state C start j) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨True.intro,(fun i=>(initial i).le.trans (Nat.zero_le _)),(fun i=>(vacant i).le.trans (Nat.zero_le _)),?_⟩
    intro u hu;omega
  | succ j ih =>
    intro hj
    have lt : j< (events C.mesh).length := hj
    let u : Fin (events C.mesh).length := ⟨j,lt⟩
    let e := (events C.mesh)[j]
    let m := state C start j
    have live : e∈events C.mesh := List.getElem_mem _
    have index : position C.mesh e=j := position_at C.mesh lt
    obtain ⟨ran,known⟩ := ih lt.le
    obtain ⟨old,saved⟩ := b.inputs C.mesh u known
    obtain ⟨can,published⟩ := advance u ran old saved
    have protect (base : ℕ) (low : base+PurchaseInventory.footprint z N k≤ arena.base C.mesh e)
        (stored : Bounded z N k base ceiling m) : Bounded z N k base ceiling (after C e m) := by
      intro i
      have hi := (Nat.add_lt_add_left (PurchaseInventory.slot_lt i) base).trans_le low
      change ((after C e m) (base+PurchaseInventory.slot i)).val≤ ceiling
      rw [after_outside C e m _ can (outsideLow e live _ hi)]
      exact stored i
    have floor : arena.first≤ arena.base C.mesh e := Nat.le_add_right ..
    refine ⟨?_,?_⟩
    · rw [List.take_succ_eq_append_getElem lt,mounted_append]
      exact ⟨ran,can,True.intro⟩
    · rw [state_succ C start j lt]
      refine ⟨protect _ (initialSpan.trans floor) known.1,protect _ (reserveSpan.trans floor) known.2.1,?_⟩
      intro v hv base member
      by_cases last : v.val=j
      · simpa only [last] using published base (by simpa only [last] using member)
      · have earlier : v.val< j := by omega
        have before : position C.mesh ((events C.mesh)[v.val])< position C.mesh e := by
          rw [position_at C.mesh v.isLt,index];exact earlier
        exact protect _ ((span _ (List.getElem_mem _) base member).trans (arena.apart C.mesh before))
          (known.2.2 v earlier base member)

end Hierarchy.ProtocolRAM.Calendar.StockBound
end

end OAI
