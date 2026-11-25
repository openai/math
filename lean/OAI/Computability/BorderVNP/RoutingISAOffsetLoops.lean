import OAI.Computability.BorderVNP.RoutingISAOffsetControl

/-! # Iterating the partner-prefix calculation over all three team coordinates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The single-partner instruction fragment returns the next prefix and cursor and
writes precisely the prefix at the current triple address. -/
def PartnerKernel {w : ℕ} (l : TableLayout) (row : ℕ → TableRow)
    (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) : Prop :=
  ∀ (u v j : ℕ), u < l.teams → v < l.teams → j < l.teams → ∀ (s : Bank w) (m : Memory w),
    l.ready (.ofWords s m) → (∀ i < l.teams^2, readings m (l.widths+i) = l.pairWidth row l.count i) →
    readings s 21 = u → readings s 22 = v → readings s 23 = j →
    readings s 20 = l.legPrefix row u v j →
    BoundedRun pub macros tabulatePartner s m tabulatePartner.slots (fun z =>
      l.ready z ∧ z.reg 21 = u ∧ z.reg 22 = v ∧ z.reg 23 = j+1 ∧
        z.reg 20 = l.legPrefix row u v (j+1) ∧
        z.mem = Function.update (readings m) (tripleIndex l.offsets l.teams u v j) (l.legPrefix row u v j))

variable {w : ℕ} {l : TableLayout} {row : ℕ → TableRow} {old : ℕ → ℕ}
  {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private def Inner (l : TableLayout) (row : ℕ → TableRow) (old : ℕ → ℕ) (u v j : ℕ) (z : NatState) : Prop :=
  l.ready z ∧ z.reg 21 = u ∧ z.reg 22 = v ∧ z.reg 23 = j ∧ z.reg 20 = l.legPrefix row u v j ∧
    OffsetMemory l row old z.mem ((u*l.teams+v)*l.teams+j) (u*l.teams+v)

private def Middle (l : TableLayout) (row : ℕ → TableRow) (old : ℕ → ℕ) (u v : ℕ) (z : NatState) : Prop :=
  l.ready z ∧ z.reg 21 = u ∧ z.reg 22 = v ∧
    OffsetMemory l row old z.mem ((u*l.teams+v)*l.teams) (u*l.teams+v)

private def Outer (l : TableLayout) (row : ℕ → TableRow) (old : ℕ → ℕ) (u : ℕ) (z : NatState) : Prop :=
  l.ready z ∧ z.reg 21 = u ∧ OffsetMemory l row old z.mem (u*l.teams*l.teams) (u*l.teams)

private theorem inner_run (ha : l.Allocated w)
    (hwidth : ∀ i < l.teams^2, old (l.widths+i) = l.pairWidth row l.count i)
    (step : PartnerKernel l row pub macros) {u v : ℕ} (hu : u < l.teams) (hv : v < l.teams)
    (s : Bank w) (m : Memory w) (h : Inner l row old u v 0 (.ofWords s m)) :
    BoundedRun pub macros (.whileLt 23 3 tabulatePartner) s m
      (l.teams*(tabulatePartner.slots+1)+1) (Inner l row old u v l.teams) := by
  have inc (j : ℕ) (hj : j < l.teams) (t : Bank w) (mt : Memory w)
      (inv : Inner l row old u v j (.ofWords t mt)) :
      BoundedRun pub macros tabulatePartner t mt tabulatePartner.slots (Inner l row old u v (j+1)) := by
    obtain ⟨hr,hr21,hr22,hr23,hr20,hm⟩ := inv
    have hw i hi := (hm.width ha hi).trans (hwidth i hi)
    apply (step u v j hu hv hj t mt hr hw hr21 hr22 hr23 hr20).mono le_rfl
    rintro z ⟨hready,h21,h22,h23,h20,hmem⟩
    refine ⟨hready,h21,h22,h23,h20,?_⟩
    rw [hmem]
    simpa only [NatState.ofWords, Nat.add_assoc] using hm.store_front hu hv hj ha
  exact run_counted_loop pub macros 23 3 _ l.teams tabulatePartner.slots (Inner l row old u v)
    (fun _ _ hi => ⟨hi.2.2.2.1, hi.1 3 (by decide)⟩) inc 0 (Nat.zero_le _) s m h

/-- Time allowance for processing one oriented pair of teams, including both loop resets. -/
def legCost (R : ℕ) := 1+(1+((R*(tabulatePartner.slots+1)+1)+legTail.slots))

private theorem leg_run (ha : l.Allocated w)
    (hwidth : ∀ i < l.teams^2, old (l.widths+i) = l.pairWidth row l.count i)
    (step : PartnerKernel l row pub macros) {u v : ℕ} (hu : u < l.teams) (hv : v < l.teams)
    (s : Bank w) (m : Memory w) (h : Middle l row old u v (.ofWords s m)) :
    BoundedRun pub macros tabulateLeg s m (legCost l.teams) (Middle l row old u (v+1)) := by
  obtain ⟨hr,h21,h22,hm⟩ := h
  apply (reset_cursor pub macros 20 (by decide) s m hr).seq
  rintro t mt ⟨hr',h20,p₁,m₁⟩
  apply (reset_cursor pub macros 23 (by decide) t mt hr').seq
  rintro t' mt' ⟨hr'',h23,p₂,m₂⟩
  have i21 := (p₂ 21 (by decide)).trans ((p₁ 21 (by decide)).trans h21)
  have i22 := (p₂ 22 (by decide)).trans ((p₁ 22 (by decide)).trans h22)
  have start : Inner l row old u v 0 (.ofWords t' mt') := by
    refine ⟨hr'',i21,i22,h23,?_,?_⟩
    · simpa [TableLayout.legPrefix] using (p₂ 20 (by decide)).trans h20
    · change OffsetMemory l row old (readings mt') _ _
      change readings mt' = readings mt at m₂
      change readings mt = readings m at m₁
      rw [Nat.add_zero, m₂, m₁]
      exact hm
  apply (inner_run ha hwidth step hu hv t' mt' start).seq
  rintro t₁ m₃ ⟨hr₁,h₂₁,h₂₂,_,h₂₀,hm₁⟩
  apply (legTail_image pub macros t₁ m₃ hr₁ ha hu hv h₂₁ h₂₂ h₂₀).mono le_rfl
  rintro z ⟨hrz,rz21,rz22,mz⟩
  refine ⟨hrz,rz21,rz22,?_⟩
  rw [mz, ← Nat.add_assoc, Nat.add_mul, Nat.one_mul]
  exact hm₁.store_total hu hv ha

private def oneEndpoint : Code := .block [.copy 22 0, .whileLt 22 3 tabulateLeg, .binary .add 21 21 1]

/-- Tick allowance for completing all relays of one endpoint. -/
def endpointCost (R : ℕ) := 1+((R*(legCost R+1)+1)+1)

private theorem endpoint_run (ha : l.Allocated w)
    (hwidth : ∀ i < l.teams^2, old (l.widths+i) = l.pairWidth row l.count i)
    (step : PartnerKernel l row pub macros) {u : ℕ} (hu : u < l.teams)
    (s : Bank w) (m : Memory w) (h : Outer l row old u (.ofWords s m)) :
    BoundedRun pub macros oneEndpoint s m (endpointCost l.teams) (Outer l row old (u+1)) := by
  obtain ⟨hr,h21,hm⟩ := h
  apply (reset_cursor pub macros 22 (by decide) s m hr).seq
  rintro t mt ⟨hr',h22,p₁,m₁⟩
  have start : Middle l row old u 0 (.ofWords t mt) := by
    refine ⟨hr', (p₁ 21 (by decide)).trans h21, h22, ?_⟩
    change OffsetMemory l row old (readings mt) _ _
    change readings mt = readings m at m₁
    rw [m₁]
    simpa only [Nat.add_zero,NatState.ofWords] using hm
  have loop := run_counted_loop pub macros 22 3 tabulateLeg l.teams (legCost l.teams)
    (Middle l row old u) (fun _ _ z => ⟨z.2.2.1,z.1 3 (by decide)⟩)
    (fun _ hv _ _ z => leg_run ha hwidth step hu hv _ _ z) 0 (Nat.zero_le _) t mt start
  apply loop.seq
  rintro t' mt' ⟨hr'',h₂₁,_,hm'⟩
  apply (advance_cursor pub macros 21 (by decide) t' mt' u hr'' h₂₁
    (lt_of_le_of_lt (show u+1 ≤ l.teams from hu) ha.teamsFit)).mono le_rfl
  rintro z ⟨hrz,rz,_,mz⟩
  refine ⟨hrz,rz,?_⟩
  rw [mz,Nat.add_mul,Nat.one_mul]
  exact hm'

/-- End-to-end native iteration of the certified one-partner instruction block,
with both output tables complete and all other words preserved. -/
theorem offsetPass_of_partnerKernel (s : Bank w) (m : Memory w) (ha : l.Allocated w)
    (hready : l.ready (.ofWords s m))
    (hwidth : ∀ i < l.teams^2, readings m (l.widths+i) = l.pairWidth row l.count i)
    (step : PartnerKernel l row pub macros) :
    BoundedRun pub macros offsetPass s m (128*(l.teams+1)^3) (fun z =>
      l.ready z ∧ (∀ u < l.teams, ∀ v < l.teams, ∀ j < l.teams,
        z.mem (tripleIndex l.offsets l.teams u v j) = l.legPrefix row u v j) ∧
      (∀ u < l.teams, ∀ v < l.teams,
        z.mem (pairIndex l.used l.teams u v) = l.legPrefix row u v l.teams) ∧
      ∀ i, ¬l.contains .offsets i → ¬l.contains .used i → z.mem i = readings m i) := by
  let old := readings m
  have r := (reset_cursor pub macros 21 (by decide) s m hready).seq (Q := Outer l row old l.teams)
    (b := Code.whileLt 21 3 oneEndpoint) (t := l.teams*(endpointCost l.teams+1)+1) (by
      rintro t mt ⟨hr,h21,_,hm⟩
      have start : Outer l row old 0 (.ofWords t mt) := by
        refine ⟨hr,h21,?_⟩
        change OffsetMemory l row old (readings mt) _ _
        change readings mt = readings m at hm
        simpa [hm,old] using (OffsetMemory.empty (l := l) (row := row) (old := readings m))
      exact run_counted_loop pub macros 21 3 oneEndpoint l.teams (endpointCost l.teams)
        (Outer l row old) (fun _ _ z => ⟨z.2.1,z.1 3 (by decide)⟩)
        (fun _ hu _ _ z => endpoint_run ha hwidth step hu _ _ z) 0 (Nat.zero_le _) t mt start)
  apply r.mono
  · have hp : tabulatePartner.slots ≤ 100 := by decide
    have ht : legTail.slots ≤ 10 := by decide
    dsimp only [endpointCost,legCost]
    nlinarith only [Nat.mul_le_mul_left (l.teams^3) hp, Nat.mul_le_mul_left (l.teams^2) ht]
  · rintro z ⟨hr,_,hm⟩
    refine ⟨hr,fun u hu v hv j hj => hm.front u hu v hv j hj ?_,
      fun u hu v hv => hm.total u hu v hv ?_,hm.other⟩
    · simpa [pow_succ] using tripleKey_bound hu hv hj
    · simpa [pow_two] using pairKey_bound hu hv

end RoutingISA

end BorderVNP
end Computability
end OAI
