import OAI.Hierarchy.DescentSelectedDonorRateNumbers
import OAI.Hierarchy.DescentPrivateDonorCalendar
import OAI.Hierarchy.DescentPrivateDonorUniform

namespace OAI
/-! # Charging the printed ordinary donor programs on every branch of the selected calendar -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree DescentRawCablePanel DescentSIMDLookup Filter
open scoped BigOperators Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits}
variable {start : Reached W₀ G q ε S k j z₀ D₀ wire hist} {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} {ticket : OrdinaryLink source he T c n target}
variable {header h K p : ℕ}

private theorem placement_dims {T₀ : StageInput W G u ε} (price : u=q*source.placement.wire)
    (placed : HEq T₀ source.placement.stage) : T₀.k=k ∧ T₀.Δ=source.placement.degree := by
  subst u
  cases eq_of_heq placed
  exact ⟨rfl,rfl⟩

theorem selected_amount (ticket : OrdinaryLink source he T c n target) :
    ticket.installedDonorWidth (max (k+3) (Nat.clog 2 (source.placement.degree+1)))
      (DescentTerminalEpochBits.width G.C)=donorAmount k source.placement.degree source.placement.cap G.b G.C G.k := by
  obtain ⟨row,d⟩:=placement_dims ticket.sourceRate ticket.placement
  unfold OrdinaryLink.installedDonorWidth OrdinaryLink.depotWidth OrdinaryLink.depotShape
  rw [row,d]
  rfl

theorem DonorVisit.dimensions (r : DonorVisit ticket header h bw K p) :
    r.grade≤donorGrade (2^k) source.placement.degree source.placement.cap ∧
    r.amount=donorAmount k source.placement.degree source.placement.cap G.b G.C G.k := by
  let short := max (k+3) (Nat.clog 2 (source.placement.degree+1))
  let fmt := ticket.depotShape short
  let matcher := DescentPacking.PackedMatch.Local.shape (2^k) source.placement.degree
    (2*source.placement.cap) (DescentTerminalEpochBits.width G.C)
  have work:=DepotRAM.Resident.field_work fmt matcher r.addresses (hostRows (S.hostSize i)) (S.groupCount i) (lanes h r.amount)
  change DepotRAM.fieldWork r.fields≤DepotRAM.Resident.fieldLimit (2^k) source.placement.degree source.placement.cap (2^(k+1)) at work
  constructor
  · have tables : r.tableCount=2*(5+((2^k)*(2*source.placement.cap)+(source.placement.degree+1+1)))+3+2^(k+1) :=rfl
    unfold grade gatherGrade donorGrade
    rw [tables,pow_succ,Nat.mul_comm ((2:ℕ)^k)]
    rw [pow_succ,Nat.mul_comm ((2:ℕ)^k)] at work
    have poly:=DepotRAM.Resident.field_limit_quartic
      (r:=2^k) (D:=source.placement.degree) (cap:=source.placement.cap) (K:=2*2^k)
      (N:=max (2^k) (max (source.placement.degree+1) (max source.placement.cap (2*2^k))))
      (by omega) (by omega) (by omega) (by omega)
    omega
  · exact selected_amount ticket

theorem OrdinaryLink.degree_limit (ticket : OrdinaryLink source he T c n target) :
    source.placement.degree≤ maximumDegree S.rounds := by
  obtain ⟨n,hn,deg⟩:=ticket.degreeSlot
  rw [source.branch,deg]
  exact Finset.single_le_sum (f:=fun j:Fin S.rounds=>atRound j.val) (fun _ _=>Nat.zero_le _) (Finset.mem_univ (⟨n,hn⟩:Fin S.rounds))

theorem selected_input_bounds (ticket : OrdinaryLink source he T c n target) {f t J g reset M tail s a : ℕ}
    (schedule : S=stageNumbers G t J f g reset M tail)
    (radix : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (rates : ∀J₀ D₁ cap : ℕ,D₁≤ maximumDegree t→cap≤2^(8+capRate G t g*((t+1)*J₀))→
      let bits₀:=groupBits t J₀ (hostRate t reset) (capRate G t g) (cutRate t f g)
      donorGrade (2^bits₀) D₁ cap≤ scale J₀ s ∧ donorAmount bits₀ D₁ cap G.b G.C G.k≤ scale J₀ a) :
    donorGrade (2^k) source.placement.degree source.placement.cap≤ scale J s ∧
    donorAmount k source.placement.degree source.placement.cap G.b G.C G.k≤ scale J a := by
  subst S
  have degMax:=OrdinaryLink.degree_limit ticket
  have ti : i≤(t+1)*J:=ticket.hubRows.choose.le
  have cap := source.valid.capacity.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (Nat.add_le_add_left (Nat.mul_le_mul_left (capRate G t g) ti) 8))
  obtain ⟨work,words⟩:=rates J _ _ degMax cap
  rw [←radix] at work words
  exact ⟨work,words⟩

private theorem date_bound (r : DonorVisit ticket header h bw K p) {f t J g reset M tail s a : ℕ}
    (schedule : S=stageNumbers G t J f g reset M tail)
    (radix : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (rates : ∀J₀ D₁ cap : ℕ,D₁≤ maximumDegree t→cap≤2^(8+capRate G t g*((t+1)*J₀))→
      let bits₀:=groupBits t J₀ (hostRate t reset) (capRate G t g) (cutRate t f g)
      donorGrade (2^bits₀) D₁ cap≤ scale J₀ s ∧ donorAmount bits₀ D₁ cap G.b G.C G.k≤ scale J₀ a) :
    r.grade≤ scale J s ∧ r.amount≤ scale J a := by
  obtain ⟨work,words⟩:=selected_input_bounds ticket schedule radix rates
  exact ⟨r.dimensions.1.trans work,r.dimensions.2.le.trans words⟩

private theorem rows_bound {path : Path start source} {calendar : MeterCalendar start header bw path} (diary : DonorDiary start header h bw K p calendar)
    {t J f g reset M tail s a : ℕ} (schedule : S=stageNumbers G t J f g reset M tail)
    (radix : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (rates : ∀J₀ D₁ cap : ℕ,D₁≤ maximumDegree t→cap≤2^(8+capRate G t g*((t+1)*J₀))→
      let bits₀:=groupBits t J₀ (hostRate t reset) (capRate G t g) (cutRate t f g)
      donorGrade (2^bits₀) D₁ cap≤ scale J₀ s ∧ donorAmount bits₀ D₁ cap G.b G.C G.k≤ scale J₀ a)
    (v : ℕ) : (diary.rows v).work≤ scale J s ∧ (diary.rows v).amount≤ scale J a := by
  induction diary with
  | seed=>exact ⟨Nat.zero_le _,Nat.zero_le _⟩
  | ordinary prior r _ ih | ordinaryAfter prior r _ _ ih=>
    by_cases hit:v=r.age
    · subst v
      simpa only [DonorDiary.rows,Function.update_self] using date_bound r schedule radix rates
    · simpa only [DonorDiary.rows,Function.update_of_ne hit] using ih
  | reset prior closed emit ih=>exact ih

/-- Before allocating memory, each actual incoming ordinary row already fits the
same packed word used by the run. This proof has no `DonorVisit` premise. -/
theorem selected_word_room_at (G : PoweredGadget F) (t f g reset e τ : ℕ) :
    let s:=(donorRates G t f g reset).work
    let a:=(donorRates G t f g reset).amount
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀ B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀M : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
        {u q ε : ℝ} {i z z' D D' wire hist : ℕ}
        {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
        {c : (T.result he).Choice} {nrm : Normalize ((T.result he).state c)}
        {target : Reached nrm.result G q ε S k (i+1) z' D' wire hist}
        (ticket : OrdinaryLink source he T c nrm target),
        let amount:=ticket.installedDonorWidth (max (k+3) (Nat.clog 2 (source.placement.degree+1)))
          (DescentTerminalEpochBits.width G.C)
        0<amount ∧ 2*amount≤h := by
  let s:=(donorRates G t f g reset).work
  let a:=(donorRates G t f g reset).amount
  have rates:=(donorRates G t f g reset).bounds
  intro _ _ _ B positive big
  filter_upwards [AgeBound.payload_room a B (by omega)] with h room
  dsimp only
  intro M P d bits W u q ε i z z' D D' wire hist source he T c nrm target ticket
  constructor
  · exact (by omega : 0<2*DepotRAM.totalBits (ticket.depotShape _)+1).trans_le
      (le_max_right .. |>.trans (le_max_right ..))
  · rw [selected_amount ticket]
    exact (Nat.mul_le_mul_left 2 (selected_input_bounds ticket rfl rfl rates).2).trans room

theorem selected_word_room (G : PoweredGadget F) (t f g reset e : ℕ) :
    let s:=(donorRates G t f g reset).work
    let a:=(donorRates G t f g reset).amount
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀ B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀M : ℕ,let S:=stageNumbers G t J f g reset M (tail ((donorRates G t f g reset).work+3+(e+5)) J)
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
        {u q ε : ℝ} {i z z' D D' wire hist : ℕ}
        {source : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
        {c : (T.result he).Choice} {nrm : Normalize ((T.result he).state c)}
        {target : Reached nrm.result G q ε S k (i+1) z' D' wire hist}
        (ticket : OrdinaryLink source he T c nrm target),
        let amount:=ticket.installedDonorWidth (max (k+3) (Nat.clog 2 (source.placement.degree+1)))
          (DescentTerminalEpochBits.width G.C)
        0<amount ∧ 2*amount≤h := by
  intro s a n B hb big
  exact selected_word_room_at G t f g reset e ((donorRates G t f g reset).work+3+(e+5)) B hb big

/-- The literal six resident fields, three date directories, packed meter, and fixed native
opcodes of every ordinary visit satisfy the joint bound for the chosen physical calendar. -/
theorem native_donor_history_at (G : PoweredGadget F) (t f g reset e K τ : ℕ)
    (tailRoom : (donorRates G t f g reset).work+3+(e+5)≤τ) :
    let s:=(donorRates G t f g reset).work
    let a:=(donorRates G t f g reset).amount
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀ B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀ M socket p : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      2^h≤2*M → p≤h → 0<socket → socket≤ scale J e → h≤32*(socket*p) →
      ∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W₀ W : MarkedWorld F d P bits}
        {q ε : ℝ} {j z₀ D₀ z D wire hist header bw : ℕ}
        {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
        {finish : Reached W G q ε S k S.length z D wire hist}
        {path : Path start finish} {calendar : MeterCalendar start header bw path},
        ∀diary : DonorDiary start header h bw K p calendar,diary.total*2^J≤2*(M*(S.copies*p)) := by
  let s:=(donorRates G t f g reset).work
  let a:=(donorRates G t f g reset).amount
  have rates:=(donorRates G t f g reset).bounds
  intro _ _ _ B hB big
  filter_upwards [calibrated_donor_history_at G t f g reset s a e K τ tailRoom B hB big] with h bound
  dsimp only
  intro M socket p₀ major core visits near cpu P d bits W₀ W q ε j z₀ D₀ z D wire hist header bw start finish path calendar diary
  exact bound M socket p₀ major core visits near cpu diary (fun v=>(rows_bound diary rfl rfl rates v.val).1)
    (fun v=>(rows_bound diary rfl rfl rates v.val).2)

theorem native_donor_history (G : PoweredGadget F) (t f g reset e K : ℕ) :
    let s:=(donorRates G t f g reset).work
    let a:=(donorRates G t f g reset).amount
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀ B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀ M socket p : ℕ, let S:=stageNumbers G t J f g reset M (tail ((donorRates G t f g reset).work+3+(e+5)) J)
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      2^h≤2*M → p≤h → 0<socket → socket≤ scale J e → h≤32*(socket*p) →
      ∀ {P : Type} {d : ℕ} {bits : P→ℕ} {W₀ W : MarkedWorld F d P bits}
        {q ε : ℝ} {j z₀ D₀ z D wire hist header bw : ℕ}
        {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
        {finish : Reached W G q ε S k S.length z D wire hist}
        {path : Path start finish} {calendar : MeterCalendar start header bw path},
        ∀diary : DonorDiary start header h bw K p calendar,diary.total*2^J≤2*(M*(S.copies*p)) := by
  intro s a n B hb big
  exact native_donor_history_at G t f g reset e K ((donorRates G t f g reset).work+3+(e+5)) le_rfl B hb big

end
end Hierarchy.DescentSixParty.Chronology

end OAI
