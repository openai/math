import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentOrdinaryDonorSample

namespace OAI
/-! # Equality of the fixed eleven-lane donor slab and the actual raw-edge panel -/

namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSixParty DescentSharedCableNames DescentCableDonorNames DescentHostDirectory
open scoped Classical
noncomputable section
variable {I P C V F J : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    [Field F] [Fintype J] [DecidableEq J] {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable {H R k hCode i a s : ℕ}
variable (A : GroupStage W G price ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (old : W.graph.Edge↪ℕ) (vertex : V↪Fin H) (group : J≃Fin R) (pick : I×Fin 2↪W.graph.Edge)
local notation "N" => W.graph
local notation "donorSpan" => R*2^k*A.cap
def oldSlot : Stage.Positive A↪Fin H×Fin donorSpan where
  toFun u := (vertex (A.pos ((N).src u.val)).2,finProdFinEquiv
    (finProdFinEquiv (group (A.pos ((N).src u.val)).1,A.block ((N).src u.val)),Stage.outgoing A old S ready u))
  inj' := by
    intro u v same
    have hv:=vertex.injective (congrArg Prod.fst same)
    have outer:=finProdFinEquiv.injective (congrArg Prod.snd same)
    have mid:=finProdFinEquiv.injective (congrArg Prod.fst outer)
    have pos : A.pos (W.graph.src u.val) = A.pos (W.graph.src v.val) :=
      Prod.ext (group.injective (congrArg Prod.fst mid)) hv
    have blockEq : A.block (W.graph.src u.val) = A.block (W.graph.src v.val) :=
      congrArg (fun x : Fin R × _ => x.2) mid
    have site : W.graph.src u.val = W.graph.src v.val := ready.coordinates (Prod.ext pos blockEq)
    exact Stage.outgoing_identify A old S ready _ _ site (congrArg Prod.snd outer)

local notation "address" => oldSlot A S ready old vertex group
local notation "rawSlot" => slot A S ready old vertex group pick

omit [Fintype I] [DecidableEq I] in
theorem split_slot (e : Live A pick) :
    let t:=address ⟨anchor pick e.val,e.property⟩
    rawSlot e=(t.1,finProdFinEquiv (t.2,role e.val)) := rfl

omit [Fintype I] [DecidableEq I] in
/-- The physical eleven-role slab retains the original positive source
outgoing ordinal and the raw old/arm/supply role in its two lowest digits. -/
theorem slot_digits (e : Live A pick) :
    ((rawSlot e).2.val/11)%A.cap=(Stage.outgoing A old S ready ⟨anchor pick e.val,e.property⟩).val ∧
      (rawSlot e).2.val%11=(role e.val).val := by
  let u : Stage.Positive A:=⟨anchor pick e.val,e.property⟩
  let t:=address u
  have both:=finProdFinEquiv.symm_apply_apply (t.2,role e.val)
  have x:=congrArg (fun pair=>pair.1.val) both
  have y:=congrArg (fun pair=>pair.2.val) both
  change (rawSlot e).2.val/11=t.2.val at x
  change (rawSlot e).2.val%11=(role e.val).val at y
  refine ⟨?_,y⟩
  rw [x]
  let b:=finProdFinEquiv (group (A.pos ((N).src u.val)).1,A.block ((N).src u.val))
  exact congrArg (fun p=>p.2.val) (finProdFinEquiv.symm_apply_apply (b,Stage.outgoing A old S ready u))

theorem no_roles (k g slots s a c : ℕ) (r : Fin 11) : report k g slots (emptyDonor s a c) r=0 := by
  refine Fin.cases ?_ (fun t=>?_) r
  · simp [report,emptyDonor]
  · refine Fin.addCases (m:=2) (n:=8) (motive := fun i : Fin (2 + 8) =>
        report k g slots (emptyDonor s a c) i.succ = 0) ?_ ?_ t
    · intro arm
      rw [arm_report]; rfl
    · intro wire
      rw [supply_report]; rfl

variable (layout : Bool) (pack : W.graph.Site→C) (rank : J×V↪ℕ) (key : Merged W.graph pick layout pack→Key (J×V))
    (hub : J×V→Bool) (g slots : ℕ) (valid : ∀q,key q∈keys hCode slots) (ids : 2^(hCode+1)*slots≤2^a)
variable (profile : I→Profile G.C)
local notation "c" => normBits A.cap G.b G.C G.k
variable (localID : W.graph.Edge→W.graph.Site→Cell s)
variable (chart : ∀ (e : W.graph.Edge) (u v : W.graph.Site),
    u ∈ terms pick e → v ∈ terms pick e →
      (localID e u = localID e v ↔
        (Prod.fst (key (newSite W.graph pick layout pack (Sum.inl u))) : J × V) =
          Prod.fst (key (newSite W.graph pick layout pack (Sum.inl v)))))
local notation "donor" => measuredDonor (a:=a) (hCode:=hCode) A S ready pick layout pack key hub slots profile localID
local notation "samp" => sample (hCode:=hCode) A S ready pick layout pack rank key hub g slots profile

def physicalRows (v : Fin H) (j : Fin donorSpan) : Donor s a c :=
  if present : ∃e,address e=(v,j) then donor present.choose else emptyDonor s a c

local notation "rows" => physicalRows (a:=a) (hCode:=hCode) A S ready old vertex group pick layout pack key hub slots profile localID

omit [DecidableEq I] in
theorem occupied_read (e : Stage.Positive A) : rows (address e).1 (address e).2=donor e := by
  have yes : ∃t,address t=((address e).1,(address e).2):=⟨e,rfl⟩
  simp only [physicalRows,dite_eq_left yes]
  rw [(address).injective yes.choose_spec]

include valid ids chart in
omit [DecidableEq I] in
theorem donor_panel (v : Fin H) (j : Fin (span R k A.cap)) :
    report hCode g slots (rows v (finProdFinEquiv.symm j).1) (finProdFinEquiv.symm j).2 =
      place rawSlot samp v j := by
  let query (z : Fin H×Fin (span R k A.cap)):=report hCode g slots (rows z.1 (finProdFinEquiv.symm z.2).1) (finProdFinEquiv.symm z.2).2
  change query (v,j)=_
  by_cases existsE : ∃e,rawSlot e=(v,j)
  · rw [place,dite_eq_left existsE]
    refine (congrArg query existsE.choose_spec.symm).trans ?_
    suffices filled : ∀ e : Live A pick, query (rawSlot e) = samp e from filled existsE.choose
    intro e
    simp only [query,split_slot,Equiv.symm_apply_apply,occupied_read]
    obtain ⟨q,hq⟩:=e
    rcases q with e|⟨u,t⟩|⟨u,t⟩
    · exact live_old (hCode:=hCode) A S ready pick layout pack rank key hub g slots valid ids profile localID chart ⟨e,hq⟩
    · exact live_arm (hCode:=hCode) A S ready pick layout pack rank key hub g slots profile localID u t hq
    · exact live_supply (hCode:=hCode) A S ready pick layout pack rank key hub g slots valid ids profile localID chart u t hq
  · rw [place,dite_eq_right existsE]
    obtain ⟨⟨j,r⟩,rfl⟩ := (finProdFinEquiv (m:=donorSpan) (n:=11)).surjective j
    simp only [query,Equiv.symm_apply_apply]
    by_cases live : ∃e,address e=(v,j)
    · obtain ⟨e,he⟩:=live
      have here : rows v j=donor e := by
        simpa only [he] using (occupied_read (a:=a) (hCode:=hCode) A S ready old vertex group pick
          layout pack key hub slots profile localID e)
      rw [here]
      have absent (raw : Raw (N).Edge I) (tagE : anchor pick raw=e.val) : role raw≠r := by
        intro eq
        let q : Live A pick:=⟨raw,tagE.symm ▸ e.property⟩
        have back : (⟨anchor pick q.val,q.property⟩:Stage.Positive A)=e:=Subtype.ext tagE
        have roleEq : role q.val = r := eq
        apply existsE
        refine ⟨q,(split_slot A S ready old vertex group pick q).trans ?_⟩
        rw [back,he,roleEq]
        rfl
      revert absent
      refine Fin.cases (fun absent=>?_) (fun t absent=>?_) r
      · exact False.elim (absent (.inl e.val) rfl rfl)
      · cases firstRead:first pick e.val with
        | none=>
          refine Fin.addCases (m:=2) (n:=8) (motive := fun i : Fin (2 + 8) =>
            report hCode g slots (donor e) i.succ = 0) ?_ ?_ t
          · intro arm
            rw [arm_report]; simp [measuredDonor,firstRead]
          · intro wire
            rw [supply_report]; simp [measuredDonor,firstRead]
        | some u=>
          have original:=first_spec pick firstRead
          have found : ∀ i : Fin (2 + 8), ∃ raw : Raw (N).Edge I,
              anchor pick raw = e.val ∧ role raw = i.succ := by
            intro i
            refine Fin.addCases (m:=2) (n:=8) (motive := fun z : Fin (2 + 8) => ∃ raw : Raw (N).Edge I,
              anchor pick raw = e.val ∧ role raw = z.succ) ?_ ?_ i
            · intro arm
              exact ⟨.inr (.inl (u,arm)),original,Fin.ext (by simp [role]; omega)⟩
            · intro wire
              exact ⟨.inr (.inr (u,wire)),original,Fin.ext (by simp [role]; omega)⟩
          obtain ⟨raw,anchored,atRole⟩ := found t
          exact False.elim (absent raw anchored atRole)
    · simp only [physicalRows,dite_eq_right live,no_roles]

end
end Hierarchy.DescentRawCablePanel

end OAI
