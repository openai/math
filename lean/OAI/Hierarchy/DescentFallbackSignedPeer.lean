import OAI.Hierarchy.DescentIssuedFallbackPanel

namespace OAI
/-! # Recovering the opposite old host from the signed compact port fields -/

namespace Hierarchy.DescentIssuedFallbackPanel
open DescentSharedCableNames Stage DescentSixParty
open scoped Classical
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i)
variable (names : Stage.Host J V k ↪ ℕ)

def physicalPeer (A : GroupStage W G q ε J V k) (names : Stage.Host J V k ↪ ℕ)
    (h : Stage.Host J V k) (j : Fin A.degree) : Option (Stage.Host J V k) :=
  let ix:=Ends.neighborOrder (Stage.near A) names (Stage.near_room A) h
  if yes : ∃v,ix v=j then some yes.choose.val else none

theorem physicalPeer_read (h : Stage.Host J V k) (p : A.CellPorts h.1.1 h.1.2 h.2) :
    physicalPeer A names h (Stage.live A native S ready names h p).neighbor=
      some ((Stage.source A native).peer h (Stage.ofPort A native h p).val) := by
  let v:=((Stage.source A native).peer h (Stage.ofPort A native h p).val)
  let ix:=Ends.neighborOrder (Stage.near A) names (Stage.near_room A) h
  have inRoster : v∈Stage.near A h := (Stage.source A native).peer_mem (Stage.near A)
    (Stage.connected A native) h (Stage.ofPort A native h p)
  let dest : ↥(Stage.near A h):=⟨v,inRoster⟩
  change (if found : ∃a,ix a=ix dest then some found.choose.val else none)=some v
  have hit : ∃a,ix a=ix dest:=⟨dest,rfl⟩
  rw [dite_eq_left hit,ix.injective hit.choose_spec]

def signedPeer (A : GroupStage W G q ε J V k) (native : W.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (names : Stage.Host J V k ↪ ℕ) (s : Bool) (h : Stage.Host J V k)
    (j : Fin (2*A.cap)) : Option (Stage.Host J V k) := do
  let z←Stage.signedPanel A native S ready names h j
  if z.target=s then physicalPeer A names h z.neighbor else none

theorem opposite_home (s : Bool) (e : Stage.Grain A) :
    (Stage.source A native).peer (Stage.home A (endSite A s e)) (Stage.stream A native e)=
      Stage.home A (endSite A (!s) e) := by
  cases s
  · simp [Ends.peer,Stage.source,endSite]
  · simp only [Ends.peer,Stage.source,Equiv.symm_apply_apply,endSite,Bool.false_eq_true,
      Bool.not_true,ite_false,ite_true]
    split <;> simp_all

theorem signedPeer_actual (s : Bool) (e : Stage.Grain A) :
    let p:=port A s e
    signedPeer A native S ready names s p.1 (Stage.signed A native S ready p.1.1 p.1.2 p.2)=
      some (Stage.home A (endSite A (!s) e)) := by
  dsimp only
  have target : (Stage.live A native S ready names (port A s e).1 (port A s e).2).target = s := by
    cases s <;> rfl
  have wire : (Stage.ofPort A native (port A s e).1 (port A s e).2).val = Stage.stream A native e := by
    cases s <;> rfl
  unfold signedPeer
  rw [Stage.signed_read]
  change (if (Stage.live A native S ready names (port A s e).1 (port A s e).2).target = s
    then physicalPeer A names (port A s e).1 (Stage.live A native S ready names (port A s e).1 (port A s e).2).neighbor
    else none) = _
  rw [ite_eq_left target, physicalPeer_read, wire, port_fst, opposite_home]

theorem from_any (h : Stage.Host J V k) (p : A.CellPorts h.1.1 h.1.2 h.2) :
    let s:=(Stage.live A native S ready names h p).target
    let e:=Stage.recover A h p
    port A s e=⟨h,p⟩ := by
  rcases h with ⟨⟨j,v⟩,x⟩
  cases p with
  | inl p=>
    rcases p with ⟨⟨e,ep,ex⟩,u⟩
    obtain rfl : (A.pos (W.graph.src e)).1=j:=congrArg Prod.fst ep
    obtain rfl : (A.pos (W.graph.src e)).2=v:=congrArg Prod.snd ep
    change A.block (W.graph.src e) = x at ex
    subst x
    rfl
  | inr p=>
    rcases p with ⟨⟨e,ep,ex⟩,u⟩
    obtain rfl : (A.pos (W.graph.dst e)).1=j:=congrArg Prod.fst ep
    obtain rfl : (A.pos (W.graph.dst e)).2=v:=congrArg Prod.snd ep
    change A.block (W.graph.dst e) = x at ex
    subst x
    rfl

theorem signedPeer_slot (s : Bool) (h : Stage.Host J V k) (j : Fin (2*A.cap)) :
    signedPeer A native S ready names s h j=
      (atSlot A native S ready s h j).map (fun e=>Stage.home A (endSite A (!s) e)) := by
  cases a : atSlot A native S ready s h j with
  | some e=>
    have addr:=(atSlot_iff A native S ready s h j e).mp a
    obtain ⟨h',p,hp⟩ : ∃ h' : Stage.Host J V k, ∃ p : A.CellPorts h'.1.1 h'.1.2 h'.2,
        port A s e = ⟨h',p⟩ := ⟨(port A s e).1,(port A s e).2,rfl⟩
    have val:=signedPeer_actual A native S ready names s e
    rw [hp] at addr val
    have hostEq : h'=h := congrArg Prod.fst addr
    subst h'
    have slotEq : Stage.signed A native S ready h.1 h.2 p=j := congrArg Prod.snd addr
    rw [←slotEq]
    exact val
  | none=>
    by_cases used : ∃ p : A.CellPorts h.1.1 h.1.2 h.2, Stage.signed A native S ready h.1 h.2 p=j
    · obtain ⟨p,rfl⟩:=used
      have bad : (Stage.live A native S ready names h p).target≠s := by
        intro same
        let e:=Stage.recover A h p
        have eqn:=from_any A native S ready names h p
        change port A (Stage.live A native S ready names h p).target e = ⟨h,p⟩ at eqn
        rw [same] at eqn
        have yes := (atSlot_iff A native S ready s h (Stage.signed A native S ready h.1 h.2 p) e).mpr
          (congrArg (address A native S ready) eqn)
        rw [a] at yes
        contradiction
      simp [signedPeer,Stage.signed_read,bad]
    · simp [signedPeer,Stage.signed_empty A native S ready names h _ (not_exists.mp used)]

end
end Hierarchy.DescentIssuedFallbackPanel

end OAI
