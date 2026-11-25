import OAI.Hierarchy.DescentCoarseCoordinates
import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentFlattenGroups
import OAI.Hierarchy.DescentResetSourceFrame

namespace OAI
/-! # Recovering all arriving grains from a terminal's local phase cells -/

namespace Hierarchy.DescentIssuedFallbackPanel
open DescentSixParty DescentColonies DescentGL DescentSharedCableNames DescentSharedCableNames.Stage
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k m c i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
    (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (basis : Layout m) (fits : c≤ m)
local notation "E" => Stage.Grain A
local notation "H" => Stage.Host J V k
local notation "cap" => 2*A.cap
local notation "signed" => Stage.signed A native S ready
local notation "remix" => rearrange basis

private abbrev CellPort (h : H) := A.CellPorts h.1.1 h.1.2 h.2

def endSite (s : Bool) (e : E) : W.graph.Site :=
  if s then W.graph.dst e.1 else W.graph.src e.1

def port (s : Bool) (e : E) : Σh : H,CellPort A h :=
  match s with
  | false=>⟨Stage.home A (W.graph.src e.1),.inl ⟨⟨e.1,rfl,rfl⟩,e.2⟩⟩
  | true=>⟨Stage.home A (W.graph.dst e.1),.inr ⟨⟨e.1,rfl,rfl⟩,e.2⟩⟩

theorem port_fst (s : Bool) (e : E) : (port A s e).1=Stage.home A (endSite A s e) := by cases s <;> rfl
theorem from_port (s : Bool) (e : E) : Stage.recover A (port A s e).1 (port A s e).2=e := by cases s <;> rfl

def address (p : Σh : H,CellPort A h) : H×Fin cap := (p.1,signed p.1.1 p.1.2 p.2)

theorem address_inj : Function.Injective (address A native S ready) := by
  rintro ⟨a,p⟩ ⟨b,q⟩ eqn
  obtain rfl : a=b:=congrArg Prod.fst eqn
  exact congrArg (Sigma.mk a) ((signed a.1 a.2).injective (congrArg Prod.snd eqn))

def oldBlock (h : H) : Block m := digits.symm (h.1.1,h.2)

def subcell (h : H) : Fin (2^(m-c)) :=
  ⟨(remix (oldBlock digits h)).val%2^(m-c),Nat.mod_lt _ (Nat.two_pow_pos _)⟩

def donor (v : V) (hi : Block c) (lo : Fin (2^(m-c))) : H :=
  let coordinates:=digits ((remix).symm (join fits hi lo))
  ((coordinates.1,v),coordinates.2)

omit [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] in
theorem donor_locates (h : H) (v : V) (hi : Block c)
    (atV : h.1.2=v) (atHigh : group c (remix (oldBlock digits h))=hi.val) :
    donor digits basis fits v hi (subcell digits basis (c:=c) h)=h := by
  let y:=remix (oldBlock digits h)
  have whole : join fits hi (subcell digits basis h)=y := by
    apply Fin.ext
    change hi.val*2^(m-c)+y.val%2^(m-c)=y.val
    change y.val/2^(m-c)=hi.val at atHigh
    rw [←atHigh,Nat.mul_comm, Nat.add_comm]
    exact Nat.mod_add_div ..
  rcases h with ⟨⟨j,v'⟩,x⟩
  obtain rfl : v'=v:=atV
  simp only [donor,whole,y,Equiv.symm_apply_apply,oldBlock,Equiv.apply_symm_apply]

/-- A donor row is read by its fixed signed slot. This inverse ranges only
over the one bounded previous cell. -/
def atSlot (s : Bool) (h : H) (slot : Fin cap) : Option E :=
  if hit : ∃p : CellPort A h,signed h.1 h.2 p=slot then
    let p:=hit.choose
    let e:=Stage.recover A h p
    if address A native S ready (port A s e)=(h,slot) then some e else none
  else none

theorem atSlot_iff (s : Bool) (h : H) (slot : Fin cap) (e : E) :
    atSlot A native S ready s h slot=some e ↔ address A native S ready (port A s e)=(h,slot) := by
  constructor
  · intro present
    by_cases hit : ∃p : CellPort A h,signed h.1 h.2 p=slot
    · let found := Stage.recover A h hit.choose
      have selected : (if address A native S ready (port A s found)=(h,slot)
          then some found else none)=some e := by
        simpa only [atSlot,dite_eq_left hit] using present
      by_cases located : address A native S ready (port A s found)=(h,slot)
      · have same : found=e := Option.some.inj (by simpa only [ite_eq_left located] using selected)
        rw [←same]
        exact located
      · simp [located] at selected
    · simp [atSlot,hit] at present
  · intro eqn
    obtain ⟨h',p,portEq⟩ : ∃h' : H, ∃p : CellPort A h',port A s e=⟨h',p⟩ :=
      ⟨(port A s e).1,(port A s e).2,rfl⟩
    rw [portEq] at eqn
    have hostEq : h'=h := congrArg Prod.fst eqn
    subst h'
    have slotEq : signed h.1 h.2 p=slot := congrArg Prod.snd eqn
    have hit : ∃p : CellPort A h,signed h.1 h.2 p=slot := ⟨p,slotEq⟩
    have chosen : hit.choose=p := (signed h.1 h.2).injective (hit.choose_spec.trans slotEq.symm)
    have back:=from_port A s e
    rw [portEq] at back
    rw [atSlot,dite_eq_left hit]
    change (if address A native S ready (port A s (Stage.recover A h hit.choose))=(h,slot)
      then some (Stage.recover A h hit.choose) else none)=some e
    rw [chosen,back,portEq,ite_eq_left eqn]

def panel (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m ≃ J × Block k) (basis : Layout m) (fits : c ≤ m)
    (s : Bool) (v : V) (hi : Block c) (eligible : Stage.Grain A → Prop)
    (j : Fin (2^(m-c)) × Fin (2*A.cap)) : Option (Stage.Grain A) :=
  Option.filter (fun e => decide (eligible e))
    (atSlot A native S ready s (donor digits basis fits v hi j.1) j.2)

def localAddress (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m ≃ J × Block k) (basis : Layout m) (s : Bool) (e : Stage.Grain A) :
    Fin (2^(m-c)) × Fin (2*A.cap) :=
  let p:=address A native S ready (port A s e)
  (subcell digits basis (c:=c) p.1,p.2)

theorem panel_at (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m ≃ J × Block k) (basis : Layout m) (fits : c ≤ m)
    (s : Bool) (v : V) (hi : Block c) (eligible : Stage.Grain A → Prop)
    (eligibleAt : ∀ e, eligible e →
      (A.pos (endSite A s e)).2 = v ∧
        group c (rearrange basis (oldBlock digits (Stage.home A (endSite A s e)))) = hi.val)
    (e : Stage.Grain A) (he : eligible e) :
    panel A native S ready digits basis fits s v hi eligible
      (localAddress (c:=c) A native S ready digits basis s e) = some e := by
  obtain ⟨a,b⟩:=eligibleAt e he
  have atV : (port A s e).1.1.2=v := by rw [port_fst];exact a
  have atHigh : group c (rearrange basis (oldBlock digits (port A s e).1))=hi.val := by
    rw [port_fst]
    exact b
  let p := port A s e
  let idx := (address A native S ready p).2
  have hit : atSlot A native S ready s p.1 idx=some e :=
    (atSlot_iff A native S ready s p.1 idx e).mpr rfl
  change ((atSlot A native S ready s (donor digits basis fits v hi (subcell digits basis p.1)) idx).filter
    (fun t=>decide (eligible t)))=some e
  rw [donor_locates digits basis fits p.1 v hi atV atHigh,hit]
  simp [Option.filter,he]

theorem panel_sound (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m ≃ J × Block k) (basis : Layout m) (fits : c ≤ m)
    (s : Bool) (v : V) (hi : Block c) (eligible : Stage.Grain A → Prop)
    {j : Fin (2^(m-c)) × Fin (2*A.cap)} {e : Stage.Grain A}
    (hit : panel A native S ready digits basis fits s v hi eligible j=some e) :
    eligible e ∧ j=localAddress (c:=c) A native S ready digits basis s e := by
  unfold panel at hit
  cases eqn : atSlot A native S ready s (donor digits basis fits v hi j.1) j.2 with
  | none=>simp [eqn] at hit
  | some t=>
    by_cases live : eligible t
    · have same : t=e := by simpa [eqn,Option.filter,live] using hit
      subst e
      have code:=(atSlot_iff A native S ready s (donor digits basis fits v hi j.1) j.2 t).mp eqn
      refine ⟨live,Prod.ext ?_ (congrArg Prod.snd code).symm⟩
      change j.1=subcell (c:=c) digits basis (address A native S ready (port A s t)).1
      rw [congrArg Prod.fst code]
      have back : oldBlock digits (donor digits basis fits v hi j.1) =
          (rearrange basis).symm (join fits hi j.1) := by
        exact digits.symm_apply_apply _
      change j.1 = DescentPlainTerminal.low (c:=c)
        (rearrange basis (oldBlock digits (donor digits basis fits v hi j.1)))
      rw [back, Equiv.apply_symm_apply, DescentPlainTerminal.low_join]
    · simp [eqn,Option.filter,live] at hit

theorem count (A : GroupStage W G price ε J V k) (native : W.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (digits : Block m ≃ J × Block k) (basis : Layout m) (fits : c ≤ m)
    (s : Bool) (v : V) (hi : Block c) (eligible : Stage.Grain A → Prop)
    (eligibleAt : ∀ e, eligible e →
      (A.pos (endSite A s e)).2 = v ∧
        group c (rearrange basis (oldBlock digits (Stage.home A (endSite A s e)))) = hi.val)
    (test : Stage.Grain A → Bool) :
    (Finset.univ.filter (fun j=>(panel A native S ready digits basis fits s v hi eligible j).any test)).card =
      (Finset.univ.filter (fun e=>eligible e ∧ test e)).card := by
  symm
  apply Finset.card_bij (fun e _=>localAddress (c:=c) A native S ready digits basis s e)
  · intro e he
    obtain ⟨live,tested⟩:=(Finset.mem_filter.mp he).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      rw [panel_at A native S ready digits basis fits s v hi eligible eligibleAt e live]
      exact tested⟩
  · intro e he f hf same
    have a:=panel_at A native S ready digits basis fits s v hi eligible eligibleAt e (Finset.mem_filter.mp he).2.1
    have b:=panel_at A native S ready digits basis fits s v hi eligible eligibleAt f (Finset.mem_filter.mp hf).2.1
    rw [same,b] at a
    exact (Option.some.inj a).symm
  · intro j hj
    have yes:=(Finset.mem_filter.mp hj).2
    cases hit : panel A native S ready digits basis fits s v hi eligible j with
    | none=>simp [hit] at yes
    | some e=>
      obtain ⟨he,hd⟩:=panel_sound A native S ready digits basis fits s v hi eligible hit
      exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he,by simpa [hit] using yes⟩,hd.symm⟩

end
end Hierarchy.DescentIssuedFallbackPanel

end OAI
