import OAI.Hierarchy.DescentScheduledLaneReset
import OAI.Hierarchy.DescentOrderedReentry
import OAI.Hierarchy.DescentPiecesSiteUnits

namespace OAI
/-! # Reentering a group with the scalar occurrences issued by the reset -/

set_option quotPrecheck false

namespace Hierarchy.DescentResetTrunks
open Computability.BorderVNP.Crossing DescentRouterBank DescentNamedContact
open scoped Classical
noncomputable section
variable {d : ℕ} {P H R : Type} {bits : P→ℕ} (N : Network d P bits) (home : N.Site→H)

/-- The old primary tensors, each incoming relay equality and each configured bank node. -/
def ActorNodes (old : N.Site→Type) (bank : R→Type) : (Bool×H)⊕R→Type
  | .inl (false,t) => Σu : Fibre home t,old u.val
  | .inl (true,t) => Fibre (moved N home) t
  | .inr r => bank r

instance actorsFinite (old : N.Site→Type) (bank : R→Type)
    [∀v,Fintype (old v)] [∀r,Fintype (bank r)] (x : (Bool×H)⊕R) :
    Fintype (ActorNodes N home old bank x) := by
  rcases x with ⟨_|_,t⟩|r <;> unfold ActorNodes <;> infer_instance


end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentHostDirectory DescentColonies DescentResetTrunks
open DescentNamedContact DescentMixedRouter DescentNetworkSubstitution StarKeys DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {F P H Y : Type} [Field F] {d h C Ht : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable (old : A.graph.Site→List H) (prog : SiteBits (U:=Y) Z.bank)
local notation "W" => (Z.reenter T)
local notation "names" => ((Bool×Z.Fallback) ⊕ Z.bank.Site)
local notation "paid" => (ActorNodes A.graph T.home (fun v=>Fin (old v).length) (fun r=>(prog r).Node))

abbrev RecipeToken := H ⊕ (A.graph.Edge ⊕ Σr : Z.bank.Site,(prog r).Node)

def recipeToken : (x : names) → paid x → RecipeToken (H:=H) Z prog
  | .inl (false,_), ⟨u,i⟩ => .inl ((old u.val).get i)
  | .inl (true,_), e => .inr (.inl e.val)
  | .inr r, n => .inr (.inr ⟨r,n⟩)

/-- Every list position identifies a real source occurrence, even when two
old occurrences have the same tag. Bank nodes carry their own physical site. -/
def recipeRecords (v : (W).graph.Site) : List (RecipeToken (H:=H) Z prog) :=
  let x:=resetNames Z T v
  List.ofFn fun i : Fin (Fintype.card (paid x))=>recipeToken Z T old prog x ((Fintype.equivFin _).symm i)

theorem recipeRecords_length (v : (W).graph.Site) :
    (recipeRecords Z T old prog v).length=Fintype.card (paid (resetNames Z T v)) := by simp [recipeRecords]

theorem recipeRecords_count :
    (∑v,(recipeRecords Z T old prog v).length)=
       (∑u,(old u).length)+Fintype.card A.graph.Edge+∑r,Fintype.card (prog r).Node := by
  simp only [recipeRecords_length]
  rw [(resetNames Z T).sum_comp (fun x=>Fintype.card (paid x)),Fintype.sum_sum_type,
    Fintype.sum_prod_type,Fintype.sum_bool]
  change (∑t,Fintype.card (Fibre (moved A.graph T.home) t))+
    (∑t,Fintype.card (Σu : Fibre T.home t,Fin (old u.val).length))+(∑r,Fintype.card (prog r).Node)=_
  simp_rw [Fintype.card_sigma,Fintype.card_fin]
  have sumOld : (∑t,∑u : Fibre T.home t,(old u.val).length)=∑u,(old u).length := by
    rw [←Fintype.sum_sigma' (fun t (u : Fibre T.home t)=>(old u.val).length)]
    exact (Equiv.sigmaFiberEquiv T.home).sum_comp (fun u=>(old u).length)
  rw [sumOld,←Fintype.card_sigma,Fintype.card_congr (Equiv.sigmaFiberEquiv (moved A.graph T.home)),
    Nat.add_comm (Fintype.card A.graph.Edge)]

variable (wire hist f g B : ℕ) (bill : ActorBudget Z T old wire hist f g B)
local notation "M" => (2^g*B : ℕ)
local notation "base" => (2^f*B : ℕ)
local notation "tag" => (reentryTag Z T)
local notation "cost" => ((W).siteUnits tag (recipeRecords Z T old prog) wire 256 hist)
local notation "dst" => (T.home ∘ A.graph.dst)
local notation "whole" => (bin T.home (A.siteUnits Z.hub old wire 256 hist))
local notation "eqw" => (funext (fun e=>(Z.allWidths e).symm))

open private tag_at_name from OAI.Hierarchy.DescentReentryCommonBlocks in
include bill in
theorem recipe_site_units {p : ℕ} (unit : p≤Z.unit) (token : 4*hist≤wire*p)
    (bank : ∀r,Fintype.card (prog r).Node*p≤2*portLoad Z.bank r)
    (rotor : 6*(2+rotorRate h C)*(base:ℝ)≤M) (rows : 18*(base:ℝ)≤M)
    (v : (W).graph.Site) : cost v≤M ∧ (tag v=true→cost v=M) := by
  obtain ⟨x,rfl⟩:=(resetNames Z T).symm.surjective v
  have read:=read_actors A T.home Z.placement.input T.hub eqw Z.bank Z.tables
    (recipeRecords Z T old prog) wire 256 hist x
  have amount:=recipeRecords_length Z T old prog ((resetNames Z T).symm x)
  rw [Equiv.apply_symm_apply] at amount
  have named := tag_at_name Z T x
  have installedAmount : (recipeRecords Z T old prog
      ((installedNames A T.home Z.placement.input T.hub eqw Z.bank Z.tables).symm x)).length =
      Fintype.card (paid x) := amount
  rw [installedAmount] at read
  rw [named, show cost ((resetNames Z T).symm x) = _ from read]
  have three (t : Z.Fallback) (ht : T.hub t=false) : (whole t:ℝ)≤3*(base:ℝ) := by
    have y : (1:ℝ)≤(2^Z.n:ℕ) := by exact_mod_cast Nat.succ_le_of_lt (Nat.two_pow_pos _)
    exact (bill.ordinary t ht).trans (div_le_self (by positivity) y)
  rcases x with ⟨_|_,t⟩|r
  · let primary := (bin (T.home ∘ A.graph.src) A.graph.width t +
        bin (T.home ∘ A.graph.dst) A.graph.width t) * wire * (if T.hub t then 256 else 1) +
        hist * Fintype.card (Σ u : Fibre T.home t, Fin (old u.val).length)
    change primary ≤ M ∧ (T.hub t = true → primary = M)
    have exactLoad:=whole_fiber A T.home T.hub wire 256 hist old t
    rw [show T.hub ∘ T.home=Z.hub from funext T.tag] at exactLoad
    have size : Fintype.card (Σu : Fibre T.home t,Fin (old u.val).length)=
        bin T.home (fun u=>(old u).length) t := by
      simp only [Fintype.card_sigma,Fintype.card_fin]
      exact width_bin T.home (fun u : A.graph.Site => (old u).length) t
    have primaryEq : primary = whole t := by
      dsimp only [primary]
      rw [size]
      exact exactLoad.symm
    rw [primaryEq]
    cases ht : T.hub t
    · refine ⟨?_,by simp⟩
      have h:=three t ht
      exact_mod_cast (show (whole t:ℝ)≤M by linarith only [h,rows,show (0:ℝ)≤base from by positivity])
    · exact ⟨(bill.hub t ht).le,fun _=>bill.hub t ht⟩
  · refine ⟨?_,by simp⟩
    let n:=Fintype.card (Fibre dst t)
    let load:=bin dst A.graph.width t
    have width : n*Z.unit=load := by
      dsimp [n,load]
      rw [←width_bin]
      simp [DescentNamedContact.width,Z.allWidths]
    have ncost : hist*n≤wire*load := by
      calc
        hist*n ≤ (wire*p)*n := Nat.mul_le_mul_right _ (by omega)
        _ = wire*(n*p) := by ring
        _ ≤ wire*(n*Z.unit) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ unit)
        _ = _ := by rw [width]
    have marg:=end_cap Z T old wire hist true t
    change load*wire*(if T.hub t then 256 else 1)≤whole t at marg
    change 2*wire*load+hist*n≤M
    cases ht : T.hub t
    · simp only [ht,Bool.false_eq_true,ite_false,mul_one] at marg
      have small : whole t≤3*base := by exact_mod_cast three t ht
      have high : 18*base≤M := by exact_mod_cast rows
      rw [Nat.mul_comm load wire] at marg
      rw [Nat.mul_assoc];omega
    · simp only [ht,ite_true,bill.hub t ht] at marg
      rw [Nat.mul_comm load wire] at marg
      rw [Nat.mul_assoc];omega
  · refine ⟨?_,by simp⟩
    let load:=wire*portLoad Z.bank r
    have bound : 2*load≤M := by
      have rotorScale := rotor
      have rowScale := rows
      push_cast at rotorScale rowScale
      have nonneg : 0 ≤ (2 : ℝ)^g * B := by positivity
      have k := port_price Z T old wire hist f g B bill r (limit := (2 : ℝ)^g * B / 2)
        (by linarith only [rotorScale]) (by linarith only [rowScale]) (by linarith only [nonneg])
      have priceBound : 2 * ((wire : ℝ) * portLoad Z.bank r) ≤ (M : ℝ) := by
        push_cast
        linarith only [k]
      exact_mod_cast priceBound
    have charge : 4*(hist*Fintype.card (prog r).Node)≤2*load := calc
      _ = (4*hist)*Fintype.card (prog r).Node := by ring
      _ ≤ (wire*p)*Fintype.card (prog r).Node := Nat.mul_le_mul_right _ token
      _ = wire*(Fintype.card (prog r).Node*p) := by ring
      _ ≤ wire*(2*portLoad Z.bank r) := Nat.mul_le_mul_left _ (bank r)
      _ = 2*load := by dsimp [load];ring
    change load+hist*Fintype.card (prog r).Node≤M
    omega

open DescentCableUnbundling
variable {J : Type} [Fintype J] [DecidableEq J] {k L : ℕ}
variable (key : A.graph.Edge↪Fin L) (digits : Block T.commonDepth≃J×Block k)
local notation "U" => (ordinaryWorld Z T)
local notation "stagePos" => (groupPosition Z T digits)
local notation "ix" => (groupBlock Z T digits)
local notation "flag" => (fun u=>commonTag Z T (placed Z T u))
local notation "rec" => (recipeRecords Z T old prog)
local notation "count" => (fun e=>(W).graph.width e/Z.unit)
local notation "orig" => (original (W).graph (W).core count)

open private tag_at_name from OAI.Hierarchy.DescentReentryCommonBlocks in
theorem recipe_empty (empty : ∀u,Z.hub u=true→ old u=[]) (v : (W).graph.Site) (inHub : tag v=true) :
    rec v=[] := by
  obtain ⟨x,rfl⟩:=(resetNames Z T).symm.surjective v
  rw [tag_at_name] at inHub
  rcases x with ⟨_|_,t⟩|r
  · apply List.length_eq_zero_iff.mp
    rw [recipeRecords_length,Equiv.apply_symm_apply]
    change Fintype.card (Σu : Fibre T.home t,Fin (old u.val).length)=0
    rw [Fintype.card_sigma]
    apply Finset.sum_eq_zero
    intro u _
    have tagged : Z.hub u.val=true := by rw [←T.tag,u.property];exact inHub
    simp [empty u.val tagged]
  · cases inHub
  · cases inHub

include bill in
/-- The installed ordinary group uses a separate token for each actual relay
and elected scalar instruction, and preserves the old paid occurrences. -/
def recipe_group_stage (G : PoweredGadget F) (q budget : ℝ) (z nextCap : ℕ)
    (hk : 0<k) (hq : 0<q) (hw : 0<wire) (hz : 0<z) (hc : 0<nextCap)
    (unit : Z.unit=z*G.b) (scale : wire*(z*G.b)*nextCap=M)
    {p : ℕ} (width : p≤Z.unit) (quantum : 4*hist≤wire*p)
    (bank : ∀r,Fintype.card (prog r).Node*p≤2*portLoad Z.bank r)
    (rotor : 6*(2+rotorRate h C)*(base:ℝ)≤M) (rows : 18*(base:ℝ)≤M)
    (empty : ∀u,Z.hub u=true→ old u=[])
    (retained : (q*hist)*(((∑u,(old u).length)+Fintype.card A.graph.Edge+
        ∑r,Fintype.card (prog r).Node : ℕ):ℝ)≤budget)
    {r : ℕ} (range : Z.k-T.commonDepth≤r)
    (roots : ((Fintype.card J*(Fintype.card Z.V*(2^(resetHostGain h (2^Z.n) Ht)*2^r)):ℕ):ℝ)*
      ((2:ℝ)^DescentHostDegree.packExponent 20 3*(q*(M:ℝ)))≤budget) :
    GroupStage (Z.orderedOrdinary T key) G q budget J ↥(commonNames Z T) k := by
  refine Z.orderedStage T key ?_
  have bounds:=recipe_site_units Z T old prog wire hist f g B bill width quantum bank rotor rows
  have tags : flag = tag := funext (placed_tag Z T)
  have table : (U).siteUnits flag rec wire 256 hist = cost :=
    (congrArg (fun tags : (W).graph.Site → Bool => (U).siteUnits tags rec wire 256 hist) tags).trans
      (funext ((W).pieces_siteUnits Z.unit count (counts_fit Z T) tag rec wire 256 hist))
  have mass (v : J × ↥(commonNames Z T)) (i : Block k) :=
    (congrArg (fun load : (W).graph.Site → ℕ => blockMass (W).graph stagePos ix load v i) table).trans
      (group_mass Z T digits cost v i)
  refine {
    Atoms := RecipeToken (H:=H) Z prog
    wire := wire
    hist := hist
    z := z
    cap := nextCap
    degree := 3
    pos := stagePos
    block := ix
    near := emittedNear Z T
    hub := commonTag Z T
    records := rec
    fieldBits := hk
    degreeMin := by decide
    degreeBound := emitted_degree Z T
    symmetric := emitted_symmetric Z T
    pricePos := hq
    wirePos := hw
    unitPos := hz
    capPos := hc
    small := ?_
    saturated := ?_
    noHubAtoms := ?_
    peers := ?_
    same := ?_
    incidence := ?_
    widths := ?_
    retained := ?_
    roots := ?_ }
  · intro v i
    rw [scale]
    exact (mass v i).le.trans (mass_cap Z T cost (fun u => (bounds u).1) _ _)
  · intro v atHub i
    rw [scale]
    exact (mass v i).trans (hub_mass Z T cost (fun u => (bounds u).2) _ atHub _)
  · exact fun u hu=>recipe_empty Z T old prog empty u ((placed_tag Z T u).symm.trans hu)
  · exact fun e=>group_peers Z T digits (orig e)
  · exact fun e=>group_same Z T digits (orig e)
  · exact Eq.mpr (congrArg (fun tags : (W).graph.Site → Bool => MarkedWorld.HubIncidence U tags) tags)
      ((W).pieces_hubs Z.unit count (counts_fit Z T) tag
        ⟨fun e => (reentry_tags Z T e).1, fun e => (reentry_tags Z T e).2⟩)
  · exact fun e he => (uniform (W).graph (W).core count Z.unit e he).trans unit
  · have total : (∑u : (W).graph.Site,((rec u).length:ℝ))=
        (((∑u,(old u).length)+Fintype.card A.graph.Edge+∑r,Fintype.card (prog r).Node:ℕ):ℝ) := by
      exact_mod_cast recipeRecords_count Z T old prog
    exact (congrArg (fun x=>(q*hist)*x) total).le.trans retained
  · rw [scale]
    have numeric := Nat.mul_le_mul_left (Fintype.card J) (placed_growth Z T range)
    have cardR : ((Fintype.card J*Fintype.card ↥(commonNames Z T):ℕ):ℝ)≤_ := (Nat.cast_le (α:=ℝ)).mpr numeric
    exact (mul_le_mul_of_nonneg_right cardR (by positivity)).trans roots


end
end Hierarchy.DescentSixParty.ResetInput

namespace Hierarchy.DescentResetTrunks
open Computability.BorderVNP.Crossing DescentRouterBank DescentNamedContact DescentSixParty DescentKernelHistory
open scoped Classical
noncomputable section
variable {d n : ℕ} {P H Q R : Type} {bits : P→ℕ} (N : Network d P bits) (home : N.Site→H)

def GatheredExterior (ghost : N.Site→Type) : (Bool×H)⊕R→Type
  | .inl (false,t) => Σu : Fibre home t,ghost u.val
  | _ => Empty

/-- Propagate the old injection into actual recipe occurrences. All relay
equalities and all bank nodes are charged at their own physical site. -/
def splitActors {before charged ghost : N.Site→Type} (bank : R→Type)
    (selected : ∀u,before u≃charged u ⊕ ghost u) (x : (Bool×H)⊕R) :
    ActorNodes N home before bank x ≃
      ActorNodes N home charged bank x ⊕ GatheredExterior (R:=R) N home ghost x := by
  rcases x with ⟨_|_,t⟩|r
  · exact (Equiv.sigmaCongrRight (fun u : Fibre home t=>selected u.val)).trans
      (Equiv.sigmaSumDistrib (fun u : Fibre home t=>charged u.val) (fun u : Fibre home t=>ghost u.val))
  · exact (Equiv.sumEmpty _ Empty).symm
  · exact (Equiv.sumEmpty _ Empty).symm

variable [Fintype H] [Fintype Q] {F Y : Type} [Field F] {A : MarkedWorld F d P bits}
variable (B : BitDescription A) (house : A.graph.Site→H) (group : Bool→A.graph.Edge→Q) (hub : H→Bool)

/-- Old nodes keep their original indices through the checked width cast and
gather. Each new relay and router index is the literal index of its recipe. -/
def installedActors {L : ℕ} {width : A.graph.Edge→ℕ} (same : width=A.graph.width)
    (board : Network n (Bool×Q) (publicWidth group width)) (legacy sorted : board.Tables F)
    (key : A.graph.Edge↪Fin L) (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) board)
    (valid : ReadsBits board scalar prog sorted) (v : (install A house group hub same board legacy).graph.Site) :
    (((B.installed house group hub same board legacy sorted key scalar prog valid).recipe v).Node) ≃
      ActorNodes A.graph house (fun u=>(B.recipe u).Node) (fun r=>(prog r).Node)
        (installedNames A house group hub same board legacy v) := by
  subst width
  rcases v with ⟨_|_,t⟩|r
  · apply Equiv.sigmaCongrRight
    rintro ⟨u,rfl⟩
    exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _

/-- Exterior occurrences are in bijection with the original public ports
attached to the primary terminal. Relays and bank actors have none. -/
def installedGhosts {width : A.graph.Edge→ℕ} (same : width=A.graph.width)
    (board : Network n (Bool×Q) (publicWidth group width)) (legacy : board.Tables F)
    (v : (install A house group hub same board legacy).graph.Site) :
    GatheredExterior (R:=board.Site) A.graph house (Attached A.graph)
      (installedNames A house group hub same board legacy v) ≃
      Attached (install A house group hub same board legacy).graph v := by
  subst width
  let fromEmpty (X : Type) (absurdX : X → False) : Empty ≃ X :=
    { toFun := Empty.elim
      invFun := fun x => (absurdX x).elim
      left_inv := by intro x; cases x
      right_inv := fun x => (absurdX x).elim }
  rcases v with ⟨_|_, t⟩ | r
  · refine ⟨fun a => ⟨a.2.val, ?_⟩,
      fun a => ⟨⟨A.graph.attach a.val, ?_⟩, ⟨a.val, rfl⟩⟩, ?_, ?_⟩
    · change Sum.inl (false, house (A.graph.attach a.2.val)) = Sum.inl (false, t)
      rw [a.2.property, a.1.property]
    · exact congrArg Prod.snd (Sum.inl.inj a.property)
    · rintro ⟨⟨u, hu⟩, ⟨p, hp⟩⟩
      change A.graph.attach p = u at hp
      subst u
      rfl
    · intro a
      rfl
  · refine fromEmpty _ ?_
    intro a
    exact Bool.false_ne_true (congrArg Prod.fst (Sum.inl.inj a.property))
  · refine fromEmpty _ ?_
    rintro ⟨p, hp⟩
    change (Sum.inl (false, house (A.graph.attach p)) : (Bool × H) ⊕ board.Site) =
      Sum.inr r at hp
    cases hp



end
end Hierarchy.DescentResetTrunks

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetTrunks DescentRouterBank
open scoped Classical
noncomputable section
variable {F P H Y : Type} [Field F] {d h C Ht L : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z) (old : A.graph.Site→List H)
    (before : BitDescription A) (key : A.graph.Edge↪Fin L)
    (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) Z.bank)
    (valid : ReadsBits Z.bank scalar prog (Z.orderedBank key))
local notation "same" => (funext (fun e=>(Z.allWidths e).symm))

/-- The actual local ordered recipe consists of precisely the charged list
positions and inherited attached public ports, with every new operation charged. -/
def recipe_partition (source : ∀u,(before.recipe u).Node≃Fin (old u).length ⊕ Attached A.graph u)
    (v : (Z.orderedReentry T key).graph.Site) :
    ((before.fromBank Z T key scalar prog valid).recipe v).Node≃
      Fin (recipeRecords Z T old prog v).length ⊕ Attached (Z.orderedReentry T key).graph v := by
  let stock:=installedActors before T.home Z.placement.input T.hub same Z.bank Z.tables
    (Z.orderedBank key) key scalar prog valid v
  let split:=splitActors A.graph T.home (fun r=>(prog r).Node) source (resetNames Z T v)
  let pins:=installedGhosts (A:=A) T.home Z.placement.input T.hub same Z.bank Z.tables v
  exact (stock.trans split).trans (Equiv.sumCongr
    ((Fintype.equivFin _).trans (finCongr (recipeRecords_length Z T old prog v).symm)) pins)

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
