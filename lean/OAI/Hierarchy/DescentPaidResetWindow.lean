import OAI.Hierarchy.DescentPaidResidentCount
import OAI.Hierarchy.DescentFallbackMeasuredPresence

namespace OAI
/-! # The measured short reset stencil selects funded particles within one coarse group -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentSixParty.ResetInput DescentContacts DescentColonies DescentGL
open DescentPlainTerminal DescentPlainTerminal.Suffix DescentIssuedFallbackPanel DescentChosenRouter
open DescentRelativeContacts DescentResetHostSize DescentFallbackShapeTable
open DescentHostDirectory DescentPackedActorMask DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
    {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
    (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ) (wt : V→Block k→ℕ)
    (flow : V→V→Block k→ℝ) (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "c" => T.commonDepth
local notation "Y" => (2^Z.n:ℕ)
local notation "r" => Z.k-c
local notation "fit" => frame.enough.trans (Nat.sub_le ..)
set_option quotPrecheck false in
local notation "safe" => roster.2.2.2.2.2.choose
local notation "ep" => endpoint near (fun v=>Z.placement.b (frame.host v)) frame.basis wt f
  (32*Nat.clog 2 (2*Δ)) B g Y safe (fun v j=>(frame.host v,j)∈Z.placement.keys) hub
local notation "μ" => rearrange frame.basis
variable (t : Z.Fallback)
set_option quotPrecheck false in
local notation "v₀" => frame.host.symm (T.code t).1
set_option quotPrecheck false in
local notation "hi" => Z.rootBlock T (.inr t)
set_option quotPrecheck false in
local notation:max "name" t:arg => (shortName c (T.code t)).2
local notation:max "code" t:arg => cell r (name t)
set_option quotPrecheck false in
local notation:max "raw" j:arg => (μ).symm (join fit hi j)
variable (word : Block (k-T.commonDepth)→ℕ)


private theorem code_inj (a b : Z.Fallback) (host : (T.code a).1=(T.code b).1)
    (group : Z.rootBlock T (.inr a)=Z.rootBlock T (.inr b)) (encoded : code a=code b) : a=b := by
  have depth (u : Z.Fallback) : (name u).1.1≤r := Nat.sub_le_sub_right (T.codeLegal u).2.1 c
  have id (u : Z.Fallback) : (name u).1.2 < 2^(name u).1.1 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have data:=congrArg (decode r Y) encoded
  rw [decode_cell r _ (depth a) (id a),decode_cell r _ (depth b) (id b)] at data
  have tags : (name a).2 = (name b).2 := congrArg Prod.snd data
  have same : Z.rootTicket T (.inr a)=Z.rootTicket T (.inr b):=congrArg Sum.inr
    (Prod.ext (Subtype.ext (congrArg Prod.fst data)) tags)
  exact Sum.inr.inj ((Z.rootLocation T (Fintype.equivFin _).toEmbedding).injective
    (Prod.ext (congrArg (Fintype.equivFin _) host) (Prod.ext group same)))

include roster in
/-- This is a per-slot theorem, retaining all old paid sites even if they
have no incident cable. The true high/group address fixes the missing part of
the short stencil identifier. -/
theorem «matches» (stencil : ∀lo,word lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v₀ (raw lo))))
    (u : A.graph.Site) (lo : Block (k-c)) (host : pos u=v₀) (coord : ix u=raw lo) :
    word lo/2=code t ↔ T.home u=t := by
  have label := roster.2.2.2.2.2.choose_spec.1 u
  rw [host,coord] at label
  have data : word lo/2=code (T.home u) := by
    rw [stencil,←label,←fields_relative,←frame.extent,Stencil.shapeCode_fields]
  rw [data]
  constructor
  · intro same
    apply code_inj (T:=T) (T.home u) t _ _ same
    · rw [frame.homeHost,host,Equiv.apply_symm_apply]
    · apply Fin.ext
      have coarse:=frame.homeHigh u
      rw [coord,Equiv.apply_symm_apply] at coarse
      exact coarse.trans (congrArg Fin.val (high_join fit hi lo))
  · intro same;rw [same]

include roster in
/-- Only `2^(k-commonDepth)` donor cells are read in the receiver's coarse
group. An old atom uses its funded multiplicity. Each individual incoming
grain for the relay instantiates the same sum with unit multiplicity. -/
theorem window_sum (stencil : ∀lo,word lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v₀ (raw lo))))
    {X : Type} [Fintype X] (whereAt : X→A.graph.Site) (amount : X→ℕ)
    (old : Block (k-c)→ℕ) (previous : ∀lo,old lo=∑u : X,
      if pos (whereAt u)=v₀ ∧ ix (whereAt u)=raw lo then amount u else 0) :
    (∑lo : Block (k-c),if word lo/2=code t then old lo else 0)=
      ∑u : {u : X // T.home (whereAt u)=t},amount u.val := by
  have regroup (lo : Block (k-c)) :
      (if word lo/2=code t then old lo else 0)=
        ∑u : X,if pos (whereAt u)=v₀ ∧ ix (whereAt u)=raw lo ∧ T.home (whereAt u)=t then amount u else 0 := by
    by_cases hit : word lo/2=code t
    · rw [ite_eq_left hit,previous]
      apply Finset.sum_congr rfl
      intro j _
      by_cases loc : pos (whereAt j)=v₀ ∧ ix (whereAt j)=raw lo
      · simp [loc.1,loc.2,(«matches» frame vertex near n f B wire K Δ wt flow roster t word stencil _
          lo loc.1 loc.2).mp hit]
      · simp [←and_assoc,loc]
    · rw [ite_eq_right hit]
      symm;apply Finset.sum_eq_zero
      intro j _
      apply ite_eq_right
      rintro ⟨hv,hx,actual⟩
      exact hit ((«matches» frame vertex near n f B wire K Δ wt flow roster t word stencil _ lo hv hx).mpr actual)
  simp_rw [regroup]
  rw [Finset.sum_comm]
  have collapse (u : X) :
      (∑lo : Block (k-c),if pos (whereAt u)=v₀ ∧ ix (whereAt u)=raw lo ∧ T.home (whereAt u)=t then amount u else 0)=
      if T.home (whereAt u)=t then amount u else 0 := by
    by_cases owns : T.home (whereAt u)=t
    · let x:=ix (whereAt u)
      let digit:=@DescentPlainTerminal.low k T.commonDepth (μ x)
      have host := frame.homeHost (whereAt u)
      rw [owns] at host
      have hv : pos (whereAt u)=v₀ := (Equiv.eq_symm_apply _).mpr host.symm
      have coarse:=frame.homeHigh (whereAt u)
      rw [owns] at coarse
      have here : high fit (μ x)=hi := Fin.ext coarse.symm
      have hx : ix (whereAt u)=raw digit:=by
        have joinEq : join fit hi digit=μ x := here ▸ join_high_low fit (μ x)
        rw [joinEq,Equiv.symm_apply_apply]
      rw [Finset.sum_eq_single digit]
      · simp [hv,hx,owns]
      · intro j _ ne
        have other : ix (whereAt u)≠raw j := by
          intro eqn
          have back : @DescentPlainTerminal.low k T.commonDepth (μ (ix (whereAt u)))=j := by simp [eqn,low_join]
          exact ne back.symm
        simp [other]
      · simp
    · simp [owns]
  simp_rw [collapse]
  let property (u : X) := T.home (whereAt u)=t
  let emb : {u : X //property u}↪X := Function.Embedding.subtype _
  exact sum_image emb (fun u=>amount u.val) property amount
    (fun j=>Iff.intro (fun h=>⟨⟨j,h⟩,rfl⟩) (by rintro ⟨u,rfl⟩;exact u.property)) (fun _=>rfl)

def tally (bits paid L root : ℕ) (stencil : Cell (bits*L)) (weights : Cell (paid*L)) : Cell paid :=
  ((∑j : Fin L,if (((encode bits L).symm stencil) j).val/2=root then
    (((encode paid L).symm weights) j).val else 0):ℕ)

theorem tally_zero (bits paid L root : ℕ) : tally bits paid L root 0 0=0 := by
  have cleared : (encode paid L).symm 0=fun _=>0 := by
    apply (encode paid L).injective
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    change 0=(finFunctionFinEquiv (fun _ : Fin L=>(0:Cell paid))).val
    simp []
  simp [tally,cleared]

/-- The bit extraction in the comparison is performed by the table on the
actual stencil word produced by `all_stencil_words` at every donor coordinate. -/
theorem funded_chip (stencil : ∀lo,word lo/2=Stencil.shapeCode (k-c) Y (fieldsRelative c (ep v₀ (raw lo))))
    {X : Type} [Fintype X] {a b : ℕ} (whereAt : X→A.graph.Site) (amount : X→ℕ)
    (address : Block (k-c)→Cell a) (old : Block (k-c)→Cell b)
    (issued : ∀lo,(address lo).val=word lo)
    (prior : ∀lo,(old lo).val=∑u : X,if pos (whereAt u)=v₀ ∧ ix (whereAt u)=raw lo then amount u else 0) :
    tally a b (2^(k-c)) (code t) (encode a _ address) (encode b _ old)=
      ((∑u : {u : X //T.home (whereAt u)=t},amount u.val):ℕ) := by
  have funds:=window_sum frame vertex near n f B wire K Δ wt flow roster t word stencil whereAt amount (fun j=>(old j).val) prior
  simpa only [tally,Equiv.symm_apply_apply,issued] using congrArg (fun q : ℕ=>(q : Cell b)) funds

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
