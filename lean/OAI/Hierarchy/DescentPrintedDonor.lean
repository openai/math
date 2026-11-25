import OAI.Hierarchy.DescentDonorSelection
import OAI.Hierarchy.DescentDonorWalkRead
import OAI.Hierarchy.DescentOrdinaryDonorRows

namespace OAI
/-! # A genuine packed previous donor reconstructs the five native venue observations -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentRawCablePanel DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false
set_option maxHeartbeats 1000000
noncomputable section
namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
local notation "names" => cableNames k rank
local notation "next" => rotor A rank
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "N" => W.graph
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 +
        (scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e) = scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "P" => coloredPack N W.core home color A.cap
local notation "pick" => colorPick N W.core home color A.cap
local notation "venue" => newSite N pick lay P
local notation "key" => nativeKey N W.core home color A.cap addr same lay
local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "peer" => fun h v x=>Option.elim (next h v) (0,0,0) (fun other=>here other x)

local notation "K" => fun (u : W.graph.Site)=>key (venue (Sum.inl u))
local notation "T" => nativeTraffic N W.core home
local notation "Idx" => NativePair N W.core home color A.cap
local notation "pos" => DescentSharedCableNames.Stage.Positive A
local notation "S₀" => DescentSharedCableNames.Stage.outgoing A native S ready
variable {H : ℕ} (host : V↪Fin H) (roster : Fin H→Fin A.degree→Option (Fin H))
    (physical : ∀z j t,rotor A rank z j=some t→ roster (host z.2) j=some (host t.2))
    (hub : V→Bool)
local notation "flag" => fun j=>if hv : ∃v,host v=j then hub hv.choose else false

theorem groups_preserved {z y : J×V} {j : Fin A.degree} (found : next z j=some y) : y.1=z.1 := by
  unfold rotor at found
  split at found
  next live =>
    have member:=live.choose.property
    have eqn:=Option.some.inj found
    rw [←eqn]
    obtain ⟨v,_,same⟩:=Finset.mem_map.mp member
    have h := congrArg Prod.fst same.symm
    exact h
  next =>contradiction

def firstWalk (q : pos) (t : Bool) : Walk :=
  let root:=A.pos ((N).src q.val)
  look (here root) (peer root) (if t then (sourceHandle A native S ready rank q).neighbor.val+1 else 0,
    (A.block ((N).src q.val)).val)

def nextHeads (q : pos) :=
  let root:=A.pos ((N).src q.val)
  let slot:Fin (2*A.cap):=(S₀ q).castLE (by omega)
  actorHeads A.cap profile (panel root) lay (here root) (peer root) (A.block ((N).src q.val)) slot

theorem representative_key (j : Idx) (t : Fin 3) :
    key (venue (.inr (j,representative t)))=K (StarKeys.endpoint N pick j t) := by
  apply congrArg key
  fin_cases t
  · exact (source_merge N pick lay P j 0).symm
  · exact (target_merge N pick lay P j 0).symm
  · exact (target_merge N pick lay P j 1).symm

include coord named fit winner df edgeOrder in
theorem actual_heads (q : pos) :
    let u:=(N).src q.val
    let born:=(nextHeads (short:=short) A native S ready rank win profile lay q).born
    (born.isSome=(DescentRawCablePanel.first pick q.val).isSome) ∧
    ∀out j,born=some out→DescentRawCablePanel.first pick q.val=some j→∀t,
      walked next (A.pos u) (out (representative t)) (K (StarKeys.endpoint N pick j t)) := by
  intro u born
  let slot:Fin (2*A.cap):=(S₀ q).castLE (by omega)
  have «rec»:=issued_heads A native S ready names win next he rank coord named fit winner (rotor_sorted A rank)
    (rotor_routes A native S ready rank) df edgeOrder profile same lay u slot
  have pos_:=source_host A he u
  have same_ (t) :=source_handle_identifies A native S ready rank he q true (home u) pos_ t
  constructor
  · have yes:=query_iff A native S ready rank win he coord named fit winner df edgeOrder profile q true
    have online : born.isSome=(query A.cap profile (panel (A.pos u)) (A.block u) (S₀ q).val true).isSome := by
      exact Option.isSome_map
    rw [online]
    apply Bool.eq_iff_iff.mpr
    apply Iff.trans yes
    change (∃j : Idx, pick (j,0)=q.val) ↔ (DescentRawCablePanel.first pick q.val).isSome=true
    unfold DescentRawCablePanel.first
    split
    next yes => exact iff_of_true yes rfl
    next no => exact iff_of_false no Bool.false_ne_true
  · intro out j shown first_ t
    have selected:=first_spec pick first_
    obtain ⟨x,observed,licensed⟩:=«rec».2 out shown
    have edgeEq:=(same_ (picked A he (home u) x true)).mp observed
    have edgeEq := (picked_old A he (home u) x true).symm.trans edgeEq
    have identical : (⟨home u,x⟩ : Idx)=j := congrArg Prod.fst ((pick).injective (edgeEq.trans selected.symm))
    subst j
    rw [←representative_key]
    exact licensed _

local notation "raw" => fun (q:pos) => DescentSharedCableNames.Stage.home A ((N).src q.val)
local notation "entry" => fun (q:pos) => host (A.pos ((N).src q.val)).2
local notation "seen" => fun (q:pos) => readWalk roster (entry q) flag
local notation "auth" => fun (q:pos) (u:(N).Site) => atKey roster (entry q) flag (fun (z : J×V)=>host z.2) (K u)

include coord named fit winner df edgeOrder physical in
/-- Every named occurrence, including an isolated destination or an unmarked
positive tether, uses the previous signed stream and the true second merge. -/
theorem donor_read (q : pos) (slots bytes age : ℕ) (chosen : Idx→Profile G.C) :
    let u:=(N).src q.val
    let starts:=nextHeads (short:=short) A native S ready rank win profile lay q
    let a:=seen q (firstWalk (short:=short) A native S ready rank win profile lay q false)
    let b:=seen q (firstWalk (short:=short) A native S ready rank win profile lay q true)
    let anchors:=starts.born.map (fun ws t=>seen q (ws (representative t)))
    let picked_:=markedChoice A.cap profile (panel (A.pos u)) (A.block u) (S₀ q).val
    let units:=DescentSharedCableNames.Stage.sourceGrains (fun j=>DescentSignedCableCodec.encode
      (DescentSharedCableNames.Stage.signedPanel A native S ready names (raw q) j)) (S₀ q)
    let c:=normBits A.cap G.b G.C G.k
    observedDonor slots bytes c a b anchors picked_ lay (Fin.ofNat (2^c) (units*G.b)) (Fin.ofNat (2^c) G.b)
      (fun t=>((DescentRawCablePanel.first pick q.val).map (fun j=>(⟨normalized A chosen (.inr (.inr (j,t))),
        normalized_fits A S ready chosen _⟩:Cell c))).getD 0)=
      measuredDonor (hCode:=age) A S ready pick lay P key (fun z=>hub z.2) slots chosen
        (relative pick lay P key) q := by
  intro u starts a b anchors picked_ units c
  have run_:=actual_heads A native S ready rank win he coord named fit winner df edgeOrder profile same lay q
  have pair (t : Bool) :=physical_walk A native S ready rank win he coord named fit winner df edgeOrder profile same lay q t
  have left_ : a=auth q u :=readWalk_atKey roster flag next _ physical _ (pair false)
  have right_ : b=auth q ((N).dst q.val) :=readWalk_atKey roster flag next _ physical _ (pair true)
  have present : starts.born.isSome=(DescentRawCablePanel.first pick q.val).isSome := run_.1
  have opts : anchors=(DescentRawCablePanel.first pick q.val).map (fun j t=>auth q (StarKeys.endpoint N pick j t)) := by
    cases startsEq:starts.born with
    | none=>
      cases orig:DescentRawCablePanel.first pick q.val with
      | none => simp only [anchors,startsEq,Option.map_none]
      | some j => simp only [startsEq,orig,Option.isSome_none,Option.isSome_some,Bool.false_eq_true] at present
    | some ws=>
      cases orig:DescentRawCablePanel.first pick q.val with
      | none=>simp only [startsEq,orig,Option.isSome_none,Option.isSome_some,Bool.true_eq_false] at present
      | some j=>
        simp only [anchors,startsEq,Option.map_some,Option.some.injEq]
        funext t
        exact readWalk_atKey roster flag next _ physical _ (run_.2 ws j startsEq orig t)
  have flagExact (v : V) : flag (host v)=hub v := by
    let usable : ∃x,host x=host v:=⟨v,rfl⟩
    change (if h : ∃ x, host x = host v then hub h.choose else false) = hub v
    rw [dite_eq_left usable,host.injective usable.choose_spec]
  have reached (t : (N).Site) (mem : t∈terms pick q.val) : ∃w,walked next (A.pos u) w (K t) := by
    simp only [terms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with (rfl|rfl)|other
    · exact ⟨_,pair false⟩
    · exact ⟨_,pair true⟩
    · cases orig:DescentRawCablePanel.first pick q.val with
      | none=>simp [orig] at other
      | some j=>
        have listed : t ∈ List.ofFn (StarKeys.endpoint N pick j) := by
          simpa only [orig,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil] using other
        obtain ⟨n,rfl⟩:=List.mem_ofFn.mp listed
        cases startsEq:starts.born with
        | none=>simp only [startsEq,orig,Option.isSome_none,Option.isSome_some,Bool.false_eq_true] at present
        | some ws=>exact ⟨_,run_.2 ws j startsEq orig n⟩
  have equality:=observed_eq (hCode:=age) A S ready pick lay P key (fun z=>hub z.2) slots chosen (a:=bytes) q (auth q)
    (fun x hx y hy=>same_grouped_rank roster flag next host physical (fun _ _ _ ok=>groups_preserved A rank ok)
      (reached x hx).choose_spec (reached y hy).choose_spec)
    (fun x _=>flagExact _) (fun x _=>rfl)
  have was:=marked_choice_read A native S ready rank win he coord named fit winner df edgeOrder profile q
  have count:=DescentSharedCableNames.Stage.source_grains A native S ready names q
  have price : Fin.ofNat (2^c) (units*G.b)=⟨normalized A chosen (.inl q.val),normalized_fits A S ready chosen _⟩ := by
    apply Fin.ext
    change (units*G.b)%2^c=_
    rw [show units=A.grainCount q.val from count]
    exact Nat.mod_eq_of_lt (normalized_fits A S ready chosen (.inl q.val))
  rw [left_,right_,opts,show picked_=_ from was,price]
  exact equality

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
