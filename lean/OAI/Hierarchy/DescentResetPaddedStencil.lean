import OAI.Hierarchy.DescentPaddedFlowChips
import OAI.Hierarchy.DescentResetStencilSlots
import OAI.Hierarchy.DescentResetStencilPorts
import OAI.Hierarchy.DescentPaddedSites

namespace OAI
/-! # The total padded physical stencil agrees with the recorded old vertex at every genuine site -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentGL DescentColonies DescentPackedColony DescentSIMDLookup DescentIssuedFallbackPanel
open DescentPlainTerminal.Suffix DescentPackedFlowPair.Padded
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k m c H N n : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (hosts : V≃Fin H) (ph : H≤N) (digits : Block m≃J×Block k)
    (small : c≤ m) (L : DescentGL.Layout m) (depth : V→ℕ) (f B K g cap : ℕ)
local notation "rank" => hosts.toEmbedding.trans (Fin.castLEEmb ph)
local notation "scanDepth" => 32*Nat.clog 2 (2*A.degree)
local notation "padded" => roster (D:=A.degree) A hosts ph
local notation "truePort" => portAt A hosts
local notation "traffic" => A.resetFlow digits
local notation "weights" => A.resetLoad digits
local notation "realList" => fun v:V=>(slots A.degree).filterMap (truePort v)
local notation "rowList" => incoming (peers padded)
local notation "felt" => (fun hi v x=>rearrangedLoad (load A hosts digits) L v (join small hi x))
local notation "sim" => (fun hi=>Scan.build rowList (felt hi) scanDepth (2^(f+1)*B) (m-c))
local notation "symNear" => fun v u (h:u∈A.near v)=>(A.symmetric v u).mp h
private theorem mutual_reverse (v u : V) (h : u∈A.mutual v) : v∈A.mutual u :=
  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).2,(Finset.mem_filter.mp h).1⟩

local notation "portsAt" => ContactRoster.ports A.mutual truePort (actual_ports A hosts symNear) (mutual_reverse A)

def hostHeader (v : Fin N) (i : Fin 3) : Cell n :=
  (project H v).elim 0 fun u=>
    ((if i.val=0 then depth (hosts.symm u)-c else if i.val=1 then m-g-c else (A.hub (hosts.symm u)).toNat):ℕ)

def side {a : ℕ} (p : Fin (a+a)) : Fin a := Sum.elim id id (finSumFinEquiv.symm p)

def portHeader (v : Fin N) (p : Fin (A.degree+A.degree)) (i : Fin 2) : Cell n :=
  (project H v).elim 0 fun t=>
    let v':=hosts.symm t
    let slot:=side p
    (((truePort v' slot).elim 0 fun u=>
      let dep:=max (depth v') (depth u)
      if i.val=0 then dep-c else threshold K (2^f*B) dep (∑x,traffic v' u x) (2^(m-c)*cap)):ℕ)

theorem socket_padded (v : V) (j : Fin A.degree) :
    padded (rank v) j=(truePort v j).map rank := by
  unfold roster DescentPackedFlowPair.Padded.next portAt
  change (project H ((hosts v).castLE ph)).bind _ = _
  simp only [project_cast,
    show project A.degree j=some j from project_cast le_rfl j]
  cases result : PackedFlow.next A hosts (hosts v) j <;> simp [result]

theorem incoming_at (v : V) : rowList (rank v)=(realList v).map rank := by
  unfold incoming peers
  rw [List.filterMap_map, List.map_filterMap]
  exact congrArg (fun get => List.filterMap get (slots A.degree))
    (funext fun j => socket_padded A hosts ph v j)

theorem listed_at (u v : V) : u∈realList v ↔ v∈A.mutual u := by
  have included (j : Fin A.degree) : j∈slots A.degree:=by simp [slots,List.mem_ofFn]
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨j,_,hit⟩
    have orig:=(actual_ports A hosts symNear v u).mpr ⟨j,hit⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp orig).2,(Finset.mem_filter.mp orig).1⟩
  · intro orig
    have rev : u∈A.mutual v :=Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp orig).2,(Finset.mem_filter.mp orig).1⟩
    obtain ⟨j,hit⟩:=(actual_ports A hosts symNear v u).mp rev
    exact ⟨j,included j,hit⟩

theorem actor (v : V) (hi : Block c) :
    Stencil.physical small L (hostHeader (m:=m) (c:=c) A hosts depth g)
      (portHeader (c:=c) A hosts digits depth f B K cap)
      (fun u hi x=>felt hi u x) (fun p u hi x=>flow A hosts digits (side p) u ((rearrange L).symm (join small hi x)))
      sim (rank v) hi=
    Stencil.measured (n:=n) small A.mutual depth L weights traffic A.hub A.degree f B K g cap portsAt realList v hi := by
  have live : project H (rank v)=some (hosts v):=project_cast ph _
  have same (u : V) (x : Block (m-c)) : felt hi (rank u) x=
      rearrangedLoad weights L u (join small hi x) := by
    simp only [rearrangedLoad,load,show project H (rank u)=some (hosts u) from project_cast ph _,Option.elim_some,
      Equiv.symm_apply_apply]
  funext j
  rcases j with t|((x|⟨d,x⟩)|(⟨i,x⟩|⟨j,s⟩))
  · simp [Stencil.physical,Stencil.measured,hostHeader]
  · exact congrArg (fun z:ℕ=>(z:Cell n)) (same v x)
  · exact congrArg (fun z:Bool=>(z.toNat:Cell n)) (Scan.padded_lookup rank realList rowList
      (fun v x=>rearrangedLoad weights L v (join small hi x)) (felt hi)
      (incoming_at A hosts ph) same scanDepth (2^(f+1)*B) (m-c) d.val v x)
  · by_cases order : (rearrange L).symm (join small hi i)<(rearrange L).symm (join small hi x) <;>
      simp [Stencil.physical,Stencil.measured,order]
  · have measured:=signed_port A hosts digits small symNear depth L f B K cap v hi (finSumFinEquiv.symm j) s
    refine Eq.trans ?_ (congrArg (fun a : ℕ => (a : Cell n)) measured).symm
    cases s with
    | inl z=>simp only [Stencil.physical,portHeader,portData,side,half,live,Option.elim_some,Equiv.symm_apply_apply]
    | inr z=>
      simp only [Stencil.physical,flow,portData,side,half,live,Option.elim_some,
        show ∀j:Fin A.degree,project A.degree j=some j from fun j=>project_cast le_rfl j]

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
