import OAI.Hierarchy.DescentResetActorWindow

namespace OAI
/-! # Querying a physical reset actor from its remixed stencil digits -/
namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentContacts DescentChosenRouter
open DescentActorRaster (complete absoluteBase)
open DescentRelativeContacts DescentFallbackLeafScan DescentPlainTerminal
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
  {d k : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
  {price ε : ℝ} {h C Ht g : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
  {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)
variable (vertex : V↪ℕ) (near : V→Finset V) (n f B wire K Δ : ℕ)
    (wt : V→Block k→ℕ) (flow : V→V→Block k→ℝ)
variable (roster : SourceFrame.Roster Z T pos ix hub g frame vertex near n f B wire K flow Δ wt)
local notation "fallbackDegree" => 32*Nat.clog 2 (2*Δ)
local notation "m" => T.commonDepth
local notation "depth" => fun v=>Z.placement.b (frame.host v)
local notation "budget" => roster.2.2.2.2.2.choose
local notation "ep" => DescentPlainTerminal.endpoint near depth frame.basis wt f fallbackDegree B g (2^Z.n) budget (fun v j=>(frame.host v,j)∈Z.placement.keys) hub

open DescentIssuedFallbackPanel DescentPlainTerminal.Suffix DescentSIMDLookup
local notation "fit" => frame.enough.trans (Nat.sub_le ..)
local notation "r" => k-m
local notation "Y" => 2^Z.n
local notation "old" => fun (highId : Block m) (j : Block r)=>(rearrange frame.basis).symm (join fit highId j)
local notation "shape_" => fun v hi j=>fieldsRelative m (ep v (old hi j))
local notation "key_" => fun v hi j=>(hub v || decide ((frame.host v,group (depth v) (join fit hi j))∈Z.placement.keys)).toNat

theorem stencil_terminal (v : V) (hi : Block m) (z : Endpoint Y)
    (legal : z.1.2<2^z.1.1) (width : z.1.1≤r) (words : Block r→ℕ)
    (measured : ∀j,words j=2*Stencil.shapeCode r Y (shape_ v hi j)+key_ v hi j) :
    (∃t,T.code t=complete m hi.val (frame.host v,z)) ↔
    ∃j,words j/2=DescentFallbackShapeTable.cell r z := by
  have upper (u : V) : depth u≤k:=(Z.placement.depth (frame.host u)).trans_eq frame.extent
  have lower (u : V) : m≤depth u:=T.commonLow _
  let z' := complete m hi.val (frame.host v,z)
  have whole : (∃t,T.code t=z') ↔ ∃x,ep v x=expand m hi.val (DescentPlainTerminal.fields z) := by
    change (∃t,T.code t=(frame.host v,z'.2)) ↔ _
    rw [terminal_hit frame vertex near n f B wire K Δ wt flow roster v z'.2]
    simp [List.any_eq_true,z',expand,DescentPlainTerminal.fields,complete]
  rw [whole,terminal_window near depth frame.basis wt f fallbackDegree B g Y budget (fun v j=>(frame.host v,j)∈Z.placement.keys) hub fit frame.enough lower upper v hi (DescentPlainTerminal.fields z) legal]
  apply exists_congr
  intro j
  have bit : key_ v hi j<2:=(fun b : Bool => show b.toNat < 2 from by cases b <;> decide) _
  have data:=measured j
  have part : words j/2=Stencil.shapeCode r Y (shape_ v hi j):=by
    rw [data,Nat.mul_add_div (by decide : 0<2),Nat.div_eq_of_lt bit,Nat.add_zero]
  rw [part,←Stencil.shapeCode_fields]
  apply Iff.symm
  apply suffix_code_injective
  · have within:=(endpoint_window near depth frame.basis wt f fallbackDegree B g Y budget (fun v j=>(frame.host v,j)∈Z.placement.keys) hub fit frame.enough lower upper v (old hi j)).2.1
    exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right within m))
  · exact legal.trans_le (Nat.pow_le_pow_right (by decide) width)
  · exact endpoint_tag near depth frame.basis wt f fallbackDegree B g Y budget (fun v j=>(frame.host v,j)∈Z.placement.keys) hub (Nat.two_pow_pos _) v (old hi j)
  · intro q eqn
    rcases z with ⟨⟨dz,iz⟩,(_|t)⟩
    · simp [DescentPlainTerminal.fields] at eqn
    · obtain rfl : t.val=q := by simpa [DescentPlainTerminal.fields] using eqn
      exact t.isLt

private theorem prefix_onto {d width id : ℕ} (bound : d≤width) (ok : id<2^d) :
    ∃j : Block width,group d j=id := by
  let gap:=2^(width-d)
  have positive : 0<gap:=Nat.two_pow_pos _
  have total : 2^d*gap=2^width:=by rw [←pow_add];congr 1;omega
  let j : Block width:=⟨id*gap,(Nat.mul_lt_mul_of_pos_right ok positive).trans_eq total⟩
  exact ⟨j,by change id*gap/gap=id;exact Nat.mul_div_cancel _ positive⟩

theorem stencil_good (s : Bool) (v : V) (hi : Block m) (id : ℕ)
    (cell : (DescentCommonPalette.rotor Z.graph).Site) (words : Block r→ℕ)
    (measured : ∀j,words j=2*Stencil.shapeCode r Y (shape_ v hi j)+key_ v hi j) :
    emits Z T (.good s (frame.host v,id) cell) hi ↔
      ∃j : Block r,group (depth v-m) j=id ∧ words j%2=0 := by
  rw [good_query]
  have lo:=T.commonLow (frame.host v)
  have upper:depth v≤k:=(Z.placement.depth _).trans_eq frame.extent
  have dOk:depth v-m≤r:=Nat.sub_le_sub_right upper m
  have ownership (j : Block r) :
      group (depth v) (join fit hi j)=hi.val*2^(depth v-m)+group (depth v-m) j := by
    have joined:=join_group fit hi j (depth v-m)
    rwa [Nat.add_sub_of_le (T.commonLow (frame.host v)),Nat.sub_sub_self dOk] at joined
  have keyRead (j : Block r) : words j%2=0 ↔
      ¬Z.placement.hub (frame.host v) ∧
      (frame.host v,hi.val*2^(depth v-m)+group (depth v-m) j)∉Z.placement.keys := by
    rw [measured j]
    dsimp only
    rw [ownership j,frame.rotorHub]
    generalize Stencil.shapeCode r Y (shape_ v hi j)=z
    cases hv:hub v <;> by_cases flag : (frame.host v,hi.val*2^(depth v-m)+group (depth v-m) j)∈Z.placement.keys <;>
      simp [Nat.mul_comm 2,Nat.mul_add_mod_self_right,flag]
  by_cases ok:id<2^(depth v-m)
  · rw [activeBase,dite_eq_left ok]
    have registered : absoluteBase Z.placement.b T.commonLow (frame.host v,id) hi ok ∈ DescentColonies.validBases Z.placement.b Z.placement.keys ↔
        (frame.host v,hi.val*2^(depth v-m)+id)∈Z.placement.keys :=
      ⟨fun h=> (Finset.mem_filter.mp h).2,fun h=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
    rw [registered]
    constructor
    · rintro ⟨miss,nonhub⟩
      obtain ⟨j,atId⟩:=prefix_onto dOk ok
      exact ⟨j,atId,(keyRead j).mpr ⟨nonhub,by rwa [atId]⟩⟩
    · rintro ⟨j,eqn,hj⟩
      obtain ⟨nonhub,miss⟩:=(keyRead j).mp hj
      exact ⟨by rwa [←eqn],nonhub⟩
  · rw [activeBase,dite_eq_right ok]
    simp only [false_iff]
    rintro ⟨j,atId,_⟩
    exact ok (atId ▸ DescentHostDirectory.group_lt dOk j)

/-- The selected fallback table height at a present root is shared by the
entire surviving block. -/
theorem stencil_fall (s : Bool) (v : V) (hi : Block m) (z : Endpoint Y) (path : List Bool)
    (legal : z.1.2<2^z.1.1) (width : z.1.1≤r) (words : Block r→ℕ)
    (measured : ∀j,words j=2*Stencil.shapeCode r Y (shape_ v hi j)+key_ v hi j)
    (height : ℕ) (header : ∀t,T.code t=complete m hi.val (frame.host v,z)→(Z.placement.fallbackBook s t).height=height) :
    emits Z T (.fall s (frame.host v,z) path) hi ↔
        (∃j,words j/2=DescentFallbackShapeTable.cell r z) ∧ path.length≤height := by
  rw [fall_query, and_iff_right legal,←stencil_terminal frame vertex near n f B wire K Δ wt flow roster v hi z legal width words measured]
  constructor
  · rintro ⟨t,read,length⟩
    obtain ⟨u,hu,ha⟩:=(terminal_read Z T _ _ _).mp read
    exact ⟨⟨u,hu⟩,by rwa [←ha,header u hu] at length⟩
  · rintro ⟨⟨u,hu⟩,length⟩
    exact ⟨height,(terminal_read Z T _ _ _).mpr ⟨u,hu,header u hu⟩,length⟩

theorem stencil_trunk (s : Bool) (v : V) (hi : Block m) (z : Endpoint Y)
    (legal : z.1.2<2^z.1.1) (width : z.1.1≤r) (words : Block r→ℕ)
    (measured : ∀j,words j=2*Stencil.shapeCode r Y (shape_ v hi j)+key_ v hi j) :
    emits Z T (.trunk s (frame.host v,z)) hi ↔ ∃j,words j/2=DescentFallbackShapeTable.cell r z := by
  rw [trunk_query, and_iff_right legal,←stencil_terminal frame vertex near n f B wire K Δ wt flow roster v hi z legal width words measured]
  generalize arg : complete m hi.val (frame.host v,z)=a
  constructor
  · intro present
    cases read:terminalEntry Z T s a with
    | none=>simp [read] at present
    | some n=>
      obtain ⟨u,eq,_⟩:=(terminal_read Z T s a n).mp read
      exact ⟨u,eq⟩
  · rintro ⟨u,eq⟩
    rw [(terminal_read Z T s a _).mpr ⟨u,eq,rfl⟩]
    rfl

variable {Δ} in
/-- This is the header stored once per prior host and local terminal. It is
independent of the surviving high block. -/
def heightAt (v : V) (z : Endpoint Y) (peer : V→Fin Δ→Option V) : ℕ :=
  Nat.clog 2 ((Finset.univ.filter (fun j : Fin Δ×Fin (2^Ht)=>
    (DescentFallbackLeafScan.candidate (k:=Z.k-m) (D:=fallbackDegree) (g:=g) (f:=f)
      (fun v=>hub (frame.host.symm v))
      (fun v (i : Fin Δ)=>(peer (frame.host.symm v) i).map frame.host) (frame.host v,z) j).isSome)).card)

include roster in
theorem window_height (peer : V→Fin Δ→Option V) (real : ∀v u,u∈near v ↔ ∃j,peer v j=some u)
    (s : Bool) (v : V) (hi : Block m) (z : Endpoint Y) (legal : z.1.2<2^z.1.1)
    (t : Z.Fallback) (atZ : T.code t=complete m hi.val (frame.host v,z)) :
    (Z.placement.fallbackBook s t).height=heightAt frame f v z peer := by
  rw [source_height frame vertex near n f B wire K Δ wt flow roster peer real]
  have rel : shortName m (T.code t)=(frame.host v,z):=by
    rw [atZ]
    rcases z with ⟨⟨d,id⟩,tag⟩
    simp [shortName,complete,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt legal]
  simp only [rel,heightAt]

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
