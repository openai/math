import OAI.Hierarchy.DescentResetStencilActors
import OAI.Hierarchy.DescentResetActorCPU
import OAI.Hierarchy.DescentDenseHostTape

namespace OAI
/-! # Occupied reset rack bits read at their actual normalized host shape -/
namespace Hierarchy.DescentSixParty.ResetInput.SourceFrame
open DescentGL DescentColonies DescentContacts DescentChosenRouter
open DescentRelativeContacts DescentFallbackLeafScan DescentPlainTerminal
open scoped Classical Fin.CommRing
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
local notation "D" => 32*Nat.clog 2 (2*Δ)
local notation "m" => T.commonDepth
local notation "depth" => fun v=>Z.placement.b (frame.host v)
local notation "budget" => roster.2.2.2.2.2.choose
local notation "ep" => DescentPlainTerminal.endpoint near depth frame.basis wt f D B g (2^Z.n) budget (fun v j=>(frame.host v,j)∈Z.placement.keys) hub

open DescentIssuedFallbackPanel DescentPlainTerminal.Suffix DescentSIMDLookup
local notation "fit" => frame.enough.trans (Nat.sub_le ..)
local notation "suffixBits" => k-m
local notation "tagCard" => 2^Z.n
local notation "old" => fun (highId : Block m) (j : Block suffixBits)=>(rearrange frame.basis).symm (join fit highId j)
local notation "shape_" => fun v hi j=>fieldsRelative m (ep v (old hi j))
local notation "key_" => fun v hi j=>(hub v || decide ((frame.host v,group (depth v) (join fit hi j))∈Z.placement.keys)).toNat

open DescentActorRaster.CPU DescentCommonHost DescentDenseHostOrder
local notation "board" => DescentCommonPalette.rotor Z.graph
local notation "shapeType" => Node Unit (Unit×Endpoint tagCard) (board).Site

/-- The opcode is entirely determined by the public common pool shape. -/
def opcode {J : Type} {Y : ℕ} (r : ℕ) : Node Unit (Unit×Endpoint Y) J → Query
  | .good _ z _=>.rotor z.2
  | .trunk _ (_,z)=>if z.1.2<2^z.1.1 ∧ z.1.1≤r then .trunk (DescentFallbackShapeTable.cell r z) else .empty
  | .fall _ (_,z) p=>if z.1.2<2^z.1.1 ∧ z.1.1≤r then .tree (DescentFallbackShapeTable.cell r z) p.length else .empty

variable {Δ} in
def levelAt (peer : V→Fin Δ→Option V) (v : V) : shapeType→ℕ
  | .good ..=>depth v-m
  | .trunk ..=>0
  | .fall _ (_,z) _=>if z.1.2<2^z.1.1 ∧ z.1.1≤ suffixBits then heightAt frame f v z peer else 0

include frame in
omit [Fintype V] [DecidableEq V] in
private theorem legal_full (t : Z.Fallback) :
    let z:=(shortName m (T.code t)).2
    z.1.2<2^z.1.1 ∧ z.1.1≤ suffixBits :=
  ⟨Nat.mod_lt _ (Nat.two_pow_pos _),Nat.sub_le_sub_right ((T.codeLegal t).2.1.trans_eq frame.extent) _⟩

theorem issued_bit (peer : V→Fin Δ→Option V) (real : ∀v u,u∈near v ↔ ∃j,peer v j=some u)
    (v : V) (hi : Block m) (q : shapeType) {t a : ℕ} (data : Fin (2^suffixBits)→Cell t)
    (measured : ∀j,(data j).val=2*Stencil.shapeCode suffixBits tagCard (shape_ v hi j)+key_ v hi j)
    (fits : levelAt frame f peer v q+1<2^a) :
    gate suffixBits t a (opcode suffixBits q) (encode t (2^suffixBits) data) (levelAt frame f peer v q+1:ℕ)=
        if emits Z T (recover Z.graph (frame.host v) q) hi then 1 else 0 := by
  rw [active _ _ _ _ _ _ fits]
  apply if_congr _ rfl rfl
  cases q with
  | good s u cell=>
      exact (stencil_good frame vertex near n f B wire K Δ wt flow roster s v hi u.2 cell _ measured).symm
  | trunk s z=>
      by_cases ok:z.2.1.2<2^z.2.1.1 ∧ z.2.1.1≤ suffixBits
      · simp only [opcode,ite_eq_left ok,accepts,recover]
        exact (stencil_trunk frame vertex near n f B wire K Δ wt flow roster s v hi z.2 ok.1 ok.2 _ measured).symm
      · simp only [opcode,ite_eq_right ok,accepts,recover,false_iff]
        rintro ⟨t,name,_⟩
        have physical : (shortName m (T.code t)).2 = z.2 := congrArg Prod.snd name
        exact ok (physical ▸ legal_full frame t)
  | fall s z path=>
      by_cases ok:z.2.1.2<2^z.2.1.1 ∧ z.2.1.1≤ suffixBits
      · simp only [opcode,ite_eq_left ok,accepts,recover,levelAt]
        exact (stencil_fall frame vertex near n f B wire K Δ wt flow roster s v hi z.2 path ok.1 ok.2 _ measured _
          (window_height frame vertex near n f B wire K Δ wt flow roster peer real s v hi z.2 ok.1)).symm
      · simp only [opcode,ite_eq_right ok,accepts,recover,false_iff]
        rintro ⟨t,name,_,_⟩
        have physical : (shortName m (T.code t)).2 = z.2 := congrArg Prod.snd name
        exact ok (physical ▸ legal_full frame t)

end
end Hierarchy.DescentSixParty.ResetInput.SourceFrame

end OAI
