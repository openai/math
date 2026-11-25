import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentPackedColonyData

namespace OAI
/-! # Native updates of the packed split cache at all common sites and group lanes -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup DescentColonies DescentColonies.PackedSplit DescentGL
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M k b w Δ : ℕ}

def folder (P : Ports Δ) (prior : Bank) (H : ℕ) (T : DescentPackedZip.Tables) (u : Expr) (i : Fin Δ) :=
  T.read u (peerExpr P prior H i)

def slots (Δ : ℕ) : List (Fin Δ) := List.ofFn id

def term (P : Ports Δ) (prior weight : Bank) (H : ℕ) (base add : DescentPackedZip.Tables) : Expr :=
  (slots Δ).foldl (folder P prior H add) (base.read (.lookup prior .row) (.lookup weight .row))

theorem fold_source (P : Ports Δ) (prior : Bank) (T : DescentPackedZip.Tables) (D d : ℕ)
    (out : ℕ) (m : Memory w) (roster : Fin H→Fin Δ→Option (Fin H)) (prev : Fin H→Fin G→Panel k)
    (word : DescentPackedZip.Static T (merge (k:=k) D d) M m)
    (tab : WordRoom T (width k) (width k) M w out) (access : Accessible P prior H G M w out)
    (arr : ∀i,DescentPackedZip.Source (peerExpr P prior H i) (fun v g=>receive (fun u=>prev u g) (roster v i)) M m)
    (is : List (Fin Δ)) (u : Expr) (safe : u.Fits w out) (x : Fin H→Fin G→Panel k) (src : DescentPackedZip.Source u x M m) :
    DescentPackedZip.Source (is.foldl (folder P prior H T) u)
      (fun v g=>(is.map (fun i=>receive (fun n=>prev n g) (roster v i))).foldl (merge D d) (x v g)) M m := by
  induction is generalizing u x with
  | nil=>exact src
  | cons i is ih=>
    have fit:=peer_fits P prior out access i
    exact ih _ (tab.safe u _ safe fit) _ (DescentPackedZip.read_data T u _ out (tab.issue u _ safe fit)
      _ (merge_zero ..) m word x _ src (arr i))

def peers (roster : Fin H→Fin Δ→Option (Fin H)) (v : Fin H) := (slots Δ).map (roster v)

def stateAt (roster : Fin H→Fin Δ→Option (Fin H)) (W : Fin G→Fin H→Block k→ℕ)
    (D cap : ℕ) (a μ : Bits k) (s : ℕ) (v : Fin H) (g : Fin G) :=
  cache (Scan.build (incoming (peers roster)) (multiplierLoad (W g) a μ) D cap s) v

structure StageRoom (P : Ports Δ) (prior wt : Bank) (base add : DescentPackedZip.Tables)
    (H G k b M w out : ℕ) : Prop where
  neighbors : Accessible P prior H G M w out
  weight : wt.Fits w out
  rows : H*chunks G M≤wt.size
  base : WordRoom base (width k) (b*2^k) M w out
  add : WordRoom add (width k) (width k) M w out

theorem term_fits (P : Ports Δ) (prior wt : Bank) (base add : DescentPackedZip.Tables)
    (out : ℕ) (space : StageRoom P prior wt base add H G k b M w out) :
    (term P prior wt H base add).Fits w out := by
  have fold (is : List (Fin Δ)) (u : Expr) (safe : u.Fits w out) :
      (is.foldl (folder P prior H add) u).Fits w out := by
    induction is generalizing u with
    | nil=>exact safe
    | cons i is ih=>exact ih _ (space.add.safe _ _ safe (peer_fits P prior out space.neighbors i))
  exact fold _ _ (space.base.safe _ _ ⟨space.neighbors.source,trivial⟩ ⟨space.weight,trivial⟩)

theorem term_read (P : Ports Δ) (prior wt : Bank) (base add : DescentPackedZip.Tables)
    (out : ℕ) (space : StageRoom P prior wt base add H G k b M w out)
    (m : Memory w) (roster : Fin H→Fin Δ→Option (Fin H)) (mounted : Mounted P roster m G M)
    (W : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (a μ : Bits k) (s : ℕ) (lt : s<k)
    (room : ∀g v x,W g v x<2^b)
    (fixed : DescentPackedZip.Static base (baseUpdate (b:=b) a μ cap (k-(s+1))) M m)
    (fixed' : DescentPackedZip.Static add (merge (k:=k) D (k-(s+1))) M m)
    (before : Reads prior (stateAt roster W D cap a μ s) M m)
    (dataW : Reads wt (fun v g=>counts b (W g v)) M m) :
    DescentPackedZip.Source (term P prior wt H base add) (stateAt roster W D cap a μ (s+1)) M m := by
  let d:=k-(s+1)
  let old:=stateAt roster W D cap a μ s
  let u : Expr:=.lookup prior .row
  let val : Expr:=.lookup wt .row
  have hu : u.Fits w out:=⟨space.neighbors.source,trivial⟩
  have hv : val.Fits w out:=⟨space.weight,trivial⟩
  have src := DescentPackedZip.source_column prior out space.neighbors.source m old space.neighbors.srcRoom before
  have cnt := DescentPackedZip.source_column wt out space.weight m _ space.rows dataW
  have first := DescentPackedZip.read_data base u val out (space.base.issue _ _ hu hv)
    (baseUpdate (b:=b) a μ cap d) (base_zero ..) m fixed old _ src cnt
  have allRows := fold_source P prior add D d out m roster old fixed' space.add space.neighbors
    (fun i=>peerSource P prior out space.neighbors roster m mounted old before i)
    (slots Δ) (base.read u val) (space.base.safe _ _ hu hv) _ first
  have same (v : Fin H) (g : Fin G) :=
    advance (peers roster) (W g) D cap a μ s lt v (room g v)
  have calcRows : DescentPackedZip.Source (term P prior wt H base add)
      (fun v g=>((peers roster v).map (receive (fun n=>old n g))).foldl (merge D d)
      (baseUpdate a μ cap d (old v g) (counts b (W g v)))) M m := by
    simpa only [term,peers,List.map_map,Function.comp_def] using allRows
  have eq : (fun v g=>((peers roster v).map (receive (fun n=>old n g))).foldl (merge D d)
      (baseUpdate a μ cap d (old v g) (counts b (W g v))))=stateAt roster W D cap a μ (s+1) :=
    funext (fun v=>funext (same v))
  rwa [eq] at calcRows

theorem term_work (P : Ports Δ) (prior weight : Bank) (H : ℕ) (base add : DescentPackedZip.Tables) :
    (term P prior weight H base add).work=25+56*Δ := by
  have step (xs : List (Fin Δ)) (acc : Expr) :
      (xs.foldl (folder P prior H add) acc).work=acc.work+56*xs.length := by
    induction xs generalizing acc with
    | nil=>simp
    | cons i xs ih=>
      simp only [List.foldl_cons,ih,List.length_cons,folder,DescentPackedZip.work]
      have hw : (peerExpr P prior H i).work=45 := rfl
      rw [hw];omega
  simp only [term,step,slots,List.length_ofFn,DescentPackedZip.work]
  rfl

end
end Hierarchy.DescentPackedColony

end OAI
