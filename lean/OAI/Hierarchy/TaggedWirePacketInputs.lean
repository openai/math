import OAI.Hierarchy.TaggedWirePacketOperands
import OAI.Hierarchy.TaggedWirePacketPrimary

namespace OAI
/-! # Descriptor operands built from the mounted local parties and primary/mate stream -/

noncomputable section
namespace Hierarchy.WireTelescope.StripPaths
open LinearAlgebra.SpectralBooks ChordGraph Probe AdaptiveProbe AdaptiveProbe.Strip
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM Calendar.CatalogueRows PacketTurns
open scoped Classical Fin.CommRing

variable {n k K N Rn W : ℕ} {A B Ball : Type}
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
local notation "U" => R⊕T
variable (extra : A⊕B→DistinctPair (TreeSite n k))
local notation "ends" => ColumnWires.ends (horizontal n) extra
variable (place : Ball×TreeSite n k↪Fin K) (u : Ball) (phys : Fin N→Chord K)
    (pr : ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k→Fin N) (ma : TreeColumn n→Fin k→Fin N)
    (tr : TreeLink n k→Fin N)
    (enum : Fin Rn≃(ColumnWires.Role (TreeColumn n) (Fin n) (A⊕B) k⊕TreeLink n k))
local notation "route" => Sum.elim (links (horizontal n) extra place u pr ma) (fun j=>[tr j]) ∘ enum
local notation "old" => Sum.elim (reportedRole place ends u) (reportedRole place (treeEnds n k) u) ∘ enum

def face (site : X→Expr) (p : DistinctPair X) (right : Bool) : Expr :=
  orderedWord (site p.left) (site p.right) right (site p.left) (site p.right)

theorem face_read (site : X→Expr) (m : Memory W) (reg : Word W) (room : K≤2^W)
    (mounted : ∀x,(site x).eval m reg=((place (u,x)).val : Word W))
    {I : Type} (pair : I→DistinctPair X) (i : I) (b : Bool) :
    (face site (pair i) b).eval m reg=
    ((if b then (reportedRole place pair u i).1.2 else (reportedRole place pair u i).1.1).val : Word W) := by
  rw [face,ordered_eval _ _ _ _ m reg (mounted _) (mounted _) room]
  by_cases order : place (u,(pair i).left)<place (u,(pair i).right)
  all_goals cases b <;> simp [reportedRole,orderedEnds,order,mounted]

def routedWord (site : X→Expr) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr)
    (r : U) (j : ℕ) : Expr :=
  r.elim (fun v=>hopWord (horizontal n) extra site primary mate v j) tree

theorem routed_read (site : X→Expr) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr)
    (m : Memory W) (reg : Word W) (room : K≤2^W) (mounted : ∀x,(site x).eval m reg=((place (u,x)).val : Word W))
    (v : Fin N→Word W) (prAt : ∀r,(primary r).eval m reg=v (pr r))
    (maAt : ∀c j,(mate c j).eval m reg=v (ma c j)) (trAt : ∀j,(tree j).eval m reg=v (tr j))
    (r : U) (j : Fin (Sum.elim (links (horizontal n) extra place u pr ma) (fun t=>[tr t]) r).length) :
    (routedWord extra site primary mate tree r j.val).eval m reg=
      v ((Sum.elim (links (horizontal n) extra place u pr ma) (fun t=>[tr t]) r).get j) := by
  rcases r with r|t
  · exact hop_eval (horizontal n) extra place u site pr ma primary mate v m reg room mounted prAt maAt r j
  · have value : [tr t].get j=tr t := by
      exact List.mem_singleton.mp (List.get_mem _ j)
    exact (trAt t).trans (congrArg v value.symm)

/-- The symbol array mentions only fixed roles and the public one- or two-hop
menu. Actual row keys, widths, and mounted site coordinates remain expressions. -/
def packetInputs (site : X→Expr) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr) (qty : U→Expr) :
    Operands fun i=>(route i).length where
  oldSite i b := face site ((enum i).elim ends (treeEnds n k)) b
  width i := qty (enum i)
  edge i j := routedWord extra site primary mate tree (enum i) j.val
  endSite i j b := routedWord extra site
    (fun v=>face site (ends (firstRole v)) b)
    (fun c a=>face site (ends (.radius c a true)) b)
    (fun t=>face site (treeEnds n k t) b) (enum i) j.val

theorem inputs_read (site : X→Expr) (primary : R→Expr) (mate : C→Fin k→Expr) (tree : T→Expr)
    (qty : U→Expr) (bits : Fin Rn→ℕ) (m : Memory W) (reg : Word W) (room : K≤2^W)
    (mounted : ∀x,(site x).eval m reg=((place (u,x)).val : Word W))
    (oldWidth : ∀i,(qty (enum i)).eval m reg=(bits i : Word W))
    (paid : ∀r,(primary r).eval m reg=((pr r).val : Word W))
    (mateRead : ∀c j,(mate c j).eval m reg=((ma c j).val : Word W))
    (treeRead : ∀j,(tree j).eval m reg=((tr j).val : Word W))
    (first : ∀r,phys (pr r)=reportedRole place ends u (firstRole r))
    (second : ∀c j,phys (ma c j)=reportedRole place ends u (.radius c j true))
    (trees : ∀j,phys (tr j)=reportedRole place (treeEnds n k) u j) :
    Reads old phys route bits (packetInputs extra place u pr ma tr enum site primary mate tree qty) m reg := by
  have oldEnd (i : Fin Rn) (b : Bool) :
      (face site ((enum i).elim ends (treeEnds n k)) b).eval m reg=
        ((if b then (old i).1.2 else (old i).1.1).val : Word W) := by
    rcases hr:enum i with r|t
    · simpa [hr,Function.comp_def] using face_read place u site m reg room mounted ends r b
    · simpa [hr,Function.comp_def] using face_read place u site m reg room mounted (treeEnds n k) t b
  have geo (b : Bool) (i : Fin Rn) (q : Fin (route i).length) :
      ((packetInputs extra place u pr ma tr enum site primary mate tree qty).endSite i q b).eval m reg=
        ((if b then (phys ((route i).get q)).1.2 else (phys ((route i).get q)).1.1).val : Word W) := by
    apply routed_read extra place u pr ma tr _ _ _ _ m reg room mounted
      (fun e=>((if b then (phys e).1.2 else (phys e).1.1).val : Word W))
    · intro r;rw [first];exact face_read place u site m reg room mounted _ _ b
    · intro c j;rw [second];exact face_read place u site m reg room mounted _ _ b
    · intro t;rw [trees];exact face_read place u site m reg room mounted _ _ b
  refine ⟨fun i=>oldEnd i false,fun i=>oldEnd i true,oldWidth,?_,fun i q=>geo false i q,fun i q=>geo true i q⟩
  intro i q
  exact routed_read extra place u pr ma tr site primary mate tree m reg room mounted (fun e=>(e.val : Word W))
    paid mateRead treeRead (enum i) q

end Hierarchy.WireTelescope.StripPaths

end
end OAI
