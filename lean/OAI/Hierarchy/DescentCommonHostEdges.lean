import OAI.Hierarchy.DescentCommonHost
import OAI.Hierarchy.DescentInstalledRotorLayers
import OAI.Hierarchy.DescentRotorPhysicalMaps
import OAI.Hierarchy.DescentOldTerminalFan

namespace OAI
/-! # Reading every real installed-bank edge in the common trivalent host -/

namespace Hierarchy.DescentCommonHost
open DescentChosenRouter DescentContacts DescentCanonicalPorts DescentRelativeContacts DescentMixedRouter
open scoped Classical
noncomputable section
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
variable {k n h C₀ bits u : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
local notation "Z" => V×Endpoint (2^n)
local notation "R" => DescentCommonPalette.rotor G
local notation "X" => Node V Z (Computability.BorderVNP.Crossing.Network.Site R)
variable (m : ℕ) (code : H ↪ V × Endpoint (2^n))
local notation "lab" => fun t=>shortName m (code t)
variable (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay) (D : ℕ)
local notation "Q" => network G hw u P.contact P.input P.site P.owner P.align (selected P G hw pay hardware) D
local notation "adj" => near P G m code
local notation "sn" => short (m:=m) P.b

/-- Projection of every hardware site onto its real position in the common
rotor or the absolute-depth-independent fallback tree. -/
def bankNode : (Q).Site→X
  | ⟨(s,.inl g),x⟩ =>
    .good s (sn g.val)
      ((DescentCommonPalette.rotorSiteEquiv G D (DescentChosenRouter.selectedRotorLayers P G hw pay hardware s g) C₀ bits u).symm x)
  | ⟨(s,.inr t),x⟩ => .fall s (lab t) (DescentCommonPalette.path x)

local notation "view" => bankNode P G m code hw pay hardware D

def publicNode (s : Bool) : P.Public→X
  | .inl (g,j) => .good s (sn g.val) ((R).attach (j,false))
  | .inr t => .fall s (lab t) []

theorem publicNode_at (s : Bool) (p : P.Public) : view ((Q).attach (s,p))=publicNode P G m code s p := by
  rcases p with ⟨g,j⟩|t
  · exact congrArg (fun v : (R).Site => (Node.good s (sn g.val) v : X))
      (DescentCommonPalette.rotor_pin_inv G D (DescentChosenRouter.selectedRotorLayers P G hw pay hardware s g) C₀ bits u (j,false))
  · cases s <;> rfl

theorem direct_at (s : Bool) (c : P.Contact) : view (if s then (Q).dst (.inl c) else (Q).src (.inl c))=
    direct G s (linkSocket P lab m s c) := by
  cases c with
  | inl c =>
    have socketProjection (side : Bool) :=
      congrArg (fun v : (R).Site => (Node.good side (P.outputName m side c).1 v : X))
        (DescentCommonPalette.rotor_pin_inv G D
          (DescentChosenRouter.selectedRotorLayers P G hw pay hardware side (P.ends side c.1)) C₀ bits u
          ((P.outputName m side c).2,true))
    cases s <;> exact socketProjection _
  | inr c => cases s <;> rfl

theorem link_mem (rotors : P.CommonOutputs m) (book : P.CommonFallback lab) (s : Bool) (c : P.Contact) :
    direct G (!s) (linkSocket P lab m (!s) c)∈adj (direct G s (linkSocket P lab m s c)) := by
  have peer := linkPeer_at P lab m rotors book s c
  rcases c with c|c
  · apply DescentCommonPalette.pin_mem R _ _ (p:=((P.outputName m s c).2,true))
    exact congrArg (Option.map (direct G (!s))) peer
  · let t := fallEnd P s c
    let e := fallLeg P s c
    let digits := (P.fallbackBook s t).codes e
    let T := DescentCommonPalette.tree (P.fallbackBook s t).height
    change _∈fallNear P G m code s (lab t) (DescentCommonPalette.path (t:=(P.fallbackBook s t).height) (T.attach (.inr digits)))
    rw [fallNear_at P G m code s (lab t) (height_at P m code book s t) (T.attach (.inr digits))]
    apply DescentCommonPalette.pin_mem T _ _ (p:=.inr digits)
    exact congrArg (Option.map (direct G (!s))) peer

theorem public_mem (book : P.CommonFallback lab) (s : Bool) (p : P.Public) :
    let z := shortName m (publicAddress P code p)
    publicNode P G m code s p ∈ adj (.trunk s z) ∧
    .trunk s z ∈ adj (publicNode P G m code s p) := by
  rcases p with ⟨g,j⟩|t
  · constructor
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      change (.good s (sn g.val) ((R).attach (j,false)) : X)∈(some (.good s (sn g.val) ((R).attach (j,false)) : X)).toFinset
      simp
    · exact DescentCommonPalette.pin_mem R _ _ (p:=(j,false)) rfl
  · constructor
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    · let T := DescentCommonPalette.tree (P.fallbackBook s t).height
      change _∈fallNear P G m code s (lab t) (DescentCommonPalette.path (t:=(P.fallbackBook s t).height) (T.attach (.inl ())))
      rw [fallNear_at P G m code s (lab t) (height_at P m code book s t) (T.attach (.inl ()))]
      exact DescentCommonPalette.pin_mem T _ _ (p:=.inl ()) rfl

theorem internal_mem (rotors : P.CommonOutputs m) (book : P.CommonFallback lab) (e : (Q).Edge) :
    view ((Q).dst e)∈adj (view ((Q).src e)) ∧ view ((Q).src e)∈adj (view ((Q).dst e)) := by
  rcases e with c|⟨⟨s,g|t⟩,e⟩
  · have left : view ((Q).src (.inl c))=direct G false (linkSocket P lab m false c) := direct_at P G m code hw pay hardware D false c
    have right : view ((Q).dst (.inl c))=direct G true (linkSocket P lab m true c) := direct_at P G m code hw pay hardware D true c
    rw [left,right]
    exact ⟨link_mem P G m code rotors book false c,link_mem P G m code rotors book true c⟩
  · let layers := DescentChosenRouter.selectedRotorLayers P G hw pay hardware s g
    let configured := DescentPhysicalSplit.graph (DescentRotor.Physical.host G.arcs D layers C₀ bits u)
    let readSite := (DescentCommonPalette.rotorSiteEquiv G D layers C₀ bits u).symm
    let wire := (DescentCommonPalette.rotorEdgeEquiv G D layers C₀ bits u).symm e
    let node := fun v : (R).Site => (Node.good s (sn g.val) v : X)
    let external := goodExt P G m code s (sn g.val)
    change node (readSite (configured.dst e)) ∈
        DescentCommonPalette.near R node external (readSite (configured.src e)) ∧
      node (readSite (configured.src e)) ∈
        DescentCommonPalette.near R node external (readSite (configured.dst e))
    have left : readSite (configured.src e)=(R).src wire :=
      DescentCommonPalette.rotor_left_inv G D layers C₀ bits u e
    have right : readSite (configured.dst e)=(R).dst wire :=
      DescentCommonPalette.rotor_right_inv G D layers C₀ bits u e
    rw [left,right]
    exact ⟨DescentCommonPalette.next_mem R node external wire,
      DescentCommonPalette.prev_mem R node external wire⟩
  · let T := DescentCommonPalette.tree (P.fallbackBook s t).height
    change _∈fallNear P G m code s (lab t) (DescentCommonPalette.path (t:=(P.fallbackBook s t).height) (T.src e)) ∧
      _∈fallNear P G m code s (lab t) (DescentCommonPalette.path (t:=(P.fallbackBook s t).height) (T.dst e))
    rw [fallNear_at P G m code s (lab t) (height_at P m code book s t) (T.src e),
      fallNear_at P G m code s (lab t) (height_at P m code book s t) (T.dst e)]
    exact ⟨DescentCommonPalette.next_mem T _ _ e,DescentCommonPalette.prev_mem T _ _ e⟩

end
end Hierarchy.DescentCommonHost

end OAI
