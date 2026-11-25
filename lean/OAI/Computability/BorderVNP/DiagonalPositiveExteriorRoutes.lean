import OAI.Computability.BorderVNP.RoutingISASignedPrepRouteFiber
import OAI.Computability.BorderVNP.CubeScatterTransmissionFiber

/-! # Eliminating the entire physical exterior at a fixed positive source header

The common header occupies every unordered block. The incoming deliveries, relay
legs, co-owned route choices and unused zeros are then forced by the actual shared
row words. The equivalence retains these words even when a subsequent stage returns
field or signed value zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator Routing
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type}
variable (G : Wiring R r t d link inner n Edge) (L : WireLayout (R+1) r link)
variable (tab : TableLayout) (row : ℕ → TableRow) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
variable (guess : Fin (R+1) → ℕ → Bool) (g : SharedRows.Layout)
variable {axes groups blocks K h : ℕ} (decl : LengthDeclaration axes groups)
variable (fixed : Block (R+1)) (header : List Bool) (len : header.length = L.header)

/-- Exterior assignments on which every block carries the specified exact list. -/
abbrev HeaderExterior (L : WireLayout (R+1) r link) (header : List Bool) :=
  {ext : Exterior R r link → Bool // ∀ b, JointHeader.observed L ext b = header}

/-- The full list observed at every block of the constructed canonical exterior. -/
theorem observed_exterior (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) (b : Block (R+1)) :
    JointHeader.observed L (JointHeader.exterior L header len payload) b = header := by
  unfold JointHeader.observed
  rw [JointHeader.exterior_header]
  apply List.ext_getElem (by simp [len])
  intro j hj _
  simp only [List.getElem_ofFn,JointHeader.headerBits]

private theorem exterior_congr {xs ys : List Bool} {hx : xs.length = L.header} {hy : ys.length = L.header}
    (eq : xs=ys) (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) :
    JointHeader.exterior L xs hx payload = JointHeader.exterior L ys hy payload := by subst ys; rfl

set_option quotPrecheck false in
local notation "Raw" => {z : Symbols groups → List Bool // ∀ p, (z p).length = SharedRows.reserved blocks K h decl p}
set_option quotPrecheck false in
local notation "Admitted" x => {z : Symbols groups → List Bool // RouteWords (G:=G) (ext:=Subtype.val x) (L:=L)
  (D:=D) (pp:=pp) (lp:=lp) (guess:=guess) (tab:=tab) (row:=row) (g:=g) (blocks:=blocks) (K:=K) (h:=h) (decl:=decl) fixed z}

/-- Exactly one exterior can carry a fixed family of routed shared words. Summing
over all complete exteriors with this source header therefore introduces no factor. -/
noncomputable def exteriorRouteWordsEquiv (len : header.length = L.header) :
    (Σ x : HeaderExterior L header, Admitted x) ≃ Raw := by
  let payload := fun (z : Symbols groups → List Bool) => tab.recordPayload (N:=R+1) row
    (G.assignedRows guess D pp lp fun i => assignedShared g z i.val)
  let ext := fun z : Raw => JointHeader.exterior L header len (payload z.val)
  have common (z : Raw) : ∀ b, JointHeader.observed L (ext z) b = header :=
    observed_exterior L header len (payload z.val)
  let choose := fun z : Raw => (⟨ext z,common z⟩ : HeaderExterior L header)
  let embed (z : Raw) : Admitted (choose z) := by
    refine ⟨z.val,z.property,?_⟩
    change JointHeader.exterior L header len (payload z.val) = JointHeader.exterior L
      (JointHeader.observed L (ext z) fixed) _ (payload z.val)
    exact (exterior_congr L (common z fixed) (payload z.val)).symm
  refine { toFun := fun a => ⟨a.2.val,a.2.property.1⟩
           invFun := fun z => ⟨choose z,embed z⟩
           left_inv := ?_
           right_inv := fun _ => rfl }
  rintro ⟨x,z⟩
  have forced := z.property.2
  change x.val = JointHeader.exterior L (JointHeader.observed L x.val fixed) _ (payload z.val) at forced
  have same : choose ⟨z.val,z.property.1⟩ = x := Subtype.ext ((forced.trans (exterior_congr L (x.property fixed) (payload z.val))).symm)
  apply Sigma.ext same
  let raw : Raw := ⟨z.val,z.property.1⟩
  change HEq (embed raw) z
  apply (Subtype.heq_iff_coe_eq (a1:=embed raw) (a2:=z) ?_).mpr
  · rfl
  · intro word
    rw [show choose raw = x from same]

/-- The inverse constructs the entire literal shared assignment from the source
header and all scheduled data, including zero padding and both relay legs. -/
theorem exteriorRouteWordsEquiv_symm (z : Raw) :
    ((exteriorRouteWordsEquiv G L tab row D pp lp guess g decl fixed header len).symm z).1.val =
      cubeExterior G L tab row D pp lp guess g z.val header len := rfl

/-- A length-correct list of shared row words has the finite cardinality of the
specified binary positions, including empty rows. -/
@[instance_reducible] noncomputable def routeRowWordFintype : Fintype Raw := by
  let positions := (p : Symbols groups) → Fin (SharedRows.reserved blocks K h decl p) → Bool
  let e : Raw ≃ positions := {
    toFun := fun z p j => (z.val p)[j.val]'(j.isLt.trans_eq (z.property p).symm)
    invFun := fun z => ⟨fun p => List.ofFn (z p),fun _ => List.length_ofFn⟩
    left_inv := fun z => Subtype.ext (funext fun p => by
      apply List.ext_getElem (List.length_ofFn.trans (z.property p).symm)
      intro i _ _
      simp only [List.getElem_ofFn])
    right_inv := fun z => funext fun p => funext fun i => by simp only [List.getElem_ofFn] }
  exact Fintype.ofEquiv positions e.symm

/-- After the actual native programs are initialized on their own exterior, all
joint route traces at this header are indexed by the raw selector/crossing words.
The inverse is the real simultaneous native replay, including all co-owned choices. -/
noncomputable def exteriorNativeRoutesEquiv (len : header.length = L.header) {pin : Fin d → Bool} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {dst ib hb sb : Fin (R+1) → ℕ} {src : HeaderExterior L header → Fin (R+1) → ℕ → ℕ}
    {group : Fin groups → Fin (R+1)} {anchor : Fin (R+1)}
    (pub : HeaderExterior L header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8)
    (regs : HeaderExterior L header → Fin (R+1) → Bank w) (before : HeaderExterior L header → Fin (R+1) → Memory w)
    (initialized : ∀ x : HeaderExterior L header, SharedRoutePrepared G pin x.val L D pp lp owner origin stride tab row (pub x) (before x) dst ib hb sb guess)
    (copies : ∀ x : HeaderExterior L header, ReturnedHeaders G pin x.val L w) (emitted : ∀ x u, g.Emitted (src x u) (readings (before x u)))
    (fitted : ∀ x u, g.Fits w (src x u)) (records : tab.records = g.records)
    (count : tab.count = g.dataCount+g.groups.choose 2) (dataCount : (D.directory pp lp).length = g.dataCount)
    (room : g.banks+g.stride*g.groups^2 ≤ 2^w) (frame : ∀ x, SymbolFrame g (src x anchor) blocks K h decl group) :
    (Σ x : HeaderExterior L header, ∀ u, Returns route (pub x u) (mac x u) (regs x u) (before x u)) ≃ Raw :=
  (Equiv.sigmaCongrRight fun x => (initialized x).routeWordsEquiv (copies x) fixed (mac x) (regs x)
    (emitted x) (fitted x) records count dataCount room (frame x)).trans
    (exteriorRouteWordsEquiv G L tab row D pp lp guess g decl fixed header len)

end TeamContraction

end BorderVNP
end Computability
end OAI
