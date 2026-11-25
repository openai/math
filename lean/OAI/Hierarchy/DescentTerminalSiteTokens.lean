import OAI.Hierarchy.DescentRecipeTokenCorrespondence
import OAI.Hierarchy.DescentRecipeGroupStage
import OAI.Hierarchy.DescentResetExteriorTokens

namespace OAI
/-! # The terminal local recipe has only polynomially many actual nodes, including external equalities -/

namespace Hierarchy.DescentKernelHistory.BitDescription
open DescentSixParty Computability.BorderVNP.Crossing DescentCompiler
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable (O : BitDescription A) (old : A.graph.Site→List H)

def Tokenized.partition (rec : O.Tokenized old) (v : A.graph.Site) :
    (O.recipe v).Node ≃ Fin (old v).length ⊕ Attached A.graph v :=
  Fintype.equivOfCardEq (by simpa [A.exterior_token_card] using rec v)

variable {h C Ht L : ℕ} {q ε : ℝ} {Y : Type} (Z : ResetInput A q ε h C Ht) (T : Z.Terminals)

theorem Tokenized.reset (rec : O.Tokenized old) (key : A.graph.Edge↪Fin L)
    (scalar : Y→List (List Bool)→F) (prog : SiteBits (U:=Y) Z.bank)
    (valid : ReadsBits Z.bank scalar prog (Z.orderedBank key)) :
    (O.fromBank Z T key scalar prog valid).Tokenized (Z.recipeRecords T old prog) := by
  intro v
  have eqn := Fintype.card_congr (Z.recipe_partition T old O key scalar prog valid (Tokenized.partition O old rec) v)
  simpa only [Fintype.card_sum,Fintype.card_fin,MarkedWorld.exterior_token_card] using eqn

variable {k : ℕ} {G : PoweredGadget F} {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A₀ : GroupStage A G q ε J V k) (S : AtomSchedule)
private abbrev siteTag (v : A.graph.Site) : Bool := A₀.hub (A₀.pos v).2

theorem local_nodes {i p : ℕ} (rec : O.Tokenized A₀.records) (hJ : 0<S.height) (hh : 0<A₀.hist)
    (age : i≤S.length) (grain : A₀.z=S.grainAt G.b p i) (hist : A₀.hist=S.firstWidth G.b p)
    (wire : A₀.wire=S.epochPower^S.priceExponent) (capacity : A₀.cap≤2^(8+S.capGain*i))
    (allPins : ∀pin,siteTag A₀ (A.graph.attach pin)=true) (widths : ∀pin,bits pin=A₀.hist)
    (hubs : A.HubExterior (siteTag A₀)) (v : A.graph.Site) :
    Fintype.card (O.recipe v).Node≤S.epochPower^S.localTokenExponent := by
  rw [rec v]
  cases known : siteTag A₀ v with
  | false=>
    rw [A.exterior_eq_zero (siteTag A₀) allPins v known,Nat.add_zero]
    exact A₀.token_room S v hJ hh age grain hist wire capacity
  | true=>
    rw [A₀.noHubAtoms v known,List.length_nil,Nat.zero_add]
    have b : 0<G.b := by have :=G.paid;omega
    have stack : A₀.z*G.b≤A₀.hist := by rw [grain,hist];exact S.grain_le_first G.b p i b
    have bound := A.hub_token_room A₀ hubs A₀.hist widths hh stack v known
    have few : A.exteriorTokens v≤A₀.cap := (Nat.le_mul_of_pos_left _ (by decide : 0<256)).trans bound
    exact (few.trans (S.local_capacity hJ age capacity)).trans (Nat.pow_le_pow_right (Nat.two_pow_pos _)
      (Nat.le_add_left _ _))

omit [Fintype P] in
/-- Bind the local token certificate to any preserved total operand/private-plus-incidence
charge, using the actual number of nodes and the common width budget at this occurrence. -/
theorem local_payload {v : A.graph.Site} {p N exp scale : ℕ} (tokens : Fintype.card (O.recipe v).Node≤N)
    (nodeCap : ∀x,(O.recipe v).nodeBits x≤p*scale) (room : scale*N≤S.epochPower^exp) :
    (∑x,(O.recipe v).nodeBits x)≤p*S.epochPower^exp := by
  calc
    _ ≤ ∑_x : (O.recipe v).Node,p*scale := Finset.sum_le_sum fun x _=>nodeCap x
    _ = p*(scale*Fintype.card (O.recipe v).Node) := by simp; ring
    _ ≤ _ := Nat.mul_le_mul_left p ((Nat.mul_le_mul_left scale tokens).trans room)

end
end Hierarchy.DescentKernelHistory.BitDescription

end OAI
