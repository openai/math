import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentPackedCensusFromSigned
import OAI.Hierarchy.DescentPackedColumnSum

namespace OAI
/-! # Assemble the physical census once for every host and group chunk -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {r : ℕ}

abbrev Column (r cap : ℕ) := Fin r × (Fin 1 ⊕ (Fin 1 ⊕ Fin (2*cap)))
def order (r cap : ℕ) : Column r cap ≃ Fin (columns r cap) :=
  ((Equiv.refl _).prodCongr (((Equiv.refl _).sumCongr finSumFinEquiv).trans finSumFinEquiv)).trans finProdFinEquiv

def width (D cap b : ℕ) : Column r cap→ℕ
  | (_,.inl _)=>1
  | (_,.inr (.inl _))=>b
  | (_,.inr (.inr _))=>DescentSignedCableCodec.width D cap

def field (D cap b : ℕ) (hub : Cell 1) (atoms : Fin r→Cell b) (port : Fin r→Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) :
    (i : Column r cap)→Cell (width D cap b i)
  | (_,.inl _)=>hub
  | (x,.inr (.inl _))=>atoms x
  | (x,.inr (.inr j))=>port x j

def contribution (D cap b : ℕ) : (i : Column r cap)→Cell (width D cap b i)→ℕ
  | (x,.inl _),v=>v.val*2^b*2^(2*(2*cap))*(2^(1+b+2*(2*cap)))^x.val
  | (x,.inr (.inl _)),v=>v.val*2^(2*(2*cap))*(2^(1+b+2*(2*cap)))^x.val
  | (x,.inr (.inr j)),v=>(DescentSignedCableCodec.census v).val*(2^2)^j.val*(2^(1+b+2*(2*cap)))^x.val

theorem contribution_zero (D cap b : ℕ) (i : Column r cap) : contribution D cap b i 0=0 := by
  rcases i with ⟨x,_|(_|j)⟩
  · simp [contribution]
  · simp [contribution]
  · have hole : DescentSignedCableCodec.census (0:Cell (DescentSignedCableCodec.width D cap))=0 := by
      rw [←DescentSignedCableCodec.empty,DescentSignedCableCodec.census_at]
      rfl
    simp [contribution]
    exact hole

theorem contribution_sum (D cap b r : ℕ) (hub : Cell 1) (atoms : Fin r→Cell b)
    (port : Fin r→Fin (2*cap)→Cell (DescentSignedCableCodec.width D cap)) :
    (∑i : Column r cap,contribution D cap b i (field D cap b hub atoms port i))=
      (assemble D cap b r hub atoms port).val := by
  change _=(finFunctionFinEquiv (fun x=>PackedCensus.header b (2*cap) ((hub,atoms x),
    fun j=>DescentSignedCableCodec.census (port x j)))).val
  rw [finFunctionFinEquiv_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Fintype.sum_sum_type,Fintype.sum_unique,field,contribution,PackedCensus.header_value]
  change _ = ((hub.val*2^b+(atoms x).val)*2^(2*(2*cap))+
    (finFunctionFinEquiv (fun j=>DescentSignedCableCodec.census (port x j))).val)*(2^(1+b+2*(2*cap)))^x.val
  rw [finFunctionFinEquiv_apply]
  simp only [Nat.add_mul,Finset.sum_mul,Nat.add_assoc]

def expr {cap : ℕ} (hub : Expr) (count : Fin r→Expr) (cables : Fin r→Fin (2*cap)→Expr) : Column r cap→Expr
  | (_,.inl _)=>hub
  | (x,.inr (.inl _))=>count x
  | (x,.inr (.inr j))=>cables x j

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age G H M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ)
  (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S age) (groups : J≃Fin G) (hosts : V↪Fin H)
  (b base out u : ℕ) (hubField : Expr) (atoms : Fin (2^k)→Expr) (cables : Fin (2^k)→Fin (2*A.cap)→Expr)
local notation "radix" => 2^k
local notation "enum_" => order radix A.cap
local notation "oldBits" => fun i=>(width A.degree A.cap b (Equiv.symm enum_ i))
local notation "func" => fun i=>(contribution A.degree A.cap b (Equiv.symm enum_ i))
local notation "src" => fun i=>(expr hubField atoms cables (Equiv.symm enum_ i))
local notation "outBits" => (1+b+2*(2*A.cap))*radix
local notation "signed_" => Prepare.signed A native S ready groups.toEmbedding hosts
local notation "slots_" => DescentSharedCableNames.Stage.signed A native S ready

theorem issue (m : Memory w) (budget : max 1 (max b (DescentSignedCableCodec.width A.degree A.cap))≤u)
    (fitHub : hubField.Fits w base) (fitCount : ∀x,(atoms x).Fits w base) (fitWire : ∀x j,(cables x j).Fits w base)
    (flag : Source hubField (fun h (_ : Fin G)=>hub A hosts h) M m)
    (recorded : ∀x,Source (atoms x) (fun h g=>count A groups hosts b h g x) M m)
    (signedData : ∀x j,Source (cables x j) (fun h g=>DescentSignedCableCodec.encode (signed_ x j h g)) M m)
    (sep : DescentPackedColumnSum.finish base (columns radix A.cap) u M≤out)
    (room : out+H*chunks G M<2^w) :
    let cpu:=DescentPackedColumnSum.program w base out u M outBits H G oldBits func src
    let o:=DescentPackedColumnSum.after base out u M outBits H G oldBits func src m
    cpu.Exec m o (DescentPackedColumnSum.ticks base u M H G oldBits src) ∧
      (∀p : Row H G M,o (out+(row H G M p).val)=((data (A.rawCensus hosts groups slots_ b) p).val:Word w)) ∧
      (∀i,i<base ∨ out+H*chunks G M ≤ i → o i=m i) ∧ CheapCode cpu := by
  let vals (h : Fin H) (g : Fin G):=(field A.degree A.cap b (hub A hosts h) (count A groups hosts b h g)
    (fun x j=>DescentSignedCableCodec.encode (signed_ x j h g)))
  apply DescentPackedColumnSum.run base out u M outBits H G oldBits func src
    (fun i h g=>vals h g (Equiv.symm enum_ i)) (A.rawCensus hosts groups slots_ b) m
  · exact fun i=>contribution_zero A.degree A.cap b (Equiv.symm enum_ i)
  · intro h g
    rw [←raw_eq A native S ready groups hosts b h g]
    exact (Fintype.sum_equiv (Equiv.symm enum_) _ _ (fun _=>rfl)).trans (contribution_sum ..)
  · intro i
    rcases (Equiv.symm enum_) i with ⟨x,_|(_|j)⟩
    · exact (le_max_left ..).trans budget
    · exact ((le_max_left ..).trans (le_max_right ..)).trans budget
    · exact ((le_max_right ..).trans (le_max_right ..)).trans budget
  · intro i
    rcases (Equiv.symm enum_) i with ⟨x,_|(_|j)⟩
    · exact fitHub
    · exact fitCount x
    · exact fitWire x j
  · intro i
    rcases (Equiv.symm enum_) i with ⟨x,_|(_|j)⟩
    · exact flag
    · exact recorded x
    · exact signedData x j
  · exact sep
  · exact room

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
