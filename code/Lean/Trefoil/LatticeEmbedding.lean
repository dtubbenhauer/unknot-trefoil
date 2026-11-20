import Trefoil.LatticeSupports
import Mathlib.Data.Fintype.Sum

/-!
# Literal integral embedding data for Section 3A

This model records the Gram data of the plumbing roots and the three heavy
vertices in a diagonal integral lattice. It does not assume a coordinate
normal form, a support frame, or the obstruction conclusion.
-/

namespace Trefoil.LatticeEmbedding

open scoped BigOperators

abbrev Ambient (m : ℕ) := Fin (m + 8)
abbrev Vector (m : ℕ) := Ambient m → ℤ

/-- Long chain, two-root chain, and the two isolated square-two roots. -/
abbrev RootIndex (m : ℕ) := Fin (m - 1) ⊕ (Fin 2 ⊕ Fin 2)

/-- The four root blocks and the remaining singleton coordinate. -/
abbrev Blocks (m : ℕ) :=
  Fin m ⊕ (Fin 3 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Unit)))

def leftEndpoint {m : ℕ} : RootIndex m → Blocks m
  | .inl i => .inl ⟨i.val, by have := i.isLt; omega⟩
  | .inr (.inl i) => .inr (.inl i.castSucc)
  | .inr (.inr i) =>
      if i.val = 0 then .inr (.inr (.inl 0))
      else .inr (.inr (.inr (.inl 0)))

def rightEndpoint {m : ℕ} : RootIndex m → Blocks m
  | .inl i => .inl ⟨i.val + 1, by have := i.isLt; omega⟩
  | .inr (.inl i) => .inr (.inl i.succ)
  | .inr (.inr i) =>
      if i.val = 0 then .inr (.inr (.inl 1))
      else .inr (.inr (.inr (.inl 1)))

def rootGram {m : ℕ} (r s : RootIndex m) : ℤ :=
  if r = s then 2 else
  match r, s with
  | .inl i, .inl j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0
  | .inr (.inl _), .inr (.inl _) => -1
  | _, _ => 0

def aRootPairing {m : ℕ} : RootIndex m → ℤ
  | .inl i => if i.val + 2 = m then -1 else 0
  | _ => 0

def bRootPairing {m : ℕ} : RootIndex m → ℤ
  | .inr (.inl i) => if i.val = 0 then -1 else 0
  | _ => 0

def cRootPairing {m : ℕ} : RootIndex m → ℤ
  | .inr (.inl i) => if i.val = 1 then -1 else 0
  | _ => 0

/-- The actual lattice data needed by the obstruction. The independence
condition is a restriction of the joint basis's independence modulo two. -/
structure Embedding (m : ℕ) where
  root : RootIndex m → Vector m
  A : Vector m
  B : Vector m
  C : Vector m
  root_pairing : ∀ r s, LatticeSupports.dot (root r) (root s) = rootGram r s
  normA : ∑ j, A j ^ 2 = 4
  normB : ∑ j, B j ^ 2 = 6
  normC : ∑ j, C j ^ 2 = 3
  pairingAB : LatticeSupports.dot A B = -1
  pairingAC : LatticeSupports.dot A C = 0
  pairingBC : LatticeSupports.dot B C = 0
  pairingA_root : ∀ r, LatticeSupports.dot A (root r) = aRootPairing r
  pairingB_root : ∀ r, LatticeSupports.dot B (root r) = bRootPairing r
  pairingC_root : ∀ r, LatticeSupports.dot C (root r) = cRootPairing r
  independent : LinearIndependent (ZMod 2)
    (fun r : Option (RootIndex m) =>
      match r with
      | none => fun j => (B j : ZMod 2)
      | some i => fun j => (root i j : ZMod 2))

theorem root_norm {m : ℕ} (E : Embedding m) (r : RootIndex m) :
    ∑ j, E.root r j ^ 2 = 2 := by
  simpa [LatticeSupports.dot, rootGram, pow_two] using E.root_pairing r r

theorem root_mod_two_injective {m : ℕ} (E : Embedding m) :
    Function.Injective (fun r : RootIndex m => fun j => (E.root r j : ZMod 2)) := by
  intro r s h
  have hi := E.independent.injective
  have hs : (some r : Option (RootIndex m)) = some s := hi h
  exact Option.some.inj hs

theorem root_support_ne {m : ℕ} (E : Embedding m) {r s : RootIndex m}
    (hrs : r ≠ s) : LatticeSupports.support (E.root r) ≠ LatticeSupports.support (E.root s) := by
  apply LatticeSupports.support_ne_of_modTwo_ne
  · exact fun j => LatticeBasics.norm_two_coordinate (E.root r) (root_norm E r) j
  · exact fun j => LatticeBasics.norm_two_coordinate (E.root s) (root_norm E s) j
  · exact fun h => hrs (root_mod_two_injective E h)

theorem root_supports_disjoint {m : ℕ} (E : Embedding m) {r s : RootIndex m}
    (hrs : r ≠ s) (hgram : rootGram r s = 0) :
    Disjoint (LatticeSupports.support (E.root r)) (LatticeSupports.support (E.root s)) := by
  apply (LatticeSupports.dot_zero_iff_disjoint (E.root r) (E.root s)
    (LatticeBasics.norm_two_support_card (E.root r) (root_norm E r))
    (LatticeBasics.norm_two_support_card (E.root s) (root_norm E s))
    (root_support_ne E hrs)).mp
  rw [E.root_pairing, hgram]

end Trefoil.LatticeEmbedding
