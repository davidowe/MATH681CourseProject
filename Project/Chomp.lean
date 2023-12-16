import Mathlib

namespace SetTheory

namespace PGame

namespace Chomp

/-

-/

@[reducible]
def Board := Finset (ℕ × ℕ)
deriving Inhabited

@[simp]
def Move := (ℕ × ℕ)

@[simp]
def moveFilterFunc (m : Move) (x : Move) : Prop := x.1 < m.1 ∨ x.2 < m.2

instance mffDecidable (m : Move) (x : Move) : Decidable (moveFilterFunc m x) := by
  simp
  exact Or.decidable

@[simp]
def makeMove (b : Board) (m : Move) : Board := Finset.filter (moveFilterFunc m) b

theorem move_ssubset {b : Board} {m : Move} (h : m ∈ b) :
  makeMove b m ⊂ b := by
  simp
  apply Finset.filter_ssubset.2
  apply Exists.intro
  case w := m
  apply And.intro
  exact h
  simp

theorem move_smaller {b : Board} {m : Move} (h : m ∈ b) :
  Finset.card (makeMove b m) < Finset.card b := by
  simp
  refine Finset.card_lt_card ?h
  exact move_ssubset h

instance chompState : State Board where
  turnBound s := s.card
  l s := s.image (makeMove s)
  r s := s.image (makeMove s)
  left_bound m := by
    simp
    simp at m
    apply Exists.elim m
    intro a b
    apply Exists.elim b
    intro c d
    have d0 := d.1
    have d1 := d.2
    rw [←d1]
    apply move_smaller
    exact d0
  right_bound m := by
    simp
    simp at m
    apply Exists.elim m
    intro a b
    apply Exists.elim b
    intro c d
    have d0 := d.1
    have d1 := d.2
    rw [←d1]
    apply move_smaller
    exact d0

def chomp (b : Board) : PGame := PGame.ofState b

instance shortChomp (b : Board) : Short (chomp b) := by
  dsimp [chomp]
  infer_instance

-- We exclude the "poisoned" (0,0) square, as players cannot play on it

def TwoByTwo : Board := ([(0,1), (1,1),
             (1,0)]).toFinset

def ThreeByThree : Board := ([(0,2),(1,2),(2,2),
          (0,1),(1,1),(2,1),
            (1,0),(2,0)]).toFinset

def FourByFour : Board := ([(0,3),(1,3),(2,3),(3,3),
            (0,2),(1,2),(2,2),(3,2),
            (0,1),(1,1),(2,1),(3,1),
              (1,0),(2,0),(3,0)]).toFinset

#eval decide (chomp TwoByTwo ≈ 0)
--#eval decide (chomp TwoByTwo > 0)
--#eval decide (chomp TwoByTwo < 0)
--#eval decide (chomp TwoByTwo ⧏ 0)
--#eval decide (chomp ThreeByThree ≈ 0)
--#eval decide (chomp ThreeByThree ⧏ 0)
--#eval decide (chomp ([(0,1),(0,2),(1,0),(2,0)].toFinset) ≈ 0)

end Chomp
