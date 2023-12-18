import Mathlib
namespace SetTheory
namespace PGame
namespace LinearClobber

/-
CGT implementation of Linear Clobber, a one dimensional variation of the game Clobber.
Linear Clobber is a partisan game where the game starts with all the black and white stones
already placed on the board.
Players then make moves by 'clobbering' the opponent stones, where they move on of their
stones onto an adjacent opponent stone, capturing it.

Example game:
◯⬤◯⬤◯⬤
Black moves:
 ◯◯⬤◯⬤
White moves:
 ◯◯ ⬤⬤
White wins as there are no legal moves left for black.

This is an interesting game for CGT analysis as games tend to decompose into independent
subgames very quickly, giving a large adge to using CGT analysis over traditional search.
Another interesting property of Clobber is that it is an all-small game, which means
that the value of any position in Clobber is infinitesimal.
I chose Linear Clobber over normal 2d Clobber because the implementation would be very
similar, but much shorter and less tedious.

The implementation of Linear Clobber was much more difficult than chomp or domineering,
as the legal moves depend not on the empty points of the board, but rather on adjacent
stones of opposite color.
This means we need to keep track of the white and black stones, and modify the
configuration of both when moves are made.
The positions of pieces are stored as a Finset of integers, and moves are represented
by an integer pair (ℤ × ℤ), where the first integer is the direction of the move
(-1 for left, 1 for right), and the second integer is the position of the stone being moved.
I then implemented a black move by erasing the stone being moved from the black stones,
inserting a stone at the position the stone would be moved to, and removing the white
stone at the point where the black stone moved to (vice-versa for white moves).
Proving turn bounds and shortness were difficult due to these complicated rules so I
needed to implement many lemmas and theorems in order to break up the problem into
smaller chunks.
-/

-- The board representation includes black pieces, and white pieces
@[reducible]
structure Board where
  blackPieces : Finset ℤ
  whitePieces : Finset ℤ
deriving DecidableEq, Inhabited

-- A container proving that the positions of the pieces of the board do not overlap
-- Sometimes we do not need this proof so I kept the Board structure separate
structure NonOverlappingBoard where
  b : Board
  h : b.blackPieces ∩ b.whitePieces = ∅
deriving DecidableEq

instance inhab_nob : Inhabited NonOverlappingBoard := by
  apply Inhabited.mk
  exact { b := { blackPieces := [].toFinset, whitePieces := [].toFinset},
          h := rfl}

/-
A move in linear clobber is specified by (ℤ × ℤ),
where the first ℤ is the direction of the move (-1 = move left, 1 = move right)
and the second ℤ is the location of the piece being moved.
Legal moves specify the location of a piece of the moving player which moves
towards an adjacent opponent piece
Example:
On board ◯⬤◯⬤,
Move (2,1) changes the board to ◯⬤ ◯
Move (3,-1) changes the board to ◯⬤⬤
-/
@[simp]
def Move := ℤ ⨯ ℤ

-- Define transformations to shift pieces one point to the left or right
-- Used to check for adjacent opponent stones to generate legal moves
@[simp]
def shiftRight : ℤ ≃ ℤ := Equiv.addRight (1 : ℤ)

@[simp]
def shiftLeft : ℤ ≃ ℤ := Equiv.subRight (1 : ℤ)

-- Generate the legal moves as:
-- (-1,x) for all x where there is a player pieces with a left adjacent opponent piece and
--  (1,x) for all x where there is a player pieces with a right adjacent opponent piece
@[simp]
def blackMoves (b : Board) : Finset (ℤ × ℤ) :=
  (Finset.image (Prod.mk (-1)) (b.blackPieces ∩ b.whitePieces.map shiftRight)) ∪
  (Finset.image (Prod.mk 1) (b.blackPieces ∩ b.whitePieces.map shiftLeft))

@[simp]
def whiteMoves (b : Board) : Finset (ℤ × ℤ) :=
  (Finset.image (Prod.mk (-1)) (b.whitePieces ∩ b.blackPieces.map shiftRight)) ∪
  (Finset.image (Prod.mk 1) (b.whitePieces ∩ b.blackPieces.map shiftLeft))

-- Make a move by erasing the moved piece, inserting a piece where it moved, and erasing the
-- clobbered opponent piece
-- Also need to prove that the board remains non-overlapping after a move
@[simp]
def makeBlackMove (nb : NonOverlappingBoard) (m : ℤ × ℤ) : NonOverlappingBoard :=
  { b :=
    { blackPieces := insert (m.1 + m.2) (nb.b.blackPieces.erase m.2),
      whitePieces := (nb.b.whitePieces.erase (m.1 + m.2))},
    h := by
      simp
      have h' := nb.h
      rw [Finset.erase_eq, Finset.erase_eq, Finset.inter_sdiff, h']
      rfl
  }

@[simp]
def makeWhiteMove (nb : NonOverlappingBoard) (m : ℤ × ℤ) : NonOverlappingBoard :=
  { b :=
    { blackPieces := (nb.b.blackPieces.erase (m.1 + m.2)),
      whitePieces := insert (m.1 + m.2) (nb.b.whitePieces.erase m.2)},
    h := by
      simp
      have h' := nb.h
      rw [Finset.erase_eq, Finset.erase_eq, Finset.inter_sdiff, h']
      rfl
  }

-- Any legal move implies that there will be an opponent piece at the point the player is moving to
theorem left_mem_implies_capture {b : Board} {m : ℤ × ℤ} (h : m ∈ blackMoves b)
    : (m.1 + m.2) ∈ b.whitePieces := by
  simp at h
  apply Or.elim h
  intro a
  apply Exists.elim a
  intro c d
  have h1 := d.1.2
  have h2 := d.2
  have heq1 : c = m.2 := congr_arg Prod.snd h2
  have heq2 : -1 = m.1 := congr_arg Prod.fst h2
  rw [←heq1, ←heq2, add_comm]
  exact h1
  intro a
  apply Exists.elim a
  intro c d
  have h1 := d.1.2
  have h2 := d.2
  have heq1 : c = m.2 := congr_arg Prod.snd h2
  have heq2 : 1 = m.1 := congr_arg Prod.fst h2
  rw [←heq1, ←heq2, add_comm]
  exact h1

theorem right_mem_implies_capture {b : Board} {m : ℤ × ℤ} (h : m ∈ whiteMoves b)
    : (m.1 + m.2) ∈ b.blackPieces := by
  simp at h
  apply Or.elim h
  intro a
  apply Exists.elim a
  intro c d
  have h1 := d.1.2
  have h2 := d.2
  have heq1 : c = m.2 := congr_arg Prod.snd h2
  have heq2 : -1 = m.1 := congr_arg Prod.fst h2
  rw [←heq1, ←heq2, add_comm]
  exact h1
  intro a
  apply Exists.elim a
  intro c d
  have h1 := d.1.2
  have h2 := d.2
  have heq1 : c = m.2 := congr_arg Prod.snd h2
  have heq2 : 1 = m.1 := congr_arg Prod.fst h2
  rw [←heq1, ←heq2, add_comm]
  exact h1
set_option linter.unusedVariables false

-- A legal move will always either have 1 or -1 as its first component
theorem black_movement {b : Board} {m : ℤ × ℤ} (h : m ∈ blackMoves b)
    : (m.1 = 1 ∨ m.1 = -1) := by
  simp at h
  apply Or.elim h
  intro a
  apply Exists.elim a
  intro c d
  have h0 := d.2
  right
  have h1 : m = (m.1, m.2) := rfl
  rw [h1] at h0
  apply Eq.symm
  exact congr_arg Prod.fst h0
  simp
  intro c d e f
  left
  have h1 : m = (m.1, m.2) := rfl
  rw [h1] at f
  apply Eq.symm
  exact congr_arg Prod.fst f

theorem white_movement {b : Board} {m : ℤ × ℤ} (h : m ∈ whiteMoves b)
    : (m.1 = 1 ∨ m.1 = -1) := by
  simp at h
  apply Or.elim h
  intro a
  apply Exists.elim a
  intro c d
  have h0 := d.2
  right
  have h1 : m = (m.1, m.2) := rfl
  rw [h1] at h0
  apply Eq.symm
  exact congr_arg Prod.fst h0
  simp
  intro c d e f
  left
  have h1 : m = (m.1, m.2) := rfl
  rw [h1] at f
  apply Eq.symm
  exact congr_arg Prod.fst f

-- A more convenient form of what it means to be a legal move
@[simp]
theorem mem_blackMoves {b : Board} {m : ℤ × ℤ}
    : (m ∈ blackMoves b) ↔ (m.2 ∈ b.blackPieces ∧ (m.1 + m.2) ∈ b.whitePieces ∧ (m.1 = 1 ∨ m.1 = -1)) := by
  apply Iff.intro
  intro a
  apply And.intro
  simp at a
  apply Or.elim a
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  rw [←hcm]
  exact d
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  rw [←hcm]
  exact d
  simp at a
  apply Or.elim a
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  have hd : -1 = m.1 := congr_arg Prod.fst f
  rw [←hcm, ←hd, add_comm]
  apply And.intro
  exact e
  right
  rfl
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  have hd : 1 = m.1 := congr_arg Prod.fst f
  rw [←hcm, ←hd, add_comm]
  apply And.intro
  exact e
  left
  rfl
  intro a
  simp
  have ho := a.2.2
  apply Or.elim ho
  intro c
  right
  apply Exists.intro
  case mpr.left.h.w := m.2
  apply And.intro
  apply And.intro
  exact a.1
  rw [←c,add_comm]
  exact a.2.1
  rw [←c]
  intro c
  left
  apply Exists.intro
  case mpr.right.h.w := m.2
  apply And.intro
  apply And.intro
  exact a.1
  rw [←c,add_comm]
  exact a.2.1
  rw [←c]

@[simp]
theorem mem_whiteMoves {b : Board} {m : ℤ × ℤ}
    : (m ∈ whiteMoves b) ↔ (m.2 ∈ b.whitePieces ∧ (m.1 + m.2) ∈ b.blackPieces ∧ (m.1 = 1 ∨ m.1 = -1)) := by
  apply Iff.intro
  intro a
  apply And.intro
  simp at a
  apply Or.elim a
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  rw [←hcm]
  exact d
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  rw [←hcm]
  exact d
  simp at a
  apply Or.elim a
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  have hd : -1 = m.1 := congr_arg Prod.fst f
  rw [←hcm, ←hd, add_comm]
  apply And.intro
  exact e
  right
  rfl
  simp
  intro c d e f
  have hm : m = (m.1, m.2) := by
    rfl
  rw [hm] at f
  have hcm : c = m.2 := congr_arg Prod.snd f
  have hd : 1 = m.1 := congr_arg Prod.fst f
  rw [←hcm, ←hd, add_comm]
  apply And.intro
  exact e
  left
  rfl
  intro a
  simp
  have ho := a.2.2
  apply Or.elim ho
  intro c
  right
  apply Exists.intro
  case mpr.left.h.w := m.2
  apply And.intro
  apply And.intro
  exact a.1
  rw [←c,add_comm]
  exact a.2.1
  rw [←c]
  intro c
  left
  apply Exists.intro
  case mpr.right.h.w := m.2
  apply And.intro
  apply And.intro
  exact a.1
  rw [←c,add_comm]
  exact a.2.1
  rw [←c]

-- Helper theorem that if an element is not in a Finset, then it is also not in the Finset after an erase
theorem not_mem_imp_not_mem_erase {S : Finset ℤ} {x : ℤ} {x' : ℤ} (h : x ∉ S)
    : x ∉ (S.erase x') := by
  simp
  intro a
  exact h

-- A player move will leave the same number of player pieces on the resulting board
theorem moveBlack_blackEq {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ blackMoves nb.b)
    : (makeBlackMove nb m).b.blackPieces.card = nb.b.blackPieces.card := by
  simp
  rw [mem_blackMoves] at h
  have p : m.1+m.2 ∉ Finset.erase nb.b.blackPieces m.2 := by
    have dj := Finset.disjoint_iff_inter_eq_empty.mpr nb.h
    have djl := Finset.disjoint_right.mp dj
    have ir := h.2.1
    have nil := djl ir
    apply not_mem_imp_not_mem_erase
    exact nil
  rw [Finset.card_insert_of_not_mem p, Finset.card_erase_of_mem h.1, Nat.sub_add_cancel]
  apply Finset.card_pos.mpr
  apply Exists.intro
  case w := m.2
  exact h.1

theorem moveWhite_whiteEq {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ whiteMoves nb.b)
    : (makeWhiteMove nb m).b.whitePieces.card = nb.b.whitePieces.card := by
  simp
  rw [mem_whiteMoves] at h
  have p : m.1+m.2 ∉ Finset.erase nb.b.whitePieces m.2 := by
    have dj := Finset.disjoint_iff_inter_eq_empty.mpr nb.h
    have djl := Finset.disjoint_left.mp dj
    have ir := h.2.1
    have nil := djl ir
    apply not_mem_imp_not_mem_erase
    exact nil
  rw [Finset.card_insert_of_not_mem p, Finset.card_erase_of_mem h.1, Nat.sub_add_cancel]
  apply Finset.card_pos.mpr
  apply Exists.intro
  case w := m.2
  exact h.1

-- A player move will shrink the number of opponent pieces
theorem moveBlack_whiteSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ blackMoves nb.b)
    : (makeBlackMove nb m).b.whitePieces.card < nb.b.whitePieces.card := by
  simp
  have h0 := h
  rw [mem_blackMoves] at h0
  rw [Finset.card_erase_of_mem h0.2.1]
  apply Nat.sub_lt
  refine Finset.card_pos.mpr ?_
  rw [Finset.Nonempty]
  apply Exists.intro
  case a.w := m.1 + m.2
  exact left_mem_implies_capture h
  exact Nat.one_pos


theorem moveWhite_blackSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ whiteMoves nb.b)
    : (makeWhiteMove nb m).b.blackPieces.card < nb.b.blackPieces.card := by
  simp
  have h0 := h
  rw [mem_whiteMoves] at h0
  rw [Finset.card_erase_of_mem h0.2.1]
  apply Nat.sub_lt
  refine Finset.card_pos.mpr ?_
  rw [Finset.Nonempty]
  apply Exists.intro
  case a.w := m.1 + m.2
  exact right_mem_implies_capture h
  exact Nat.one_pos

-- A player move will decrease the overall number of pieces on the board
theorem moveBlack_sumSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ blackMoves nb.b)
    : ((makeBlackMove nb m).b.blackPieces.card + (makeBlackMove nb m).b.whitePieces.card) <
      (nb.b.blackPieces.card + nb.b.whitePieces.card) := by
  have ll := moveBlack_blackEq h
  rw [ll]
  apply Nat.add_lt_add_left
  exact moveBlack_whiteSmaller h

theorem moveWhite_sumSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ whiteMoves nb.b)
    : ((makeWhiteMove nb m).b.blackPieces.card + (makeWhiteMove nb m).b.whitePieces.card) <
      (nb.b.blackPieces.card + nb.b.whitePieces.card) := by
  have rr := moveWhite_whiteEq h
  rw [rr]
  apply Nat.add_lt_add_right
  exact moveWhite_blackSmaller h

-- Create a linear clobber state from a non-overlapping board
instance linClobberState : State NonOverlappingBoard where
  turnBound nb := nb.b.blackPieces.card + nb.b.whitePieces.card -- An upperbound on the number of turns is the number of pieces
  l nb := Finset.image (makeBlackMove nb) (blackMoves nb.b)
  r nb := Finset.image (makeWhiteMove nb) (whiteMoves nb.b)
  left_bound m := by -- Prove that a left (black) move decreases the turnbound
    aesop -- Not sure if this is bad practice, but it transforms the context into a nice state and saves a lot of effort
    have p : -1 + w_1 ∉ Finset.erase s.b.blackPieces w_1 := by
      have dj := Finset.disjoint_iff_inter_eq_empty.mpr s.h
      have djl := Finset.disjoint_right.mp dj
      have nil := djl right_1
      apply not_mem_imp_not_mem_erase
      rw [add_comm]
      exact nil
    rw [Finset.card_insert_of_not_mem p, Finset.card_erase_of_mem left_1, Nat.sub_add_cancel]
    simp
    rw [add_comm] at right_1
    rw [Finset.card_erase_of_mem right_1]
    apply Nat.sub_lt
    refine Finset.card_pos.mpr ?_
    rw [Finset.Nonempty]
    apply Exists.intro
    exact right_1
    exact zero_lt_one
    apply Finset.card_pos.mpr
    rw [Finset.Nonempty]
    apply Exists.intro
    exact left_1

    have p : 1 + w_1 ∉ Finset.erase s.b.blackPieces w_1 := by
      have dj := Finset.disjoint_iff_inter_eq_empty.mpr s.h
      have djl := Finset.disjoint_right.mp dj
      have nil := djl right_1
      apply not_mem_imp_not_mem_erase
      rw [add_comm]
      exact nil
    rw [Finset.card_insert_of_not_mem p, Finset.card_erase_of_mem left_1, Nat.sub_add_cancel]
    simp
    rw [add_comm] at right_1
    rw [Finset.card_erase_of_mem right_1]
    apply Nat.sub_lt
    refine Finset.card_pos.mpr ?_
    rw [Finset.Nonempty]
    apply Exists.intro
    exact right_1
    exact zero_lt_one
    apply Finset.card_pos.mpr
    rw [Finset.Nonempty]
    apply Exists.intro
    exact left_1

  right_bound m := by -- Prove that a right (white) move decreases the turn bound
    aesop
    have p : -1 + w_1 ∉ Finset.erase s.b.whitePieces w_1 := by
      have dj := Finset.disjoint_iff_inter_eq_empty.mpr s.h
      have djl := Finset.disjoint_left.mp dj
      have nil := djl right_1
      apply not_mem_imp_not_mem_erase
      rw [add_comm]
      exact nil
    rw [Finset.card_insert_of_not_mem p, Finset.card_erase_of_mem left_1, Nat.sub_add_cancel]
    simp
    rw [add_comm] at right_1
    rw [Finset.card_erase_of_mem right_1]
    apply Nat.sub_lt
    refine Finset.card_pos.mpr ?_
    rw [Finset.Nonempty]
    apply Exists.intro
    exact right_1
    exact zero_lt_one
    apply Finset.card_pos.mpr
    rw [Finset.Nonempty]
    apply Exists.intro
    exact left_1

    have p : 1 + w_1 ∉ Finset.erase s.b.whitePieces w_1 := by
      have dj := Finset.disjoint_iff_inter_eq_empty.mpr s.h
      have djl := Finset.disjoint_left.mp dj
      have nil := djl right_1
      apply not_mem_imp_not_mem_erase
      rw [add_comm]
      exact nil
    rw [Finset.card_insert_of_not_mem p, Finset.card_erase_of_mem left_1, Nat.sub_add_cancel]
    simp
    rw [add_comm] at right_1
    rw [Finset.card_erase_of_mem right_1]
    apply Nat.sub_lt
    refine Finset.card_pos.mpr ?_
    rw [Finset.Nonempty]
    apply Exists.intro
    exact right_1
    exact zero_lt_one
    apply Finset.card_pos.mpr
    rw [Finset.Nonempty]
    apply Exists.intro
    exact left_1

def linClobber (nb : NonOverlappingBoard) : PGame := PGame.ofState nb

instance shortlinClobber (nb : NonOverlappingBoard) : Short (linClobber nb) := by
  dsimp [linClobber]
  infer_instance

-- Helper function to construct a board
def getLinClobberBoard (b : Finset ℤ) (w : Finset ℤ) : NonOverlappingBoard :=
  { b := {
      blackPieces := b \ w,
      whitePieces := w
    },
    h := by
      simp
  }

-- Some example positions:

-- ◯◯⬤⬤
def ex1 := getLinClobberBoard {0,1} {2,3}
#eval linClobber ex1 ≈ 0
-- Any game in the form (◯)^n(⬤)^m where n, m > 0 is a second player win
-- Shown in "An Introduction to Clobber" by Wolfe et al.

-- ◯◯◯◯◯◯⬤
def ex2 := getLinClobberBoard {0,1,2,3,4,5} {6}
#eval linClobber ex2 > 0
#eval 0 ⧏ linClobber ex2
#eval linClobber ex2 ⧏ 0
-- Precise value of this position is 5.↑*
-- This is an example of a positive infinitesimal value
-- Smaller than any real number, but greater than zero
-- "An Introduction to Clobber" shows that (◯)^n⬤ ≈ ↑.(n-1) + *.n

-- ◯⬤◯⬤
def ex3 := getLinClobberBoard {0,2} {1,3}
#eval linClobber ex3 ⧏ 0
#eval 0 ⧏ linClobber ex3


-- ◯⬤◯⬤◯⬤
def ex4 := getLinClobberBoard {0,2,4} {1,3,5}
#eval linClobber ex4 ≈ 0

-- ◯⬤◯⬤◯⬤◯⬤
def ex5 := getLinClobberBoard {0,2,4,6} {1,3,5,7}
#eval linClobber ex5 ⧏ 0
#eval 0 ⧏ linClobber ex5

-- ◯⬤◯⬤◯⬤◯⬤◯⬤
def ex6 := getLinClobberBoard {0,2,4,6,8} {1,3,5,7,9}
#eval linClobber ex6 ⧏ 0
#eval 0 ⧏ linClobber ex6

-- Currently working on a paper with my research group showing that (◯⬤)^n ‖ 0 for n ≠ 3
-- Suprisingly difficult problem, the proof is many pages long

-- ◯⬤ and ◯⬤◯⬤
#eval linClobber (getLinClobberBoard {0} {1}) ≈ linClobber ex3
-- Even though these two positions are both fuzzy with zero,
-- they are not equivalent.
-- ◯⬤ ≈ *
-- ◯⬤◯⬤ = {◯◯⬤ | ◯⬤⬤} = {↑ | ↓}
-- ◯⬤◯⬤ is an example of a 'hot' game where left can play to a positive position,
-- and right can play to a negative position
-- Hot games are fuzzy with the range of values between its most positive left option
-- and most negative right option, and cannot be reduced to a number

end LinearClobber
