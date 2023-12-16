import Mathlib

namespace SetTheory

namespace PGame

namespace LinearClobber

@[reducible]
structure Board where
  leftPieces : Finset ℤ
  rightPieces : Finset ℤ
deriving DecidableEq, Inhabited


structure NonOverlappingBoard where
  b : Board
  h : b.leftPieces ∩ b.rightPieces = ∅
deriving DecidableEq

instance inhab_nob : Inhabited NonOverlappingBoard := by
  apply Inhabited.mk
  exact { b := { leftPieces := [].toFinset, rightPieces := [].toFinset},
          h := rfl}

--instance deceq_nob : DecidableEq NonOverlappingBoard := by
--  exact Classical.decEq NonOverlappingBoard

-- A move in linear clobber is specified by (ℤ × ℤ),
-- where the first ℤ is the direction of the move (-1 = move left, 1 = move right)
-- and the second ℤ is the location of the piece being moved,
-- Legal moves specify the location of a piece of a moving player which moves towards an adjacent opponent piece
@[simp]
def Move := ℤ ⨯ ℤ

@[simp]
def shiftRight : ℤ ≃ ℤ := Equiv.addRight (1 : ℤ)

@[simp]
def shiftLeft : ℤ ≃ ℤ := Equiv.subRight (1 : ℤ)

@[simp]
def leftMoves (b : Board) : Finset (ℤ × ℤ) :=
  (Finset.image (Prod.mk (-1)) (b.leftPieces ∩ b.rightPieces.map shiftRight)) ∪ (Finset.image (Prod.mk 1) (b.leftPieces ∩ b.rightPieces.map shiftLeft))

@[simp]
def rightMoves (b : Board) : Finset (ℤ × ℤ) :=
  (Finset.image (Prod.mk (-1)) (b.rightPieces ∩ b.leftPieces.map shiftRight)) ∪ (Finset.image (Prod.mk 1) (b.rightPieces ∩ b.leftPieces.map shiftLeft))

-- BBWWBW.WB
def exb : Board := { leftPieces := [0,1,4,8].toFinset, rightPieces := [2,3,5,7].toFinset}

#eval leftMoves exb
#eval rightMoves exb


@[simp]
def makeLeftMove (nb : NonOverlappingBoard) (m : ℤ × ℤ) : NonOverlappingBoard :=
  { b :=
    { leftPieces := insert (m.1 + m.2) (nb.b.leftPieces.erase m.2),
      rightPieces := (nb.b.rightPieces.erase (m.1 + m.2))},
    h := by
      simp
      have h' := nb.h
      rw [Finset.erase_eq, Finset.erase_eq, Finset.inter_sdiff, h']
      rfl
  }

@[simp]
def makeRightMove (nb : NonOverlappingBoard) (m : ℤ × ℤ) : NonOverlappingBoard :=
  { b :=
    { leftPieces := (nb.b.leftPieces.erase (m.1 + m.2)),
      rightPieces := insert (m.1 + m.2) (nb.b.rightPieces.erase m.2)},
    h := by
      simp
      have h' := nb.h
      rw [Finset.erase_eq, Finset.erase_eq, Finset.inter_sdiff, h']
      rfl
  }

theorem left_mem_implies_capture {b : Board} {m : ℤ × ℤ} (h : m ∈ leftMoves b)
    : (m.1 + m.2) ∈ b.rightPieces := by
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

theorem right_mem_implies_capture {b : Board} {m : ℤ × ℤ} (h : m ∈ rightMoves b)
    : (m.1 + m.2) ∈ b.leftPieces := by
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

theorem left_movement {b : Board} {m : ℤ × ℤ} (h : m ∈ leftMoves b)
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

theorem right_movement {b : Board} {m : ℤ × ℤ} (h : m ∈ rightMoves b)
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


@[simp]
theorem mem_leftMoves {b : Board} {m : ℤ × ℤ}
    : (m ∈ leftMoves b) ↔ (m.2 ∈ b.leftPieces ∧ (m.1 + m.2) ∈ b.rightPieces ∧ (m.1 = 1 ∨ m.1 = -1)) := by
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
theorem mem_rightMoves {b : Board} {m : ℤ × ℤ}
    : (m ∈ rightMoves b) ↔ (m.2 ∈ b.rightPieces ∧ (m.1 + m.2) ∈ b.leftPieces ∧ (m.1 = 1 ∨ m.1 = -1)) := by
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

-- Not sure how to prove this for arbitrary types although I'm sure it is possible
-- Something is going wrong with Finset.erase, I think the type needs to be proven decidable, not sure how to do that
-- Doesn't seem to be as simple as adding [Decidable X]
theorem not_mem_imp_not_mem_erase {S : Finset ℤ} {x : ℤ} {x' : ℤ} (h : x ∉ S)
    : x ∉ (S.erase x') := by
  simp
  intro a
  exact h


theorem moveLeft_leftEq {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ leftMoves nb.b)
    : (makeLeftMove nb m).b.leftPieces.card = nb.b.leftPieces.card := by
  simp
  rw [mem_leftMoves] at h
  have p : m.1+m.2 ∉ Finset.erase nb.b.leftPieces m.2 := by
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

theorem moveRight_rightEq {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ rightMoves nb.b)
    : (makeRightMove nb m).b.rightPieces.card = nb.b.rightPieces.card := by
  simp
  rw [mem_rightMoves] at h
  have p : m.1+m.2 ∉ Finset.erase nb.b.rightPieces m.2 := by
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


theorem moveLeft_rightSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ leftMoves nb.b)
    : (makeLeftMove nb m).b.rightPieces.card < nb.b.rightPieces.card := by
  simp
  have h0 := h
  rw [mem_leftMoves] at h0
  rw [Finset.card_erase_of_mem h0.2.1]
  apply Nat.sub_lt
  refine Finset.card_pos.mpr ?_
  rw [Finset.Nonempty]
  apply Exists.intro
  case a.w := m.1 + m.2
  exact left_mem_implies_capture h
  exact Nat.one_pos


theorem moveRight_leftSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ rightMoves nb.b)
    : (makeRightMove nb m).b.leftPieces.card < nb.b.leftPieces.card := by
  simp
  have h0 := h
  rw [mem_rightMoves] at h0
  rw [Finset.card_erase_of_mem h0.2.1]
  apply Nat.sub_lt
  refine Finset.card_pos.mpr ?_
  rw [Finset.Nonempty]
  apply Exists.intro
  case a.w := m.1 + m.2
  exact right_mem_implies_capture h
  exact Nat.one_pos


theorem moveLeft_sumSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ leftMoves nb.b)
    : ((makeLeftMove nb m).b.leftPieces.card + (makeLeftMove nb m).b.rightPieces.card) <
      (nb.b.leftPieces.card + nb.b.rightPieces.card) := by
  have ll := moveLeft_leftEq h
  rw [ll]
  apply Nat.add_lt_add_left
  exact moveLeft_rightSmaller h

theorem moveRight_sumSmaller {nb : NonOverlappingBoard} {m : ℤ × ℤ} (h : m ∈ rightMoves nb.b)
    : ((makeRightMove nb m).b.leftPieces.card + (makeRightMove nb m).b.rightPieces.card) <
      (nb.b.leftPieces.card + nb.b.rightPieces.card) := by
  have rr := moveRight_rightEq h
  rw [rr]
  apply Nat.add_lt_add_right
  exact moveRight_leftSmaller h


instance linClobberState : State NonOverlappingBoard where
  turnBound nb := nb.b.leftPieces.card + nb.b.rightPieces.card
  l nb := Finset.image (makeLeftMove nb) (leftMoves nb.b)
  r nb := Finset.image (makeRightMove nb) (rightMoves nb.b)
  left_bound m := by
    aesop
    have p : -1 + w_1 ∉ Finset.erase s.b.leftPieces w_1 := by
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

    have p : 1 + w_1 ∉ Finset.erase s.b.leftPieces w_1 := by
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

  right_bound m := by
    aesop
    have p : -1 + w_1 ∉ Finset.erase s.b.rightPieces w_1 := by
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

    have p : 1 + w_1 ∉ Finset.erase s.b.rightPieces w_1 := by
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


def getLinClobberBoard (l : List ℤ) (r : List ℤ) : NonOverlappingBoard :=
  { b := {
      leftPieces := l.toFinset \ r.toFinset,
      rightPieces := r.toFinset
    },
    h := by
      simp
  }

def ex1 := getLinClobberBoard [0,2,4] [1,3,5,6]

def b1 : NonOverlappingBoard := { b := {
                                    leftPieces := [0].toFinset,
                                    rightPieces := [1].toFinset
                                  },
                                  h := rfl
                                }

#check ex1

#eval decide (linClobber ex1 ≈ 0)

--def wb_to_op (w : WithBot ℤ) : Option ℤ := w

--def LinearClobberToString (lp : List ℤ) (h : lp.length > 0) : IO Unit := do
--  for x in List.range (max ((wb_to_op lp.maximum).get h) rp.maximum) do
--    IO.println s!"x: {x}"
--  return 0

--def LinearClobberToString (b : Board) : String :=
--  have lp := b.leftPieces
--  have rp := b.rightPieces
--  let mut s := 0
--  for x in lp do
--    s := s ++ x
--  s

--#eval LinearClobberToString ex1.b

end LinearClobber
