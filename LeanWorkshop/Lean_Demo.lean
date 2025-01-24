import Mathlib

def s : ℝ := 2

#check s
#eval s

theorem equals (x : Nat) (h : x = 7) : x = 7 := h

#check equals
#print equals

theorem equals_itself (x : Nat) : x = x := Eq.refl x

theorem equals2 (x : Nat) : 3*x + 7 = 3*x + 7 := Eq.refl _ 

theorem symm' (x : Nat) (h : x = 7) : 7 = x := Eq.symm h

theorem transitive (x y : Nat) (h1 : x = 3) (h2 : x = y) : y = 3 :=
    Eq.trans (Eq.symm h2) h1

-- comment

theorem equals1 (x : Nat) : x = x := by rfl

theorem symm'' (x : Nat) (h : x = 7) : 7 = x := by
  have h1 : 7 = x := Eq.symm h
  exact h1

theorem symm''' (x : Nat) (h : x = 7) : 7 = x := by
  rw[h]

theorem symm'''' (x : Nat) (h : x = 7) : 7 = x := by
  rw[← h]

theorem simple : 1 + 1 = 2 := by rfl

theorem rewrite_1 (x y : Nat) (h : y = x - 2) : 3 * y = 3 * (x - 2) := by
  rw[h]

theorem rewrite_2' (x y z : Nat) (h1 : x = 3 * y) (h2 : y = z + 3) : x = 3 * (z + 3) := by
  rw[h2] at h1
  exact h1



namespace Hidden

inductive Natl where
  | zero : Natl
  | succ : Natl → Natl
  deriving Repr

namespace Natl

def add (m n : Natl) : Natl :=
  match n with
  | zero => m
  | succ n => succ (add m n)

instance : Add Natl where
  add := add

theorem add_zero (m : Natl) : m + zero = m := by rfl
theorem add_succ (m n : Natl) : m + succ n = succ (m + n) := by rfl

theorem zero_add (m : Natl) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ n h => rw[add_succ, h]

theorem succ_add (m n : Natl) : (succ m) + n = succ (m + n) := by
  sorry

theorem add_comm (m n : Natl) : m + n = n + m := by
  induction n with
  | zero => rw[add_zero, zero_add]
  | succ n h => rw[add_succ, succ_add, h]

#print add_comm

theorem add_assoc (p q r : Natl) : p + q + r = p + (q + r) := by
  induction r with
  | zero => rw[add_zero, add_zero]
  | succ r h => rw[add_succ, add_succ, add_succ, h]

end Natl

end Hidden

#check Nat.add_zero
#check Nat.zero_add
#check Nat.add_comm
#check Nat.add_assoc
#check Nat.add_right_cancel
