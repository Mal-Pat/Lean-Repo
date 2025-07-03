import Mathlib

def x : Nat := 5

#check x
#eval x
#print x

theorem name (x : Nat) (h : x = 0) : x = 0 := h

#check name
#print name

theorem equals : x = x := Eq.refl x

theorem symmetric (h : x = 4) : 4 = x := Eq.symm h

theorem transitive (h1 : x = y) (h2 : 4 = y) : x = 4 := Eq.trans h1 (Eq.symm h2)

theorem substitutes (h1 : x = y) (h2 : 4 = y) : x = 4 := Eq.subst (Eq.symm h2) h1

example (h1 : x = y) (h2 : 4 = y) : x = 4 := Eq.subst (Eq.symm h2) h1

example (h : x = 0) : x = 0 := by exact h

example (h : x = 4) : 4 = x := by rw[h]

example (h : 4 = x) : x = 4 := by rw[h]

example (a : Nat) : a + 0 = a := by
  rw[Nat.add_zero]

example : 7 = 7 := by rfl
example : 2 + 5 = 7 := by rfl


namespace Hidden

inductive Natl where
  | zero : Natl
  | succ : Natl → Natl
  deriving Repr


namespace Natl

def add (m n : Natl) : Natl :=
  match n with
  | zero => m
  | succ p => succ (add m p)

instance : Add Natl where
  add := add

theorem add_zero (m : Natl) : m + zero = m := by rfl
theorem add_succ (m n : Natl) : m + succ n = succ (m + n) := by rfl

theorem zero_add (m : Natl) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ n h => rw[add_succ, h]

theorem succ_add (m n : Natl) : succ n + m = succ (n + m) := by
  induction m with
  | zero => rw[add_zero, add_zero]
  | succ m h => rw[add_succ, h, add_succ]

theorem add_comm (m n : Natl) : m + n = n + m := by
  induction n with
  | zero => rw[add_zero, zero_add]
  | succ n h => rw[add_succ, h, succ_add]

#print add_comm

end Natl

end Hidden

example (a b : Nat) : a + 0 + b = a + b := by
  rw[Nat.add_zero]

theorem proof (a b c : Nat) : a + 0 + c + b + 0 = a + b + c := by linarith

#print proof
