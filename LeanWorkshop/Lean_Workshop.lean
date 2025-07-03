import Mathlib




example (x : Nat) (h : x = 7) : x = 7 := h

example (x : Nat) : x = x := Eq.refl x

example (x : Nat) : 8 * (x ^ 2) - 5 = 8 * (x ^ 2) - 5 := Eq.refl _

example (x : Nat) (h : 7 = x) : x = 7 := Eq.symm h

example (x y : Nat) (h1 : x = 3) (h2 : y = x) : y = 3 := Eq.trans h2 h1

example (x y : Nat) (h1 : x = 3) (h2 : y = x) : y = 3 := Eq.subst h1 h2

--Starting to get cumbersome
example (x y : Nat) (h1 : x = 3) (h2 : x = y) : y = 3 := Eq.trans (Eq.symm h2) h1





theorem p_imp_p (x : Nat) (h : x = 0) : x = 0 := by
  exact h

#print p_imp_p

theorem same0r_2 (x : Nat) (h : x = 0) : 0 = x := by
  have h2 := Eq.comm.mp h
  exact h2

theorem same0r_1 (x : Nat) (h : x = 0) : 0 = x := by
  rw[h]

theorem same0l_1 (x : Nat) (h : 0 = x) : x = 0 := by
  rw[h]

#print same0l_1

#print same0r_1

theorem same0r_1' (x : Nat) (h : x = 0) : 0 = x :=
  (fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2) x h

theorem same0r_1'' (x : Nat) : x = 0 → 0 = x :=
  (fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2) x

theorem same0r_1''' : (x : Nat) → x = 0 → 0 = x :=
  fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2

theorem same0r_1'''' : ∀ x : Nat, x = 0 → 0 = x :=
  fun x h ↦
    let_fun h2 := Eq.comm.mp h;
    h2

#check same0r_1'

theorem one_plus_one_eq_two : 1 + 1 = 2 := by
  rfl

theorem some_calc : 3*(104 - 4)/10 = 30 := by
  rfl

#print some_calc

theorem add_zero' (a : Nat) : a + 0 = a := by
  apply Nat.add_zero



def s : String := "Hello"

#print s






-- Using rfl

theorem eq_refl_1 (x : Nat) : x = x := by
  rfl

theorem eq_refl_2 (x : Nat) : 8 * (x ^ 2) - 5 = 8 * (x ^ 2) - 5 := by
  rfl




-- Using exact

theorem exact_1 (x : Nat) (h : x = 7) : x = 7 := by
  exact h

theorem exact_1' (x : Nat) (h : x = 7) : x = 7 := by
  assumption




-- Using rw

theorem rewrite_1 (x y : Nat) (h : y = x - 2) : 3 * y = 3 * (x - 2) := by
  rw[h]

theorem rewrite_1' (x y : Nat) (h : y = x - 2) : 3 * y = 3 * (x - 2) := by
  rw[← h]

theorem rewrite_2 (x y z : Nat) (h1 : x = 3 * y) (h2 : y = z + 3) : x = 3 * (z + 3) := by
  rw[h1]
  rw[h2]

theorem rewrite_2' (x y z : Nat) (h1 : x = 3 * y) (h2 : y = z + 3) : x = 3 * (z + 3) := by
  rw[h2] at h1
  exact h1

theorem rewrite_2'' (x y z : Nat) (h1 : x = 3 * y) (h2 : y = z + 3) : x = 3 * (z + 3) := by
  rw[← h2]
  exact h1

#print rewrite_2''


-- Defining Nat on our own

namespace Hidden

inductive Natl where
 | zero : Natl
 | succ : Natl → Natl
 deriving Repr

namespace Natl



-- Defining addition on our own

def add (m n : Natl) : Natl :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

instance : Add Natl where
  add := add



-- Proving basic addition lemmas from addition definition

theorem add_zero (m : Natl) : m + zero = m := rfl
theorem add_succ (m n : Natl) : m + succ n = succ (m + n) := rfl

#check Eq.rec

-- Proving addition theorems using induction

theorem zero_add (m : Natl) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ n h => rw[add_succ, h]

theorem succ_add (m n : Natl) : (succ m) + n = succ (m + n) := by
  induction n with
  | zero => rw[add_zero, add_zero]
  | succ n h => rw[add_succ, add_succ, h]

theorem add_comm (m n : Natl) : m + n = n + m := by
  induction n with
  | zero => rw[add_zero, zero_add]
  | succ n h => rw[add_succ, succ_add, h]

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




example (a b : Nat) : a + (b + 0) = a + b + a - a := by simp

section

variable (p q r : Prop)

example (h : p) (k : p → q) : q := by
  exact k h
