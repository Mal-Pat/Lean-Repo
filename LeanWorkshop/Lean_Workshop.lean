import Mathlib




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




-- Defining Nat on our own

namespace Hidden

inductive Nat where
 | zero : Nat
 | succ : Nat → Nat
 deriving Repr

namespace Nat



-- Defining addition on our own

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

instance : Add Nat where
  add := add



-- Proving basic addition lemmas from addition definition

theorem add_zero (m : Nat) : m + zero = m := rfl
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl



-- Proving addition theorems using induction

theorem zero_add (m : Nat) : zero + m = m := by
  induction m with
  | zero => rfl
  | succ n h => rw[add_succ, h]

theorem succ_add (m n : Nat) : (succ m) + n = succ (m + n) := by
  induction n with
  | zero => rw[add_zero, add_zero]
  | succ n h => rw[add_succ, add_succ, h]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero => rw[add_zero, zero_add]
  | succ n h => rw[add_succ, succ_add, h]

theorem add_assoc (p q r : Nat) : p + q + r = p + (q + r) := by
  induction r with
  | zero => rw[add_zero, add_zero]
  | succ r h => rw[add_succ, add_succ, add_succ, h]

end Nat

end Hidden





-- Using in-built theorems in Mathlib

theorem adding_zero_1 (a b : Nat) : a + (b + 0) = a + b := by
  rw[Nat.add_zero]

theorem adding_zero_2 (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw[Nat.add_zero]
  rw[Nat.add_zero]

theorem adding_zero_2' (a b c : Nat) : a + (b + 0) + (c + 0) = a + b + c := by
  rw[Nat.add_zero, Nat.add_zero]

theorem adding_zero_3 (a b c : Nat) : a + (b + 0) + (c + 0) = a + (b + 0) + c := by
  rw[Nat.add_zero, Nat.add_zero]

theorem adding_zero_3' (a b c : Nat) : a + (b + 0) + (c + 0) = a + (b + 0) + c := by
  repeat rw[Nat.add_zero]



-- Using nth_rw

theorem adding_zero_3'' (a b c : Nat) : a + (b + 0) + (c + 0) = a + (b + 0) + c := by
  nth_rw 2 [Nat.add_zero]




-- Using apply

theorem apply_1 (x y : Nat) (h1 : x = 8) (h2 : x = 8 → y = 3) : y = 3 := by
  apply h2
  exact h1

-- Using have

theorem have_1 (x y : Nat) (h1 : x = 8) (h2 : x = 8 → y = 3) : y = 3 := by
  have h3 : y = 3 := h2 h1
  exact h3

-- Using intro

theorem intro_1 (x y : Nat) : x + 1 = y + 1 → x = y := by
  intro h
  exact Nat.add_right_cancel h











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
